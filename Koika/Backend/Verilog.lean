/-
  Koika/Backend/Verilog.lean - Verilog code generation
  Generates synthesizable Verilog from Koika circuits
-/

import Koika.Types
import Koika.Primitives
import Koika.Compile.Circuit
import Koika.Compile.Lowered

namespace Koika.Backend.Verilog

/-! ## Verilog Generation Monad -/

/-- State for Verilog generation -/
structure VerilogState where
  gensym : Nat := 0
  wires : List (String × Nat)  -- (name, width)
  assigns : List String
  deriving Repr

/-- Verilog generation monad -/
abbrev VerilogM := StateM VerilogState

/-- Generate a fresh wire name -/
def freshWire (width : Nat) : VerilogM String := do
  let st ← get
  let name := s!"_w{st.gensym}"
  set { st with gensym := st.gensym + 1, wires := (name, width) :: st.wires }
  return name

/-- Add an assignment -/
def addAssign (assign : String) : VerilogM Unit := do
  modify fun st => { st with assigns := assign :: st.assigns }

/-! ## Verilog Formatting Helpers -/

/-- Format a bitvector constant -/
def formatBits (bv : BitVec n) : String :=
  if n == 0 then "1'b0"
  else if n == 1 then s!"{n}'b{if bv.toNat == 0 then "0" else "1"}"
  else s!"{n}'h{String.ofList (bv.toNat.toDigits 16)}"

/-- Format a wire/port declaration -/
def formatWireDecl (name : String) (width : Nat) (keyword : String := "wire") : String :=
  if width <= 1 then
    s!"\t{keyword} {name};"
  else
    s!"\t{keyword} [{width - 1}:0] {name};"

/-- Format a register declaration with initial value -/
def formatRegDecl (name : String) (width : Nat) (init : BitVec width) : String :=
  if width <= 1 then
    s!"\treg {name} = {formatBits init};"
  else
    s!"\treg [{width - 1}:0] {name} = {formatBits init};"

/-- Format an input port -/
def formatInputPort (name : String) (width : Nat) : String :=
  if width == 1 then s!"input {name}"
  else s!"input [{width - 1}:0] {name}"

/-- Format an output port -/
def formatOutputPort (name : String) (width : Nat) : String :=
  if width == 1 then s!"output {name}"
  else s!"output [{width - 1}:0] {name}"

/-! ## Unary Operation Verilog Generation -/

/-- Generate Verilog for a unary operation -/
def genUnop (fn : Typed.FBits1) (arg : String) : String :=
  match fn with
  | .not _ => s!"~{arg}"
  | .sext sz width =>
      if sz < width then
        -- Sign extend: {{(N){arg[MSB]}}, arg}
        "{" ++ "{" ++ s!"({width - sz})" ++ "{" ++ s!"{arg}[{sz-1}]" ++ "}" ++ "}" ++ s!", {arg}" ++ "}"
      else arg
  | .zextL sz width =>
      if sz < width then
        -- Zero extend left: {{N'b0}, arg}
        "{" ++ "{" ++ s!"{width - sz}'b0" ++ "}" ++ s!", {arg}" ++ "}"
      else arg
  | .zextR sz width =>
      if sz < width then
        -- Zero extend right: {arg, {N'b0}}
        "{" ++ s!"{arg}, " ++ "{" ++ s!"{width - sz}'b0" ++ "}" ++ "}"
      else arg
  | .repeat _ times =>
      -- Repeat: {N{arg}}
      "{" ++ s!"{times}" ++ "{" ++ arg ++ "}" ++ "}"
  | .slice _ offset width => s!"{arg}[{offset} +: {width}]"
  | .lowered (.ignoreBits _) => "0"  -- Ignored value
  | .lowered (.displayBits _) => "0"  -- Display is a no-op in Verilog

/-! ## Binary Operation Verilog Generation -/

/-- Generate Verilog for a binary operation -/
def genBinop (fn : Typed.FBits2) (arg1 arg2 : String) : String :=
  match fn with
  | .and _ => s!"{arg1} & {arg2}"
  | .or _ => s!"{arg1} | {arg2}"
  | .xor _ => s!"{arg1} ^ {arg2}"
  | .lsl _ _ => s!"{arg1} << {arg2}"
  | .lsr _ _ => s!"{arg1} >> {arg2}"
  | .asr _ _ => s!"$signed({arg1}) >>> {arg2}"
  | .concat _ _ =>
      -- Concatenation: {arg1, arg2}
      "{" ++ s!"{arg1}, {arg2}" ++ "}"
  | .sel _ => s!"{arg1}[{arg2}]"
  | .sliceSubst sz offset width =>
      -- Replace bits [offset +: width] in arg1 with arg2
      let hi := offset + width
      if offset == 0 then
        "{" ++ s!"{arg1}[{sz-1}:{hi}], {arg2}" ++ "}"
      else if hi >= sz then
        "{" ++ s!"{arg2}, {arg1}[{offset-1}:0]" ++ "}"
      else
        "{" ++ s!"{arg1}[{sz-1}:{hi}], {arg2}, {arg1}[{offset-1}:0]" ++ "}"
  | .indexedSlice _ width => s!"{arg1}[{arg2} +: {width}]"
  | .plus _ => s!"{arg1} + {arg2}"
  | .minus _ => s!"{arg1} - {arg2}"
  | .mul _ _ => s!"{arg1} * {arg2}"
  | .eqBits _ neg => if neg then s!"{arg1} != {arg2}" else s!"{arg1} == {arg2}"
  | .compare signed cmp _ =>
      let cast := if signed then fun s => s!"$signed({s})" else id
      let op := match cmp with
        | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="
      s!"{cast arg1} {op} {cast arg2}"

/-! ## Circuit to Verilog -/

section CircuitGen

variable {reg_t ext_fn_t : Type} [ToString reg_t] [ToString ext_fn_t]
variable (CR : reg_t → Nat)
variable (CSigma : ext_fn_t → CExternalSig)

/-- Environment mapping circuit tags to wire names -/
abbrev CircuitEnv := List (Nat × String)

/-- Generate Verilog expression for a circuit, returning wire name -/
partial def genCircuit
    (env : CircuitEnv)
    (c : Circuit reg_t ext_fn_t CR CSigma sz)
    : VerilogM String := do
  match c with
  | .const bv =>
      return formatBits bv
  | .readReg r =>
      return toString r
  | .mux sel t f =>
      let selW ← genCircuit env sel
      let tW ← genCircuit env t
      let fW ← genCircuit env f
      let w ← freshWire sz
      addAssign s!"\tassign {w} = {selW} ? {tW} : {fW};"
      return w
  | .unop fn arg =>
      let argW ← genCircuit env arg
      let w ← freshWire sz
      addAssign s!"\tassign {w} = {genUnop fn argW};"
      return w
  | .binop fn arg1 arg2 =>
      let arg1W ← genCircuit env arg1
      let arg2W ← genCircuit env arg2
      let w ← freshWire sz
      addAssign s!"\tassign {w} = {genBinop fn arg1W arg2W};"
      return w
  | .external fn arg =>
      let argW ← genCircuit env arg
      let w ← freshWire sz
      -- External modules are instantiated separately
      addAssign s!"\t// External call to {toString fn}: {argW} -> {w}"
      return w
  | .annot name inner =>
      let innerW ← genCircuit env inner
      let w ← freshWire sz
      addAssign s!"\tassign {w} = {innerW}; // {name}"
      return w

end CircuitGen

/-! ## Register Info -/

/-- Information about a register for code generation -/
structure RegInfo where
  name : String
  width : Nat
  initValue : String
  writeEnable : String
  writeData : String
  deriving Repr

/-! ## Main Verilog Module Generation -/

/-- Generate a complete Verilog module -/
def generateModule
    (moduleName : String)
    (registers : List RegInfo)
    (extraPorts : List (String × Nat × Bool))  -- (name, width, isOutput)
    (bodyGen : VerilogM Unit)
    : String := Id.run do
  -- Run generation to collect wires and assignments
  let initState : VerilogState := { gensym := 0, wires := [], assigns := [] }
  let (_, st) := bodyGen.run initState

  -- Build module
  let mut lines : List String := []

  -- Header
  lines := lines ++ ["// -*- mode: verilog -*-", s!"module {moduleName}("]

  -- Ports: clock, reset
  let mut portLines : List String := ["\tinput CLK", "\tinput RST_N"]

  -- Register ports (for debugging)
  for reg in registers do
    portLines := portLines ++ [s!"\toutput [{reg.width - 1}:0] {reg.name}__data"]

  -- Extra ports
  for (name, width, isOutput) in extraPorts do
    if isOutput then
      portLines := portLines ++ [formatOutputPort name width]
    else
      portLines := portLines ++ [formatInputPort name width]

  lines := lines ++ [String.intercalate ",\n" portLines, ");", ""]

  -- Register declarations
  for reg in registers do
    lines := lines ++ [formatRegDecl reg.name reg.width (BitVec.ofNat reg.width 0)]

  lines := lines ++ [""]

  -- Wire declarations
  for (name, width) in st.wires.reverse do
    lines := lines ++ [formatWireDecl name width]

  lines := lines ++ [""]

  -- Continuous assignments
  for assign in st.assigns.reverse do
    lines := lines ++ [assign]

  lines := lines ++ [""]

  -- Register update logic
  lines := lines ++ ["\talways @(posedge CLK) begin"]
  lines := lines ++ ["\t\tif (!RST_N) begin"]
  for reg in registers do
    lines := lines ++ [s!"\t\t\t{reg.name} <= {reg.initValue};"]
  lines := lines ++ ["\t\tend else begin"]
  for reg in registers do
    lines := lines ++ [s!"\t\t\tif ({reg.writeEnable}) {reg.name} <= {reg.writeData};"]
  lines := lines ++ ["\t\tend"]
  lines := lines ++ ["\tend", ""]

  -- Output assignments
  for reg in registers do
    lines := lines ++ [s!"\tassign {reg.name}__data = {reg.name};"]

  lines := lines ++ ["", "endmodule"]

  String.intercalate "\n" lines

/-! ## Simplified Circuit Generation for SchedulerCircuit -/

/-- Generate Verilog for a scheduler circuit -/
def generateSchedulerVerilog
    {reg_t ext_fn_t rule_name_t : Type}
    [ToString reg_t] [ToString ext_fn_t]
    [BEq reg_t] [Hashable reg_t]
    (moduleName : String)
    (regs : List reg_t)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig)
    (initValues : (r : reg_t) → BitVec (CR r))
    (circuit : SchedulerCircuit reg_t ext_fn_t rule_name_t CR CSigma)
    : String := Id.run do
  -- Build register info
  let mut regInfos : List RegInfo := []
  let mut writeEnables : List (reg_t × String) := []
  let mut writeDatas : List (reg_t × String) := []

  -- For now, create placeholder write enable/data
  -- In a full implementation, we'd generate circuits for each register
  for r in regs do
    let name := toString r
    let width := CR r
    let initVal := formatBits (initValues r)
    regInfos := regInfos ++ [{
      name := name
      width := width
      initValue := initVal
      writeEnable := s!"{name}_write_en"
      writeData := s!"{name}_write_data"
    }]

  -- Generate the module with circuit body
  let bodyGen : VerilogM Unit := do
    for r in regs do
      let name := toString r
      let writeEnCircuit := circuit.writeEnable r
      let writeDataCircuit := circuit.writeData r
      let weWire ← genCircuit CR CSigma [] writeEnCircuit
      let wdWire ← genCircuit CR CSigma [] writeDataCircuit
      addAssign s!"\tassign {name}_write_en = {weWire};"
      addAssign s!"\tassign {name}_write_data = {wdWire};"

  generateModule moduleName regInfos [] bodyGen

end Koika.Backend.Verilog
