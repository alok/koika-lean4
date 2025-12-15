/-
  Examples/GCDMachine.lean - Port of examples/gcd_machine.v
  A simple GCD computation machine demonstrating the Koika DSL
-/

import Koika

namespace Examples.GCDMachine

open Koika

/-! ## Register Definitions -/

/-- Registers for the GCD machine -/
inductive Reg where
  | inputData   -- Input pair (a, b)
  | inputValid  -- Input is valid
  | gcdBusy     -- GCD computation in progress
  | gcdA        -- Current value of a
  | gcdB        -- Current value of b
  | outputData  -- Output result
  deriving DecidableEq, Repr, Inhabited, BEq

instance : ToString Reg where
  toString
    | .inputData => "input_data"
    | .inputValid => "input_valid"
    | .gcdBusy => "gcd_busy"
    | .gcdA => "gcd_a"
    | .gcdB => "gcd_b"
    | .outputData => "output_data"

/-! ## Type Assignments -/

/-- Pair struct for input -/
def pairStruct : Ty :=
  .struct "pair" [("a", .bits 16), ("b", .bits 16)]

/-- Type of each register -/
def regType : Reg → Ty
  | .inputData => pairStruct
  | .inputValid => .bits 1
  | .gcdBusy => .bits 1
  | .gcdA => .bits 16
  | .gcdB => .bits 16
  | .outputData => .bits 16

/-- Initial value of each register -/
def regInit (r : Reg) : (regType r).denote :=
  match r with
  | .inputData => ((0 : BitVec 16), ((0 : BitVec 16), ()))
  | .inputValid => (0 : BitVec 1)
  | .gcdBusy => (0 : BitVec 1)
  | .gcdA => (0 : BitVec 16)
  | .gcdB => (0 : BitVec 16)
  | .outputData => (0 : BitVec 16)

/-! ## External Functions -/

/-- No external functions needed -/
inductive ExtFn where
  -- empty

def extSig : ExtFn → ExternalSig
  | e => nomatch e

/-! ## Rules as Untyped Actions -/

/-- Abbreviation for our action type -/
abbrev Act := SimpleUAction Reg ExtFn

/-- Rule 1: Start GCD computation when input is valid and not busy -/
def gcdStartRule : Act :=
  -- if read0(input_valid) == Ob~1 && !read0(gcd_busy) then
  --   let data := read0(input_data) in
  --   write0(gcd_a, get(data, a));
  --   write0(gcd_b, get(data, b));
  --   write0(gcd_busy, Ob~1);
  --   write0(input_valid, Ob~0)
  -- else fail
  let cond : Act := UAction.binop (.eq false)
        (UAction.read .p0 Reg.inputValid)
        (UAction.const (.bits 1) (1 : BitVec 1))
  let notBusy : Act := UAction.unop (.bits1 .not) (UAction.read .p0 Reg.gcdBusy)
  let body : Act := UAction.bind "data" (UAction.read .p0 Reg.inputData)
    (UAction.seq
      (UAction.write .p0 Reg.gcdA
        (UAction.unop (.struct1 (.getFieldBits "pair" [("a", .bits 16), ("b", .bits 16)] "a"))
          (UAction.var "data")))
      (UAction.seq
        (UAction.write .p0 Reg.gcdB
          (UAction.unop (.struct1 (.getFieldBits "pair" [("a", .bits 16), ("b", .bits 16)] "b"))
            (UAction.var "data")))
        (UAction.seq
          (UAction.write .p0 Reg.gcdBusy (UAction.const (.bits 1) (1 : BitVec 1)))
          (UAction.write .p0 Reg.inputValid (UAction.const (.bits 1) (0 : BitVec 1))))))
  UAction.if cond (UAction.if notBusy body (UAction.fail unitTy)) (UAction.fail unitTy)

/-- Rule 2: Compute GCD step - if a != 0, swap or subtract -/
def gcdComputeRule : Act :=
  -- let a := read0(gcd_a) in
  -- let b := read0(gcd_b) in
  -- if a != |16`d0| then
  --   if a < b then
  --     write0(gcd_b, a);
  --     write0(gcd_a, b)
  --   else
  --     write0(gcd_a, a - b)
  -- else fail
  let readA : Act := UAction.read .p0 Reg.gcdA
  let readB : Act := UAction.read .p0 Reg.gcdB
  let varA : Act := UAction.var "a"
  let varB : Act := UAction.var "b"
  let aIsZero : Act := UAction.binop (.eq true) varA (UAction.const (.bits 16) (0 : BitVec 16))
  let aLtB : Act := UAction.binop (.bits2 (.compare false .lt)) varA varB
  let swapAB : Act := UAction.seq
    (UAction.write .p0 Reg.gcdB varA)
    (UAction.write .p0 Reg.gcdA varB)
  let subAB : Act := UAction.write .p0 Reg.gcdA
    (UAction.binop (.bits2 .minus) varA varB)
  UAction.bind "a" readA
    (UAction.bind "b" readB
      (UAction.if aIsZero
        (UAction.fail unitTy)  -- a == 0, fail
        (UAction.if aLtB swapAB subAB)))

/-- Rule 3: Output result when a == 0 -/
def gcdGetResultRule : Act :=
  -- if (read1(gcd_a) == |16`d0|) && read0(gcd_busy) then
  --   write0(gcd_busy, Ob~0);
  --   write0(output_data, read1(gcd_b))
  -- else fail
  let aIsZero : Act := UAction.binop (.eq false)
    (UAction.read .p1 Reg.gcdA)
    (UAction.const (.bits 16) (0 : BitVec 16))
  let isBusy : Act := UAction.binop (.eq false)
    (UAction.read .p0 Reg.gcdBusy)
    (UAction.const (.bits 1) (1 : BitVec 1))
  let outputBody : Act := UAction.seq
    (UAction.write .p0 Reg.gcdBusy (UAction.const (.bits 1) (0 : BitVec 1)))
    (UAction.write .p0 Reg.outputData (UAction.read .p1 Reg.gcdB))
  UAction.if aIsZero
    (UAction.if isBusy outputBody (UAction.fail unitTy))
    (UAction.fail unitTy)

/-! ## Rule Names and Scheduler -/

/-- Rule names -/
inductive RuleName where
  | start
  | stepCompute
  | getResult
  deriving DecidableEq, Repr

/-- Rule lookup -/
def rules : RuleName → Act
  | .start => gcdStartRule
  | .stepCompute => gcdComputeRule
  | .getResult => gcdGetResultRule

/-- Scheduler: start |> step_compute |> get_result |> done -/
def scheduler : Scheduler Unit RuleName :=
  .cons .start (.cons .stepCompute (.cons .getResult .done))

/-! ## Package Definition -/

/-- GCD Machine package -/
structure GCDPackage where
  moduleName : String := "gcd_machine"
  regTypes : Reg → Ty := regType
  regInit : (r : Reg) → (regType r).denote := regInit
  extSig : ExtFn → ExternalSig := extSig
  rules : RuleName → Act := rules
  scheduler : Scheduler Unit RuleName := scheduler

def package : GCDPackage := {}

/-! ## Example Usage -/

#check package.moduleName   -- "gcd_machine"
#check package.regTypes     -- Reg → Ty
#check package.scheduler    -- The scheduler

end Examples.GCDMachine
