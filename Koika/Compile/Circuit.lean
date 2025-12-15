/-
  Koika/Compile/Circuit.lean - Port of coq/CircuitSyntax.v
  Circuit/RTL syntax for hardware representation
-/

import Koika.Types
import Koika.Primitives
import Koika.Compile.Lowered

namespace Koika

/-! ## Read/Write Data Fields -/

/-- Fields in read/write data structure -/
inductive RWDataField where
  | r0     -- read on port 0
  | r1     -- read on port 1
  | w0     -- write on port 0
  | w1     -- write on port 1
  | data0  -- data for port 0
  | data1  -- data for port 1
  deriving DecidableEq, Repr, BEq

/-- Fields in the circuit structure -/
inductive CircuitField (reg_t : Type) where
  | rwdata (r : reg_t) (field : RWDataField)
  | canfire
  deriving Repr

/-! ## Circuit Syntax -/

/-- Circuit (RTL) representation.
    Circuits are combinational logic with references to registers. -/
inductive Circuit (reg_t ext_fn_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig)
    : Nat → Type where
  | mux : Circuit reg_t ext_fn_t CR CSigma 1 →
          Circuit reg_t ext_fn_t CR CSigma sz →
          Circuit reg_t ext_fn_t CR CSigma sz →
          Circuit reg_t ext_fn_t CR CSigma sz
  | const : BitVec sz → Circuit reg_t ext_fn_t CR CSigma sz
  | readReg : (reg : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR reg)
  | unop : (fn : Typed.FBits1) →
           Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig1 fn).1 →
           Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig1 fn).2
  | binop : (fn : Typed.FBits2) →
            Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig2 fn).1 →
            Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig2 fn).2.1 →
            Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig2 fn).2.2
  | external : (fn : ext_fn_t) →
               Circuit reg_t ext_fn_t CR CSigma (CSigma fn).argSize →
               Circuit reg_t ext_fn_t CR CSigma (CSigma fn).retSize
  | annot : String → Circuit reg_t ext_fn_t CR CSigma sz →
            Circuit reg_t ext_fn_t CR CSigma sz

/-! ## Circuit Smart Constructors -/

namespace Circuit

variable {reg_t ext_fn_t : Type}
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

/-- AND gate -/
def and (a b : Circuit reg_t ext_fn_t CR CSigma sz) : Circuit reg_t ext_fn_t CR CSigma sz :=
  sorry  -- Would use .binop (.and sz) a b but need type matching

/-- OR gate -/
def or (a b : Circuit reg_t ext_fn_t CR CSigma sz) : Circuit reg_t ext_fn_t CR CSigma sz :=
  sorry  -- Would use .binop (.or sz) a b

/-- NOT gate -/
def not (a : Circuit reg_t ext_fn_t CR CSigma sz) : Circuit reg_t ext_fn_t CR CSigma sz :=
  sorry  -- Would use .unop (.not sz) a

/-- Constant zero -/
def zero : Circuit reg_t ext_fn_t CR CSigma sz :=
  .const 0

/-- Constant one (for 1-bit circuits) -/
def one : Circuit reg_t ext_fn_t CR CSigma 1 :=
  .const 1

end Circuit

/-! ## Read/Write Data Structures -/

/-- Read/write data for a single register -/
structure RWData (reg_t ext_fn_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig)
    (sz : Nat) where
  read0 : Circuit reg_t ext_fn_t CR CSigma 1
  read1 : Circuit reg_t ext_fn_t CR CSigma 1
  write0 : Circuit reg_t ext_fn_t CR CSigma 1
  write1 : Circuit reg_t ext_fn_t CR CSigma 1
  data0 : Circuit reg_t ext_fn_t CR CSigma sz
  data1 : Circuit reg_t ext_fn_t CR CSigma sz

/-- Create initial RWData for a register -/
def RWData.init {reg_t ext_fn_t : Type}
    {CR : reg_t → Nat}
    {CSigma : ext_fn_t → CExternalSig}
    (sz : Nat) : RWData reg_t ext_fn_t CR CSigma sz :=
  { read0 := .const 0
    read1 := .const 0
    write0 := .const 0
    write1 := .const 0
    data0 := .const 0
    data1 := .const 0 }

/-! ## Action Circuit Result -/

/-- Result of compiling an action to a circuit -/
structure ActionCircuit (reg_t ext_fn_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig)
    (sz : Nat) where
  canfire : Circuit reg_t ext_fn_t CR CSigma 1
  value : Circuit reg_t ext_fn_t CR CSigma sz
  rwdata : (r : reg_t) → RWData reg_t ext_fn_t CR CSigma (CR r)

/-! ## Rule/Scheduler Circuit -/

/-- Result of compiling a scheduler to circuits -/
structure SchedulerCircuit (reg_t ext_fn_t rule_name_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig) where
  /-- Final write enable for each register -/
  writeEnable : reg_t → Circuit reg_t ext_fn_t CR CSigma 1
  /-- Final write data for each register -/
  writeData : (r : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR r)

end Koika
