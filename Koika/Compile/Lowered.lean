/-
  Koika/Compile/Lowered.lean - Port of coq/LoweredSyntax.v
  Lowered/type-erased AST where everything is bitvector sizes
-/

import Koika.Types
import Koika.Primitives
import Koika.TypedSyntax

namespace Koika

/-! ## Membership in Lowered Signature -/

/-- Membership in a lowered signature -/
inductive LMember : Nat → LSig → Type where
  | here : LMember sz (sz :: sig)
  | there : LMember sz sig → LMember sz (sz' :: sig)
  deriving Repr

/-! ## Lowered Action -/

/-- Lowered action - the AST after type erasure.
    Everything is in terms of bitvector sizes (Nat). -/
inductive LAction (reg_t ext_fn_t : Type)
    (R : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig)
    : LSig → Nat → Type where
  | fail : (sz : Nat) → LAction reg_t ext_fn_t R CSigma sig sz
  | var : (k : String) → LMember sz sig → LAction reg_t ext_fn_t R CSigma sig sz
  | const : BitVec sz → LAction reg_t ext_fn_t R CSigma sig sz
  | assign : (k : String) → LMember sz sig → LAction reg_t ext_fn_t R CSigma sig sz →
             LAction reg_t ext_fn_t R CSigma sig 0
  | seq : LAction reg_t ext_fn_t R CSigma sig 0 →
          LAction reg_t ext_fn_t R CSigma sig sz →
          LAction reg_t ext_fn_t R CSigma sig sz
  | bind : (k : String) → LAction reg_t ext_fn_t R CSigma sig sz →
           LAction reg_t ext_fn_t R CSigma (sz :: sig) sz' →
           LAction reg_t ext_fn_t R CSigma sig sz'
  | «if» : LAction reg_t ext_fn_t R CSigma sig 1 →
           LAction reg_t ext_fn_t R CSigma sig sz →
           LAction reg_t ext_fn_t R CSigma sig sz →
           LAction reg_t ext_fn_t R CSigma sig sz
  | read : Port → (reg : reg_t) → LAction reg_t ext_fn_t R CSigma sig (R reg)
  | write : Port → (reg : reg_t) →
            LAction reg_t ext_fn_t R CSigma sig (R reg) →
            LAction reg_t ext_fn_t R CSigma sig 0
  | unop : (fn : Typed.FBits1) →
           LAction reg_t ext_fn_t R CSigma sig (Circuit.sig1 fn).1 →
           LAction reg_t ext_fn_t R CSigma sig (Circuit.sig1 fn).2
  | binop : (fn : Typed.FBits2) →
            LAction reg_t ext_fn_t R CSigma sig (Circuit.sig2 fn).1 →
            LAction reg_t ext_fn_t R CSigma sig (Circuit.sig2 fn).2.1 →
            LAction reg_t ext_fn_t R CSigma sig (Circuit.sig2 fn).2.2
  | extCall : (fn : ext_fn_t) →
              LAction reg_t ext_fn_t R CSigma sig (CSigma fn).argSize →
              LAction reg_t ext_fn_t R CSigma sig (CSigma fn).retSize

/-- A lowered rule is a closed lowered action returning 0 bits -/
abbrev LRule (reg_t ext_fn_t : Type) (R : reg_t → Nat) (CSigma : ext_fn_t → CExternalSig) :=
  LAction reg_t ext_fn_t R CSigma [] 0

/-! ## Lowering Helpers -/

/-- Lower a type context signature to sizes -/
def lowerSig (sig : List (String × Ty)) : LSig :=
  sig.map fun (_, ty) => ty.size

/-- Lower a typed member witness to a lowered member -/
def lowerMember : Member (k, tau) sig → LMember tau.size (lowerSig sig)
  | .here => .here
  | .there m => .there (lowerMember m)

end Koika
