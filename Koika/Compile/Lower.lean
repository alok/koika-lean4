/-
  Koika/Compile/Lower.lean - Port of coq/Lowering.v
  Compilation from typed ASTs to lowered ASTs
-/

import Koika.Types
import Koika.Primitives
import Koika.TypedSyntax
import Koika.Compile.Lowered

namespace Koika

/-! ## Value/Bits Conversion -/

/-- Convert a typed value to bits -/
def bitsOfValue {tau : Ty} : tau.denote → BitVec tau.size :=
  match tau with
  | .bits sz => fun v => v
  | .enum sig => fun v => v  -- Already BitVec
  | .struct _ fields => fun v => sorry  -- Would pack struct fields
  | .array elemTy len => fun v => sorry  -- Would pack array elements

/-- Convert bits to a typed value -/
def valueOfBits {tau : Ty} : BitVec tau.size → tau.denote :=
  match tau with
  | .bits sz => fun v => v
  | .enum sig => fun v => v  -- Already BitVec
  | .struct _ fields => fun v => sorry  -- Would unpack struct fields
  | .array elemTy len => fun v => sorry  -- Would unpack array elements

/-! ## Lower External Signature -/

/-- Lower an external signature to circuit level -/
def lowerExternalSig (sig : ExternalSig) : CExternalSig :=
  { argSize := sig.argType.size
    retSize := sig.retType.size }

/-! ## Lower Primitives -/

/-- Lower a typed unary operation to a circuit-level operation -/
def lowerFn1 (fn : Typed.Fn1) : Typed.FBits1 :=
  match fn with
  | .display fn => .lowered (.displayBits fn)
  | .conv tau .pack => .lowered (.ignoreBits 0)  -- No-op at circuit level
  | .conv tau .unpack => .lowered (.ignoreBits 0)  -- No-op at circuit level
  | .conv tau .ignore => .lowered (.ignoreBits tau.size)
  | .bits1 fn => fn
  | .struct1 .getField name fields idx =>
      -- Extract field from packed struct
      let offset := fields.take idx |>.foldl (fun acc (_, ty) => acc + ty.size) 0
      let width := match fields[idx]? with
        | some (_, ty) => ty.size
        | none => 0
      .slice (fields.foldl (fun acc (_, ty) => acc + ty.size) 0) offset width
  | .array1 .getElement elemTy len idx =>
      -- Extract element from packed array
      .slice (len * elemTy.size) (idx * elemTy.size) elemTy.size

/-- Lower a typed binary operation to circuit-level operations -/
def lowerFn2 (fn : Typed.Fn2) : Typed.FBits2 :=
  match fn with
  | .eq tau negate => .eqBits tau.size negate
  | .bits2 fn => fn
  | .struct2 .substField name fields idx =>
      -- Substitute field in packed struct
      let offset := fields.take idx |>.foldl (fun acc (_, ty) => acc + ty.size) 0
      let width := match fields[idx]? with
        | some (_, ty) => ty.size
        | none => 0
      .sliceSubst (fields.foldl (fun acc (_, ty) => acc + ty.size) 0) offset width
  | .array2 .substElement elemTy len idx =>
      -- Substitute element in packed array
      .sliceSubst (len * elemTy.size) (idx * elemTy.size) elemTy.size

/-! ## Main Lowering Pass -/

section Lower

variable {reg_t ext_fn_t : Type}
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Lowered register type function -/
def lowerR (r : reg_t) : Nat := (R r).size

/-- Lowered external signature function -/
def lowerSigma (f : ext_fn_t) : CExternalSig := lowerExternalSig (Sigma f)

/-- Lower a typed action to a lowered action -/
def lowerAction : Action reg_t ext_fn_t R Sigma sig tau →
                  LAction reg_t ext_fn_t (lowerR R) (lowerSigma Sigma) (lowerSig sig) tau.size
  | .fail tau => .fail tau.size
  | .var m => .var m.varName (lowerMember m)
  | .const v => .const (bitsOfValue v)
  | .assign m e => .assign m.varName (lowerMember m) (lowerAction e)
  | .seq a b => .seq (lowerAction a) (lowerAction b)
  | .bind v e body => .bind v (lowerAction e) (lowerAction body)
  | .if c t f => .if (lowerAction c) (lowerAction t) (lowerAction f)
  | .read p r => .read p r
  | .write p r v => .write p r (lowerAction v)
  | .unop fn a =>
      -- This is simplified - would need proper type coercion
      sorry
  | .binop fn a1 a2 =>
      -- This is simplified - would need proper type coercion
      sorry
  | .extCall fn a => .extCall fn (lowerAction a)

/-- Lower a typed rule to a lowered rule -/
def lowerRule (rl : Rule reg_t ext_fn_t R Sigma)
    : LRule reg_t ext_fn_t (lowerR R) (lowerSigma Sigma) :=
  lowerAction R Sigma rl

end Lower

/-! ## Lower Register State -/

/-- Lower register state from typed to bitvectors -/
def lowerRegState {reg_t : Type}
    (R : reg_t → Ty)
    (env : (r : reg_t) → (R r).denote)
    : (r : reg_t) → BitVec (R r).size :=
  fun r => bitsOfValue (env r)

end Koika
