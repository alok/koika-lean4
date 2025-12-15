/-
  Koika/TypeInference.lean - Port of coq/TypeInference.v
  Type inference and typechecking for Kôika programs
-/

import Koika.Types
import Koika.Primitives
import Koika.Syntax
import Koika.TypedSyntax

namespace Koika

/-! ## Type Inference Errors -/

/-- Error during type inference -/
inductive TcError (var_t fn_name_t : Type) where
  | unboundVariable (var : var_t)
  | unboundField (f : String) (structName : String)
  | unboundEnumMember (f : String) (sig : EnumSig)
  | outOfBounds (pos : Nat) (elemType : Ty) (len : Nat)
  | typeMismatch (actual expected : Ty)
  | kindMismatch (expected : String) (actual : Ty)
  | sugaredConstructorInAst
  | explicitErrorInAst
  | tooManyArguments (fnName : fn_name_t) (nexpected nextra : Nat)
  | tooFewArguments (fnName : fn_name_t) (nexpected nmissing : Nat)
  deriving Repr

/-- Result type for type inference -/
abbrev TcResult (var_t fn_name_t α : Type) := Except (TcError var_t fn_name_t) α

/-! ## Primitive Type Inference

Convert untyped primitives to typed primitives given argument types.
-/

namespace PrimTc

open Untyped Typed

/-- Assert a type is bits and return the size -/
def assertBits (tau : Ty) : Except String Nat :=
  match tau with
  | .bits sz => .ok sz
  | _ => .error s!"expected bits type, got {repr tau}"

/-- Assert a type is a struct and return the info -/
def assertStruct (tau : Ty) : Except String (String × List (String × Ty)) :=
  match tau with
  | .struct name fields => .ok (name, fields)
  | _ => .error s!"expected struct type, got {repr tau}"

/-- Assert a type is an array and return the info -/
def assertArray (tau : Ty) : Except String (Ty × Nat) :=
  match tau with
  | .array elemTy len => .ok (elemTy, len)
  | _ => .error s!"expected array type, got {repr tau}"

/-- Find field index in struct -/
def findField (fields : List (String × Ty)) (f : String) : Option Nat :=
  fields.findIdx? (fun (name, _) => name == f)

/-- Type check a unary primitive -/
def tc1 (fn : Untyped.Fn1) (tau1 : Ty) : Except String Typed.Fn1 := do
  match fn with
  | .display (.utf8) =>
      let (_, len) ← assertArray tau1
      return .display (.utf8 len)
  | .display (.value opts) =>
      return .display (.value tau1 opts)
  | .conv .pack =>
      return .conv tau1 .pack
  | .conv (.unpack tau) =>
      return .conv tau .unpack
  | .conv .ignore =>
      return .conv tau1 .ignore
  | .bits1 fn =>
      let sz ← assertBits tau1
      let fn' := match fn with
        | .not => Typed.FBits1.not sz
        | .sext width => .sext sz width
        | .zextL width => .zextL sz width
        | .zextR width => .zextR sz width
        | .repeat times => .repeat sz times
        | .slice offset width => .slice sz offset width
      return .bits1 fn'
  | .struct1 fn =>
      match fn with
      | .getField f =>
          let (name, fields) ← assertStruct tau1
          match findField fields f with
          | some idx => return .struct1 .getField name fields idx
          | none => throw s!"field {f} not found in struct {name}"
      | .getFieldBits structName fields f =>
          match findField fields f with
          | some idx => return .bits1 (.lowered (.ignoreBits 0))  -- TODO: proper impl
          | none => throw s!"field {f} not found"
  | .array1 fn =>
      match fn with
      | .getElement pos =>
          let (elemTy, len) ← assertArray tau1
          if pos < len then
            return .array1 .getElement elemTy len pos
          else
            throw s!"array index {pos} out of bounds (len={len})"
      | .getElementBits elemTy len pos =>
          if pos < len then
            return .bits1 (.lowered (.ignoreBits 0))  -- TODO: proper impl
          else
            throw s!"array index {pos} out of bounds (len={len})"

/-- Type check a binary primitive -/
def tc2 (fn : Untyped.Fn2) (tau1 tau2 : Ty) : Except String Typed.Fn2 := do
  match fn with
  | .eq negate =>
      return .eq tau1 negate
  | .bits2 fn =>
      let sz1 ← assertBits tau1
      let sz2 ← assertBits tau2
      let fn' := match fn with
        | .and => Typed.FBits2.and sz1
        | .or => .or sz1
        | .xor => .xor sz1
        | .lsl => .lsl sz1 sz2
        | .lsr => .lsr sz1 sz2
        | .asr => .asr sz1 sz2
        | .concat => .concat sz1 sz2
        | .sel => .sel sz1
        | .sliceSubst offset width => .sliceSubst sz1 offset width
        | .indexedSlice width => .indexedSlice sz1 width
        | .plus => .plus sz1
        | .minus => .minus sz1
        | .mul => .mul sz1 sz2
        | .compare signed cmp => .compare signed cmp sz1
      return .bits2 fn'
  | .struct2 fn =>
      match fn with
      | .substField f =>
          let (name, fields) ← assertStruct tau1
          match findField fields f with
          | some idx => return .struct2 .substField name fields idx
          | none => throw s!"field {f} not found in struct {name}"
      | .substFieldBits structName fields f =>
          match findField fields f with
          | some idx => return .struct2 .substField structName fields idx
          | none => throw s!"field {f} not found"
  | .array2 fn =>
      match fn with
      | .substElement pos =>
          let (elemTy, len) ← assertArray tau1
          if pos < len then
            return .array2 .substElement elemTy len pos
          else
            throw s!"array index {pos} out of bounds (len={len})"
      | .substElementBits elemTy len pos =>
          if pos < len then
            return .array2 .substElement elemTy len pos
          else
            throw s!"array index {pos} out of bounds (len={len})"

end PrimTc

/-! ## Main Type Inference -/

section TypeInference

variable {reg_t ext_fn_t : Type}
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Result of type inference: a type paired with a typed action.
    This lives in Type 1 because Action is in Type 1. -/
structure TypedActionResult (sig : List (String × Ty)) where
  tau : Ty
  action : Action reg_t ext_fn_t R Sigma sig tau

/-- Inhabited instance for partial recursion -/
instance : Inhabited (TypedActionResult (reg_t := reg_t) (ext_fn_t := ext_fn_t) R Sigma sig) :=
  ⟨⟨unitTy, .fail unitTy⟩⟩

/-- Result type for type inference -/
abbrev TcActionResult (sig : List (String × Ty)) :=
  Except (TcError String String) (TypedActionResult R Sigma sig)

/-- Lookup a variable in the context -/
def lookupVar (sig : List (String × Ty)) (v : String)
    : Except (TcError String String) (Σ tau, Member (v, tau) sig) :=
  match lookupMember v sig with
  | some result => Except.ok result
  | none => Except.error (.unboundVariable v)

/-- Cast a typed action to a specific type -/
def castAction (sig : List (String × Ty)) (tau_actual tau_expected : Ty)
    (a : Action reg_t ext_fn_t R Sigma sig tau_actual)
    : Except (TcError String String) (Action reg_t ext_fn_t R Sigma sig tau_expected) :=
  if h : tau_actual = tau_expected then
    Except.ok (h ▸ a)
  else
    Except.error (.typeMismatch tau_actual tau_expected)

/-- Type check an untyped action, producing a typed action -/
partial def typeAction
    (sig : List (String × Ty))
    (e : UAction Unit String String reg_t ext_fn_t)
    : TcActionResult R Sigma sig :=
  match e with
  | .error _ => Except.error .explicitErrorInAst
  | .sugar _ => Except.error .sugaredConstructorInAst
  | .fail tau => Except.ok ⟨tau, .fail tau⟩
  | .var v =>
      match lookupVar sig v with
      | .error err => Except.error err
      | .ok ⟨tau, m⟩ => Except.ok ⟨tau, .var m⟩
  | .const tau val =>
      Except.ok ⟨tau, .const val⟩
  | .assign v expr =>
      match lookupVar sig v with
      | .error err => Except.error err
      | .ok ⟨tau, m⟩ =>
          match typeAction sig expr with
          | .error err => Except.error err
          | .ok result =>
              match castAction R Sigma sig result.tau tau result.action with
              | .error err => Except.error err
              | .ok e'' => Except.ok ⟨unitTy, .assign m e''⟩
  | .seq a b =>
      match typeAction sig a with
      | .error err => Except.error err
      | .ok ra =>
          match castAction R Sigma sig ra.tau unitTy ra.action with
          | .error err => Except.error err
          | .ok a'' =>
              match typeAction sig b with
              | .error err => Except.error err
              | .ok rb => Except.ok ⟨rb.tau, .seq a'' rb.action⟩
  | .bind v expr body =>
      match typeAction sig expr with
      | .error err => Except.error err
      | .ok re =>
          match typeAction ((v, re.tau) :: sig) body with
          | .error err => Except.error err
          | .ok rb => Except.ok ⟨rb.tau, .bind v re.action rb.action⟩
  | .if cond tbranch fbranch =>
      match typeAction sig cond with
      | .error err => Except.error err
      | .ok rc =>
          match castAction R Sigma sig rc.tau (.bits 1) rc.action with
          | .error err => Except.error err
          | .ok c'' =>
              match typeAction sig tbranch with
              | .error err => Except.error err
              | .ok rt =>
                  match typeAction sig fbranch with
                  | .error err => Except.error err
                  | .ok rf =>
                      match castAction R Sigma sig rf.tau rt.tau rf.action with
                      | .error err => Except.error err
                      | .ok f'' => Except.ok ⟨rt.tau, .if c'' rt.action f''⟩
  | .read port reg =>
      Except.ok ⟨R reg, .read port reg⟩
  | .write port reg val =>
      match typeAction sig val with
      | .error err => Except.error err
      | .ok rv =>
          match castAction R Sigma sig rv.tau (R reg) rv.action with
          | .error err => Except.error err
          | .ok v'' => Except.ok ⟨unitTy, .write port reg v''⟩
  | .unop fn arg =>
      match typeAction sig arg with
      | .error err => Except.error err
      | .ok ra =>
          match PrimTc.tc1 fn ra.tau with
          | .error msg => Except.error (.kindMismatch msg ra.tau)
          | .ok fn' =>
              match castAction R Sigma sig ra.tau (Sig.arg1 fn') ra.action with
              | .error err => Except.error err
              | .ok arg'' => Except.ok ⟨Sig.ret1 fn', .unop fn' arg''⟩
  | .binop fn arg1 arg2 =>
      match typeAction sig arg1 with
      | .error err => Except.error err
      | .ok r1 =>
          match typeAction sig arg2 with
          | .error err => Except.error err
          | .ok r2 =>
              match PrimTc.tc2 fn r1.tau r2.tau with
              | .error msg => Except.error (.kindMismatch msg r1.tau)
              | .ok fn' =>
                  match castAction R Sigma sig r1.tau (Sig.args2 fn').1 r1.action with
                  | .error err => Except.error err
                  | .ok arg1'' =>
                      match castAction R Sigma sig r2.tau (Sig.args2 fn').2 r2.action with
                      | .error err => Except.error err
                      | .ok arg2'' => Except.ok ⟨Sig.ret2 fn', .binop fn' arg1'' arg2''⟩
  | .extCall fn arg =>
      match typeAction sig arg with
      | .error err => Except.error err
      | .ok ra =>
          match castAction R Sigma sig ra.tau (Sigma fn).argType ra.action with
          | .error err => Except.error err
          | .ok arg'' => Except.ok ⟨(Sigma fn).retType, .extCall fn arg''⟩
  | .intCall _ _ =>
      -- Internal calls would need special handling
      Except.error (.kindMismatch "internal calls not yet supported" unitTy)
  | .pos _ inner =>
      -- Position wrapper - just type check the inner expression
      typeAction sig inner

/-- Type check an action against an expected type -/
def tcAction
    (sig : List (String × Ty))
    (expected : Ty)
    (e : UAction Unit String String reg_t ext_fn_t)
    : Except (TcError String String) (Action reg_t ext_fn_t R Sigma sig expected) :=
  match typeAction R Sigma sig e with
  | .error err => Except.error err
  | .ok result => castAction R Sigma sig result.tau expected result.action

/-- Type check a rule (closed action returning unit) -/
def tcRule (e : UAction Unit String String reg_t ext_fn_t)
    : Except (TcError String String) (Rule reg_t ext_fn_t R Sigma) :=
  tcAction R Sigma [] unitTy e

end TypeInference

end Koika
