/-
  Koika/TypedSyntax.lean - Port of coq/TypedSyntax.v
  Typed AST for Kôika programs (after type inference)
-/

import Koika.Types
import Koika.Primitives

namespace Koika

/-! ## Context Membership

A proof that a variable with a given type is in the context.
-/

/-- Membership witness for a variable in a context -/
inductive Member : (String × Ty) → List (String × Ty) → Type where
  | here : Member (k, tau) ((k, tau) :: sig)
  | there : Member (k, tau) sig → Member (k, tau) ((k', tau') :: sig)
  deriving Repr

/-- Look up a variable in context -/
def lookupMember (k : String) : (sig : List (String × Ty)) → Option (Σ tau, Member (k, tau) sig)
  | [] => none
  | (k', tau) :: rest =>
      if h : k = k' then
        some ⟨tau, h ▸ .here⟩
      else
        match lookupMember k rest with
        | some ⟨tau', m⟩ => some ⟨tau', .there m⟩
        | none => none

/-- Extract the variable name from a membership witness -/
def Member.varName {k : String} {tau : Ty} {sig : List (String × Ty)}
    : Member (k, tau) sig → String
  | .here => k
  | .there m => m.varName

/-! ## Typed Context

A context maps variable names to typed values.
-/

/-- A typed context storing values for each variable in the signature -/
inductive TContext : List (String × Ty) → Type where
  | empty : TContext []
  | cons : {k : String} → (tau : Ty) → tau.denote → TContext sig → TContext ((k, tau) :: sig)

/-- Get a value from a typed context -/
def TContext.get : TContext sig → Member (k, tau) sig → tau.denote
  | .cons _ v _, .here => v
  | .cons _ _ ctx, .there m => ctx.get m

/-- Set a value in a typed context -/
def TContext.set : TContext sig → Member (k, tau) sig → tau.denote → TContext sig
  | .cons _ _ ctx, .here, v => .cons _ v ctx
  | .cons tau' v' ctx, .there m, v => .cons tau' v' (ctx.set m v)

/-! ## Typed Action

The typed AST after type inference. Each node is annotated with its type.
We use `Type 1` to allow register/external function types to be in `Type`.
-/

/-- Typed action - the AST after type inference -/
inductive Action (reg_t : Type) (ext_fn_t : Type)
    (R : reg_t → Ty) (Sigma : ext_fn_t → ExternalSig)
    : (sig : List (String × Ty)) → (tau : Ty) → Type 1 where
  | fail : (tau : Ty) → Action reg_t ext_fn_t R Sigma sig tau
  | var : Member (k, tau) sig → Action reg_t ext_fn_t R Sigma sig tau
  | const : tau.denote → Action reg_t ext_fn_t R Sigma sig tau
  | assign : Member (k, tau) sig → Action reg_t ext_fn_t R Sigma sig tau →
             Action reg_t ext_fn_t R Sigma sig unitTy
  | seq : Action reg_t ext_fn_t R Sigma sig unitTy →
          Action reg_t ext_fn_t R Sigma sig tau →
          Action reg_t ext_fn_t R Sigma sig tau
  | bind : (v : String) → Action reg_t ext_fn_t R Sigma sig tau₁ →
           Action reg_t ext_fn_t R Sigma ((v, tau₁) :: sig) tau₂ →
           Action reg_t ext_fn_t R Sigma sig tau₂
  | «if» : Action reg_t ext_fn_t R Sigma sig (.bits 1) →
           Action reg_t ext_fn_t R Sigma sig tau →
           Action reg_t ext_fn_t R Sigma sig tau →
           Action reg_t ext_fn_t R Sigma sig tau
  | read : Port → (reg : reg_t) → Action reg_t ext_fn_t R Sigma sig (R reg)
  | write : Port → (reg : reg_t) → Action reg_t ext_fn_t R Sigma sig (R reg) →
            Action reg_t ext_fn_t R Sigma sig unitTy
  | unop : (fn : Typed.Fn1) →
           Action reg_t ext_fn_t R Sigma sig (Sig.arg1 fn) →
           Action reg_t ext_fn_t R Sigma sig (Sig.ret1 fn)
  | binop : (fn : Typed.Fn2) →
            Action reg_t ext_fn_t R Sigma sig (Sig.args2 fn).1 →
            Action reg_t ext_fn_t R Sigma sig (Sig.args2 fn).2 →
            Action reg_t ext_fn_t R Sigma sig (Sig.ret2 fn)
  | extCall : (fn : ext_fn_t) →
              Action reg_t ext_fn_t R Sigma sig (Sigma fn).argType →
              Action reg_t ext_fn_t R Sigma sig (Sigma fn).retType

/-- A rule is a closed action returning unit -/
abbrev Rule (reg_t ext_fn_t : Type) (R : reg_t → Ty) (Sigma : ext_fn_t → ExternalSig) :=
  Action reg_t ext_fn_t R Sigma [] unitTy

/-! ## Action Utilities -/

namespace Action

variable {reg_t ext_fn_t : Type} {R : reg_t → Ty} {Sigma : ext_fn_t → ExternalSig}

/-- Create a sequence of actions from a list -/
def seqMany : List (Action reg_t ext_fn_t R Sigma sig unitTy) →
              Action reg_t ext_fn_t R Sigma sig unitTy
  | [] => .const (0 : BitVec 0)  -- unitTy.denote is BitVec 0
  | [a] => a
  | a :: as => .seq a (seqMany as)

/-- Map a function over all subactions (shallow) -/
def mapChildren (f : ∀ tau, Action reg_t ext_fn_t R Sigma sig tau →
                            Action reg_t ext_fn_t R Sigma sig tau)
    : Action reg_t ext_fn_t R Sigma sig tau → Action reg_t ext_fn_t R Sigma sig tau
  | .fail tau => .fail tau
  | .var m => .var m
  | .const c => .const c
  | .assign m e => .assign m (f _ e)
  | .seq a b => .seq (f _ a) (f _ b)
  | .bind v e body => .bind v (f _ e) body  -- body has different sig
  | .if c t e => .if (f _ c) (f _ t) (f _ e)
  | .read p r => .read p r
  | .write p r v => .write p r (f _ v)
  | .unop fn a => .unop fn (f _ a)
  | .binop fn a b => .binop fn (f _ a) (f _ b)
  | .extCall fn a => .extCall fn (f _ a)

end Action

end Koika
