/-
  Koika/Syntax.lean - Port of coq/Syntax.v
  Untyped syntax for Kôika programs
-/

import Koika.Types
import Koika.Primitives

namespace Koika

/-! ## Error Types -/

/-- Basic type error messages -/
inductive BasicErrorMsg where
  | outOfBounds (pos : Nat) (elemType : Ty) (len : Nat)
  | unboundField (f : String) (structName : String)
  | typeMismatch (actual expected : Ty)
  | kindMismatch (actual expected : TyKind)
  deriving Repr

/-- Error messages -/
inductive ErrorMsg (var_t fn_name_t : Type) where
  | explicitErrorInAst
  | sugaredConstructorInAst
  | unboundVariable (var : var_t)
  | unboundEnumMember (f : String) (sig : EnumSig)
  | basicError (msg : BasicErrorMsg)
  | tooManyArguments (fnName : fn_name_t) (nexpected nextra : Nat)
  | tooFewArguments (fnName : fn_name_t) (nexpected nmissing : Nat)
  deriving Repr

/-- Location in function for type checking errors -/
inductive FnTcErrorLoc where
  | arg1 | arg2
  deriving Repr, BEq, DecidableEq

/-- Error with position information -/
structure Error (pos_t var_t fn_name_t : Type) where
  pos : pos_t
  msg : ErrorMsg var_t fn_name_t
  deriving Repr

/-! ## Internal Function Definition -/

/-- Internal function definition (polymorphic in action type) -/
structure UInternalFn (var_t fn_name_t action : Type) where
  name : fn_name_t
  argSpec : List (var_t × Ty)
  retType : Ty
  body : action
  deriving Repr

/-- Map over the body of an internal function -/
def UInternalFn.mapBody (f : α → β) (fn : UInternalFn var_t fn_name_t α)
    : UInternalFn var_t fn_name_t β :=
  { fn with body := f fn.body }

/-! ## Untyped Syntax

USugar: Syntactic sugar - desugars to UAction
UAction: Untyped action - the core AST before type checking
-/

mutual
  inductive USugar (pos_t var_t fn_name_t reg_t ext_fn_t : Type) where
    | errorInAst
    | skip
    | constBits (sz : Nat) (bs : BitVec sz)
    | constString (s : String)
    | constEnum (sig : EnumSig) (member : String)
    | progn (actions : List (UAction pos_t var_t fn_name_t reg_t ext_fn_t))
    | «let» (bindings : List (var_t × UAction pos_t var_t fn_name_t reg_t ext_fn_t))
            (body : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | when (cond body : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | switch (scrutinee : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
             (default : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
             (branches : List (UAction pos_t var_t fn_name_t reg_t ext_fn_t ×
                               UAction pos_t var_t fn_name_t reg_t ext_fn_t))
    | structInit (name : String) (fields : List (String × Ty))
                 (inits : List (String × UAction pos_t var_t fn_name_t reg_t ext_fn_t))
    | arrayInit (elemType : Ty) (elements : List (UAction pos_t var_t fn_name_t reg_t ext_fn_t))

  inductive UAction (pos_t var_t fn_name_t reg_t ext_fn_t : Type) where
    | error (err : Error pos_t var_t fn_name_t)
    | fail (ty : Ty)
    | var (v : var_t)
    | const (ty : Ty) (val : ty.denote)
    | assign (v : var_t) (e : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | seq (a b : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | bind (v : var_t) (e body : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | «if» (cond tbranch fbranch : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | read (port : Port) (reg : reg_t)
    | write (port : Port) (reg : reg_t) (val : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | unop (fn : Untyped.Fn1) (arg : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | binop (fn : Untyped.Fn2) (arg1 arg2 : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | extCall (fn : ext_fn_t) (arg : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | intCall (fn : UInternalFn var_t fn_name_t (UAction pos_t var_t fn_name_t reg_t ext_fn_t))
              (args : List (UAction pos_t var_t fn_name_t reg_t ext_fn_t))
    | pos (p : pos_t) (e : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    | sugar (s : USugar pos_t var_t fn_name_t reg_t ext_fn_t)
end

/-! ## Scheduler -/

/-- Scheduler for ordering rule execution -/
inductive Scheduler (pos_t rule_name_t : Type) where
  | done
  | cons (r : rule_name_t) (s : Scheduler pos_t rule_name_t)
  | try_ (r : rule_name_t) (s1 s2 : Scheduler pos_t rule_name_t)
  | pos (p : pos_t) (s : Scheduler pos_t rule_name_t)
  deriving Repr

/-! ## Convenient Type Aliases -/

/-- Simple untyped action without position tracking -/
abbrev SimpleUAction (reg_t ext_fn_t : Type) :=
  UAction Unit String String reg_t ext_fn_t

/-- Simple scheduler without position tracking -/
abbrev SimpleScheduler (rule_name_t : Type) :=
  Scheduler Unit rule_name_t

/-! ## Smart Constructors -/

namespace UAction

variable {pos_t var_t fn_name_t reg_t ext_fn_t : Type}

/-- Create a skip action (unit value) -/
def mkSkip : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  .sugar .skip

/-- Create a constant bitvector -/
def mkConstBits (sz : Nat) (bs : BitVec sz) : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  .sugar (.constBits sz bs)

/-- Create a when (guard) expression -/
def mkWhen (cond body : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  .sugar (.when cond body)

/-- Sequence multiple actions -/
def mkProgn (actions : List (UAction pos_t var_t fn_name_t reg_t ext_fn_t))
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  .sugar (.progn actions)

end UAction

/-! ## Scheduler Smart Constructors -/

namespace Scheduler

/-- Create a sequential scheduler from a list of rules -/
def ofList (rules : List rule_name_t) : Scheduler pos_t rule_name_t :=
  rules.foldr (fun r s => .cons r s) .done

/-- Convert scheduler to list of rules (for sequential schedulers) -/
partial def toList : Scheduler pos_t rule_name_t → List rule_name_t
  | .done => []
  | .cons r s => r :: toList s
  | .try_ r s1 _ => r :: toList s1  -- simplified
  | .pos _ s => toList s

end Scheduler

/-! ## Rule Definition -/

/-- An untyped rule is a named action -/
structure URule (pos_t var_t fn_name_t reg_t ext_fn_t rule_name_t : Type) where
  name : rule_name_t
  body : UAction pos_t var_t fn_name_t reg_t ext_fn_t

/-- Simple untyped rule without position tracking -/
abbrev SimpleURule (reg_t ext_fn_t rule_name_t : Type) :=
  URule Unit String String reg_t ext_fn_t rule_name_t

end Koika
