/-
  Koika/Types.lean - Port of coq/Types.v
  Core type system for Kôika programs
-/

import Lean.Data.Format

namespace Koika

/-! ## Read/Write Ports -/

inductive Port where
  | p0
  | p1
  deriving DecidableEq, Repr, Inhabited, BEq

/-! ## Type Signatures -/

/-- Enum signature: named enumeration with bit patterns -/
structure EnumSig where
  name : String
  size : Nat  -- number of members
  bitsize : Nat  -- bit width for encoding
  members : Array String  -- member names (length = size)
  deriving Repr, BEq, DecidableEq

/-! ## Kôika Types -/

/-- Core type system for Kôika -/
inductive Ty where
  | bits (sz : Nat)
  | enum (sig : EnumSig)
  | struct (name : String) (fields : List (String × Ty))
  | array (elemType : Ty) (len : Nat)

/-- Unit type is 0-bit bitvector -/
abbrev unitTy : Ty := .bits 0

/-! ## BEq and DecidableEq for Ty -/

mutual
  def Ty.beq : Ty → Ty → Bool
    | .bits sz1, .bits sz2 => sz1 == sz2
    | .enum sig1, .enum sig2 => sig1 == sig2
    | .struct n1 f1, .struct n2 f2 => n1 == n2 && fieldsBeq f1 f2
    | .array t1 l1, .array t2 l2 => Ty.beq t1 t2 && l1 == l2
    | _, _ => false

  def fieldsBeq : List (String × Ty) → List (String × Ty) → Bool
    | [], [] => true
    | (n1, t1) :: rest1, (n2, t2) :: rest2 =>
        n1 == n2 && Ty.beq t1 t2 && fieldsBeq rest1 rest2
    | _, _ => false
end

instance : BEq Ty := ⟨Ty.beq⟩

instance : DecidableEq Ty := fun t1 t2 =>
  if t1.beq t2 then isTrue (by sorry) else isFalse (by sorry)

/-! ## Repr for Ty -/

mutual
  partial def Ty.reprPrec : Ty → Nat → Lean.Format
    | .bits sz, _ => f!"Ty.bits {sz}"
    | .enum sig, _ => f!"Ty.enum {repr sig}"
    | .struct name fields, _ => f!"Ty.struct {repr name} {fieldsRepr fields}"
    | .array elemType len, _ => f!"Ty.array ({Ty.reprPrec elemType 0}) {len}"

  partial def fieldsRepr : List (String × Ty) → Lean.Format
    | [] => "[]"
    | fields => f!"[{fields.map (fun (n, t) => f!"({repr n}, {Ty.reprPrec t 0})")}]"
end

instance : Repr Ty := ⟨Ty.reprPrec⟩

/-! ## Type Kind (for pattern matching without full details) -/

inductive TyKind where
  | bits
  | enum
  | struct
  | array
  deriving DecidableEq, Repr

def Ty.kind : Ty → TyKind
  | .bits _ => .bits
  | .enum _ => .enum
  | .struct _ _ => .struct
  | .array _ _ => .array

/-! ## Type Size Computation -/

mutual
  /-- Compute bit width of a type -/
  def Ty.size : Ty → Nat
    | .bits sz => sz
    | .enum sig => sig.bitsize
    | .struct _ fields => fieldsSize fields
    | .array elemType len => len * Ty.size elemType

  def fieldsSize : List (String × Ty) → Nat
    | [] => 0
    | (_, ty) :: rest => Ty.size ty + fieldsSize rest
end

/-! ## Type Denotation (Lean type for Kôika type) -/

mutual
  /-- Lean type corresponding to a Kôika type -/
  def Ty.denote : Ty → Type
    | .bits sz => BitVec sz
    | .enum sig => BitVec sig.bitsize
    | .struct _ fields => fieldsDenote fields
    | .array elemType len => Fin len → Ty.denote elemType

  def fieldsDenote : List (String × Ty) → Type
    | [] => Unit
    | (_, ty) :: rest => Ty.denote ty × fieldsDenote rest
end

/-! ## Default Values -/

mutual
  /-- Default (zero) value for a type -/
  def Ty.default : (ty : Ty) → ty.denote
    | .bits sz => (0 : BitVec sz)
    | .enum sig => (0 : BitVec sig.bitsize)
    | .struct _ fields => fieldsDefault fields
    | .array elemType _ => fun _ => Ty.default elemType

  def fieldsDefault : (fields : List (String × Ty)) → fieldsDenote fields
    | [] => ()
    | (_, ty) :: rest => (Ty.default ty, fieldsDefault rest)
end

instance (ty : Ty) : Inhabited ty.denote := ⟨Ty.default ty⟩

/-! ## Struct Field Access -/

/-- Get field type by name -/
def Ty.fieldType? (ty : Ty) (fieldName : String) : Option Ty :=
  match ty with
  | .struct _ fields => fields.lookup fieldName
  | _ => none

/-- Number of fields in a struct -/
def Ty.numFields : Ty → Nat
  | .struct _ fields => fields.length
  | _ => 0

/-! ## Function Signatures -/

/-- Generic function signature -/
structure FnSig where
  argTypes : List Ty
  retType : Ty
  deriving Repr

/-- External function signature (1 argument) -/
structure ExternalSig where
  argType : Ty
  retType : Ty
  deriving Repr

/-- Lowered (circuit-level) signature with sizes instead of types -/
structure CExternalSig where
  argSize : Nat
  retSize : Nat
  deriving Repr, BEq, DecidableEq

def ExternalSig.toLowered (sig : ExternalSig) : CExternalSig :=
  { argSize := sig.argType.size
    retSize := sig.retType.size }

def CExternalSig.toTyped (sig : CExternalSig) : ExternalSig :=
  { argType := .bits sig.argSize
    retType := .bits sig.retSize }

/-! ## Internal Function Signature -/

/-- Type signature for local variables -/
abbrev TSig (var_t : Type) := List (var_t × Ty)

/-- Lowered signature (just sizes) -/
abbrev LSig := List Nat

def TSig.toLSig (sig : TSig var_t) : LSig :=
  sig.map (fun (_, ty) => ty.size)

/-- Internal function definition -/
structure InternalFn (var_t fn_name_t action : Type) where
  name : fn_name_t
  argSpec : TSig var_t
  retType : Ty
  body : action

def InternalFn.mapBody (f : α → β) (fn : InternalFn var_t fn_name_t α) : InternalFn var_t fn_name_t β :=
  { fn with body := f fn.body }

/-! ## Type ID for debugging -/

def Ty.id : Ty → String
  | .bits sz => s!"bits_{sz}"
  | .enum sig => sig.name
  | .struct name _ => name
  | .array elemType len => s!"array_{len}_{elemType.id}"

/-! ## DecidableEq for denote -/

-- DecidableEq for denote is complex; defer for now
instance (ty : Ty) : DecidableEq ty.denote := fun _ _ => sorry

end Koika
