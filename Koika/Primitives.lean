/-
  Koika/Primitives.lean - Port of coq/Primitives.v
  Combinational primitives available in all Kôika programs
-/

import Koika.Types

namespace Koika

/-! ## Comparison Types -/

inductive Comparison where
  | lt | gt | le | ge
  deriving DecidableEq, Repr, BEq

/-! ## Display Options -/

inductive DisplayStyle where
  | bin | dec | hex | full
  deriving DecidableEq, Repr, BEq

structure DisplayOptions where
  showStrings : Bool := true
  showNewline : Bool := true
  style : DisplayStyle := .dec
  deriving Repr, BEq

/-! ## Untyped Primitives (before type inference) -/

namespace Untyped

inductive Display where
  | utf8
  | value (opts : DisplayOptions)
  deriving Repr, BEq

inductive Conv where
  | pack
  | unpack (tau : Ty)
  | ignore
  deriving Repr

inductive Bits1 where
  | not
  | sext (width : Nat)
  | zextL (width : Nat)
  | zextR (width : Nat)
  | «repeat» (times : Nat)
  | slice (offset width : Nat)
  deriving Repr, BEq

inductive Bits2 where
  | and | or | xor
  | lsl | lsr | asr
  | concat
  | sel
  | sliceSubst (offset width : Nat)
  | indexedSlice (width : Nat)
  | plus | minus | mul
  | compare (signed : Bool) (cmp : Comparison)
  deriving Repr

inductive Struct1 where
  | getField (f : String)
  | getFieldBits (structName : String) (fields : List (String × Ty)) (f : String)
  deriving Repr

inductive Struct2 where
  | substField (f : String)
  | substFieldBits (structName : String) (fields : List (String × Ty)) (f : String)
  deriving Repr

inductive Array1 where
  | getElement (pos : Nat)
  | getElementBits (elemType : Ty) (len : Nat) (pos : Nat)
  deriving Repr

inductive Array2 where
  | substElement (pos : Nat)
  | substElementBits (elemType : Ty) (len : Nat) (pos : Nat)
  deriving Repr

/-- Untyped unary function -/
inductive Fn1 where
  | display (fn : Display)
  | conv (fn : Conv)
  | bits1 (fn : Bits1)
  | struct1 (fn : Struct1)
  | array1 (fn : Array1)
  deriving Repr

/-- Untyped binary function -/
inductive Fn2 where
  | eq (negate : Bool)
  | bits2 (fn : Bits2)
  | struct2 (fn : Struct2)
  | array2 (fn : Array2)
  deriving Repr

end Untyped

/-! ## Typed Primitives (after type inference) -/

namespace Typed

inductive FDisplay where
  | utf8 (len : Nat)
  | value (tau : Ty) (opts : DisplayOptions)
  deriving Repr

inductive FConv where
  | pack | unpack | ignore
  deriving Repr, BEq, DecidableEq

inductive Lowered1 where
  | ignoreBits (sz : Nat)
  | displayBits (fn : FDisplay)
  deriving Repr

/-- Typed bitvector unary operations -/
inductive FBits1 where
  | not (sz : Nat)
  | sext (sz width : Nat)
  | zextL (sz width : Nat)
  | zextR (sz width : Nat)
  | «repeat» (sz times : Nat)
  | slice (sz offset width : Nat)
  | lowered (fn : Lowered1)
  deriving Repr

/-- Typed bitvector binary operations -/
inductive FBits2 where
  | and (sz : Nat)
  | or (sz : Nat)
  | xor (sz : Nat)
  | lsl (bitsSz shiftSz : Nat)
  | lsr (bitsSz shiftSz : Nat)
  | asr (bitsSz shiftSz : Nat)
  | concat (sz1 sz2 : Nat)
  | sel (sz : Nat)
  | sliceSubst (sz offset width : Nat)
  | indexedSlice (sz width : Nat)
  | plus (sz : Nat)
  | minus (sz : Nat)
  | mul (sz1 sz2 : Nat)
  | eqBits (sz : Nat) (negate : Bool)
  | compare (signed : Bool) (cmp : Comparison) (sz : Nat)
  deriving Repr

inductive FStruct1 where
  | getField
  deriving Repr, BEq, DecidableEq

inductive FStruct2 where
  | substField
  deriving Repr, BEq, DecidableEq

inductive FArray1 where
  | getElement
  deriving Repr, BEq, DecidableEq

inductive FArray2 where
  | substElement
  deriving Repr, BEq, DecidableEq

/-- Typed unary function -/
inductive Fn1 where
  | display (fn : FDisplay)
  | conv (tau : Ty) (fn : FConv)
  | bits1 (fn : FBits1)
  | struct1 (fn : FStruct1) (structName : String) (fields : List (String × Ty)) (fieldIdx : Nat)
  | array1 (fn : FArray1) (elemType : Ty) (len : Nat) (idx : Nat)
  deriving Repr

/-- Typed binary function -/
inductive Fn2 where
  | eq (tau : Ty) (negate : Bool)
  | bits2 (fn : FBits2)
  | struct2 (fn : FStruct2) (structName : String) (fields : List (String × Ty)) (fieldIdx : Nat)
  | array2 (fn : FArray2) (elemType : Ty) (len : Nat) (idx : Nat)
  deriving Repr

end Typed

/-! ## Circuit-Level Signatures (sizes only) -/

namespace Circuit

/-- Signature for unary bitvector operation -/
def sig1 (fn : Typed.FBits1) : Nat × Nat :=
  match fn with
  | .not sz => (sz, sz)
  | .sext sz width => (sz, max sz width)
  | .zextL sz width => (sz, max sz width)
  | .zextR sz width => (sz, max sz width)
  | .repeat sz times => (sz, times * sz)
  | .slice sz _ width => (sz, width)
  | .lowered (.ignoreBits sz) => (sz, 0)
  | .lowered (.displayBits (.utf8 len)) => (len * 8, 0)
  | .lowered (.displayBits (.value tau _)) => (tau.size, 0)

/-- Signature for binary bitvector operation -/
def sig2 (fn : Typed.FBits2) : Nat × Nat × Nat :=
  match fn with
  | .sel sz => (sz, Nat.log2 sz, 1)
  | .sliceSubst sz _ width => (sz, width, sz)
  | .indexedSlice sz width => (sz, Nat.log2 sz, width)
  | .and sz => (sz, sz, sz)
  | .or sz => (sz, sz, sz)
  | .xor sz => (sz, sz, sz)
  | .lsl bitsSz shiftSz => (bitsSz, shiftSz, bitsSz)
  | .lsr bitsSz shiftSz => (bitsSz, shiftSz, bitsSz)
  | .asr bitsSz shiftSz => (bitsSz, shiftSz, bitsSz)
  | .concat sz1 sz2 => (sz1, sz2, sz2 + sz1)
  | .eqBits sz _ => (sz, sz, 1)
  | .plus sz => (sz, sz, sz)
  | .minus sz => (sz, sz, sz)
  | .mul sz1 sz2 => (sz1, sz2, sz1 + sz2)
  | .compare _ _ sz => (sz, sz, 1)

end Circuit

/-! ## High-Level Signatures (types) -/

namespace Sig

/-- Argument type for unary function -/
def arg1 (fn : Typed.Fn1) : Ty :=
  match fn with
  | .display (.utf8 len) => .array (.bits 8) len
  | .display (.value tau _) => tau
  | .conv tau .pack => tau
  | .conv tau .unpack => .bits tau.size
  | .conv tau .ignore => tau
  | .bits1 fn => .bits (Circuit.sig1 fn).1
  | .struct1 _ name fields _ => .struct name fields
  | .array1 _ elemType len _ => .array elemType len

/-- Return type for unary function -/
def ret1 (fn : Typed.Fn1) : Ty :=
  match fn with
  | .display _ => unitTy
  | .conv tau .pack => .bits tau.size
  | .conv tau .unpack => tau
  | .conv _ .ignore => unitTy
  | .bits1 fn => .bits (Circuit.sig1 fn).2
  | .struct1 _ _ fields idx =>
      match fields[idx]? with
      | some (_, ty) => ty
      | none => unitTy  -- shouldn't happen
  | .array1 _ elemType _ _ => elemType

/-- Argument types for binary function -/
def args2 (fn : Typed.Fn2) : Ty × Ty :=
  match fn with
  | .eq tau _ => (tau, tau)
  | .bits2 fn =>
      let (a1, a2, _) := Circuit.sig2 fn
      (.bits a1, .bits a2)
  | .struct2 _ name fields idx =>
      let fieldTy := match fields[idx]? with
        | some (_, ty) => ty
        | none => unitTy
      (.struct name fields, fieldTy)
  | .array2 _ elemType len _ => (.array elemType len, elemType)

/-- Return type for binary function -/
def ret2 (fn : Typed.Fn2) : Ty :=
  match fn with
  | .eq _ _ => .bits 1
  | .bits2 fn => .bits (Circuit.sig2 fn).2.2
  | .struct2 _ name fields _ => .struct name fields
  | .array2 _ elemType len _ => .array elemType len

end Sig

/-! ## Primitive Semantics -/

namespace Sem

/-- Select a single bit from bitvector by index -/
def sel (bs : BitVec sz) (idx : BitVec idxSz) : BitVec 1 :=
  let i := idx.toNat
  if h : i < sz then
    BitVec.ofBool (bs.getLsbD i)
  else
    0

/-- Logical shift left -/
def lsl (bs : BitVec bitsSz) (places : BitVec shiftSz) : BitVec bitsSz :=
  bs <<< places.toNat

/-- Logical shift right -/
def lsr (bs : BitVec bitsSz) (places : BitVec shiftSz) : BitVec bitsSz :=
  bs >>> places.toNat

/-- Arithmetic shift right -/
def asr (bs : BitVec bitsSz) (places : BitVec shiftSz) : BitVec bitsSz :=
  BitVec.sshiftRight bs places.toNat

/-- Equality check returning 1-bit result -/
def beqBits (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if bs1 == bs2 then 1 else 0

/-- Inequality check returning 1-bit result -/
def bneBits (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if bs1 == bs2 then 0 else 1

/-- Unsigned less-than -/
def ult (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if BitVec.ult bs1 bs2 then 1 else 0

/-- Unsigned less-or-equal -/
def ule (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if BitVec.ule bs1 bs2 then 1 else 0

/-- Unsigned greater-than -/
def ugt (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if BitVec.ult bs2 bs1 then 1 else 0

/-- Unsigned greater-or-equal -/
def uge (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if BitVec.ule bs2 bs1 then 1 else 0

/-- Signed less-than -/
def slt (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if BitVec.slt bs1 bs2 then 1 else 0

/-- Signed less-or-equal -/
def sle (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if BitVec.sle bs1 bs2 then 1 else 0

/-- Signed greater-than -/
def sgt (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if BitVec.slt bs2 bs1 then 1 else 0

/-- Signed greater-or-equal -/
def sge (bs1 bs2 : BitVec sz) : BitVec 1 :=
  if BitVec.sle bs2 bs1 then 1 else 0

/-- Execute a comparison -/
def compare (signed : Bool) (cmp : Comparison) (bs1 bs2 : BitVec sz) : BitVec 1 :=
  match signed, cmp with
  | false, .lt => ult bs1 bs2
  | false, .le => ule bs1 bs2
  | false, .gt => ugt bs1 bs2
  | false, .ge => uge bs1 bs2
  | true, .lt => slt bs1 bs2
  | true, .le => sle bs1 bs2
  | true, .gt => sgt bs1 bs2
  | true, .ge => sge bs1 bs2

/-- Interpret typed unary bitvector operation -/
def interp1 (fn : Typed.FBits1) : BitVec (Circuit.sig1 fn).1 → BitVec (Circuit.sig1 fn).2 :=
  match fn with
  | .not sz => fun bs => ~~~bs
  | .sext sz width => fun bs =>
      -- Sign extend preserving sign
      BitVec.signExtend (max sz width) bs
  | .zextL sz width => fun bs =>
      BitVec.ofNat (max sz width) bs.toNat
  | .zextR sz width => fun bs =>
      -- Extend on the right (LSB side) with zeros
      BitVec.ofNat (max sz width) (bs.toNat * (2 ^ (max sz width - sz)))
  | .repeat sz times => fun bs =>
      -- Repeat the bitvector `times` times
      let result := (List.replicate times bs.toNat).foldl
        (fun acc v => acc * (2 ^ sz) + v) 0
      BitVec.ofNat (times * sz) result
  | .slice sz offset width => fun bs =>
      bs.extractLsb' offset width
  | .lowered (.ignoreBits _) => fun _ => 0
  | .lowered (.displayBits _) => fun _ => 0

/-- Interpret typed binary bitvector operation -/
def interp2 (fn : Typed.FBits2)
    : BitVec (Circuit.sig2 fn).1 → BitVec (Circuit.sig2 fn).2.1 → BitVec (Circuit.sig2 fn).2.2 :=
  match fn with
  | .sel sz => fun bs idx => sel bs idx
  | .sliceSubst sz offset width => fun bs v =>
      -- Replace slice at offset with v
      let mask : Nat := ((1 <<< width) - 1) <<< offset
      let cleared := bs.toNat &&& (Nat.xor mask (2^sz - 1))
      let inserted := (v.toNat &&& ((1 <<< width) - 1)) <<< offset
      BitVec.ofNat sz (cleared ||| inserted)
  | .indexedSlice sz width => fun bs offset =>
      bs.extractLsb' offset.toNat width
  | .and sz => fun a b =>
      BitVec.ofNat sz (a.toNat &&& b.toNat)
  | .or sz => fun a b =>
      BitVec.ofNat sz (a.toNat ||| b.toNat)
  | .xor sz => fun a b =>
      BitVec.ofNat sz (Nat.xor a.toNat b.toNat)
  | .lsl bitsSz _ => fun bs places => lsl bs places
  | .lsr bitsSz _ => fun bs places => lsr bs places
  | .asr bitsSz _ => fun bs places => asr bs places
  | .concat sz1 sz2 => fun a b =>
      -- a is MSB, b is LSB
      let result := a.toNat * (2 ^ sz2) + b.toNat
      BitVec.ofNat (sz2 + sz1) result
  | .plus sz => fun a b =>
      BitVec.ofNat sz (a.toNat + b.toNat)
  | .minus sz => fun a b =>
      BitVec.ofNat sz (a.toNat - b.toNat)
  | .mul sz1 sz2 => fun a b =>
      BitVec.ofNat (sz1 + sz2) (a.toNat * b.toNat)
  | .eqBits sz false => fun a b => beqBits a b
  | .eqBits sz true => fun a b => bneBits a b
  | .compare signed cmp sz => fun a b => compare signed cmp a b

end Sem

end Koika
