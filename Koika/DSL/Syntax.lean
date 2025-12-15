/-
  Koika/DSL/Syntax.lean - Macro system for Kôika DSL
  Port of coq/Parsing.v notation system

  The koika! syntax allows writing Kôika programs in a familiar imperative style
  that gets elaborated to UAction terms.
-/

import Koika.Syntax
import Lean

namespace Koika.DSL

open Lean Elab Meta Term
open Koika

/-! ## Custom Syntax Categories -/

declare_syntax_cat koika
declare_syntax_cat koika_bits

/-! ## Bit Constant Syntax -/

-- Binary bit patterns like ~1~0~1
syntax "~0" : koika_bits
syntax "~1" : koika_bits
syntax koika_bits "~0" : koika_bits
syntax koika_bits "~1" : koika_bits

/-! ## Core Koika Syntax -/

-- Atoms
syntax "fail" : koika
syntax "fail" "(" term ")" : koika
syntax "pass" : koika
syntax "magic" : koika

-- Variables
syntax ident : koika

-- Constants
syntax "Ob" koika_bits : koika
syntax "bv" "(" term "," term ")" : koika  -- bv(size, value)

-- Let and sequencing
syntax "klet" ident ":=" koika "kin" koika : koika  -- using klet/kin to avoid conflict
syntax:10 koika ";" koika : koika
syntax "set" ident ":=" koika : koika
syntax "(" koika ")" : koika

-- Control flow
syntax:20 "kif" koika "kthen" koika "kelse" koika : koika
syntax "guard" "(" koika ")" : koika
syntax "when" koika "kdo" koika : koika

-- Register operations
syntax "read0" "(" term ")" : koika
syntax "read1" "(" term ")" : koika
syntax "write0" "(" term "," koika ")" : koika
syntax "write1" "(" term "," koika ")" : koika

-- Binary operations (with precedence)
syntax:80 koika "&&" koika : koika
syntax:85 koika "||" koika : koika
syntax:85 koika "^^" koika : koika  -- xor
syntax:85 koika "+" koika : koika
syntax:85 koika "-" koika : koika
syntax:84 koika "*" koika : koika
syntax:79 koika "==" koika : koika
syntax:79 koika "!=" koika : koika
syntax:79 koika ">>" koika : koika
syntax:79 koika ">>>" koika : koika
syntax:79 koika "<<" koika : koika
syntax:79 koika "<" koika : koika
syntax:79 koika "<s" koika : koika
syntax:79 koika "<=" koika : koika
syntax:79 koika ">" koika : koika
syntax:79 koika ">s" koika : koika
syntax:79 koika ">=" koika : koika
syntax:80 koika "++" koika : koika

-- Unary operations
syntax:75 "!" koika : koika

-- Bit operations
syntax:75 koika "[" koika "]" : koika  -- bit select
syntax:75 koika "[" koika ":+" term "]" : koika  -- indexed slice

-- Extension operations
syntax "zeroExtend" "(" koika "," term ")" : koika
syntax "sext" "(" koika "," term ")" : koika
syntax "kignore" "(" koika ")" : koika
syntax "kpack" "(" koika ")" : koika
syntax "kunpack" "(" term "," koika ")" : koika

-- Struct operations
syntax "kget" "(" koika "," ident ")" : koika
syntax "ksubst" "(" koika "," ident "," koika ")" : koika

-- Array operations
syntax "aref" "(" koika "," term ")" : koika
syntax "asubst" "(" koika "," term "," koika ")" : koika


/-! ## Main Entry Point -/

syntax "koika!" koika : term

/-! ## Macro Expansion Rules -/

-- Helper to build bit constants from koika_bits
partial def expandBitsAux : TSyntax `koika_bits → MacroM (Nat × Nat)
  | `(koika_bits| ~0) => return (1, 0)
  | `(koika_bits| ~1) => return (1, 1)
  | `(koika_bits| $bs:koika_bits ~0) => do
      let (sz, v) ← expandBitsAux bs
      return (sz + 1, v * 2)
  | `(koika_bits| $bs:koika_bits ~1) => do
      let (sz, v) ← expandBitsAux bs
      return (sz + 1, v * 2 + 1)
  | _ => Macro.throwUnsupported

-- Main macro rules
macro_rules
  -- Atoms
  | `(koika! fail) => `(UAction.fail (.bits 0))
  | `(koika! fail ($t:term)) => `(UAction.fail (.bits $t))
  | `(koika! pass) => `(UAction.sugar (.constBits 0 0))
  | `(koika! magic) => `(UAction.sugar .errorInAst)

  -- Variables - convert ident to string literal
  | `(koika! $x:ident) => do
      let nameStr := Syntax.mkStrLit x.getId.toString
      `(UAction.var $nameStr)

  -- Bit constants
  | `(koika! Ob $bs:koika_bits) => do
      let (sz, v) ← expandBitsAux bs
      let szLit := Syntax.mkNumLit (toString sz)
      let vLit := Syntax.mkNumLit (toString v)
      `(UAction.sugar (.constBits $szLit $vLit))
  | `(koika! bv ($sz:term, $v:term)) =>
      `(UAction.sugar (.constBits $sz (BitVec.ofNat $sz $v)))

  -- Let and sequencing
  | `(koika! klet $x:ident := $e kin $body) => do
      let nameStr := Syntax.mkStrLit x.getId.toString
      `(UAction.bind $nameStr (koika! $e) (koika! $body))
  | `(koika! $a ; $b) => `(UAction.seq (koika! $a) (koika! $b))
  | `(koika! set $x:ident := $e) => do
      let nameStr := Syntax.mkStrLit x.getId.toString
      `(UAction.assign $nameStr (koika! $e))
  | `(koika! ( $a )) => `(koika! $a)

  -- Control flow
  | `(koika! kif $c kthen $t kelse $f) => `(UAction.if (koika! $c) (koika! $t) (koika! $f))
  | `(koika! guard ($a)) =>
      `(UAction.if (UAction.unop (.bits1 .not) (koika! $a))
                   (UAction.fail (.bits 0))
                   (UAction.sugar (.constBits 0 0)))
  | `(koika! when $c kdo $t) =>
      `(UAction.if (koika! $c) (koika! $t) (UAction.sugar (.constBits 0 0)))

  -- Register operations
  | `(koika! read0 ($r:term)) => `(UAction.read .p0 $r)
  | `(koika! read1 ($r:term)) => `(UAction.read .p1 $r)
  | `(koika! write0 ($r:term, $v)) => `(UAction.write .p0 $r (koika! $v))
  | `(koika! write1 ($r:term, $v)) => `(UAction.write .p1 $r (koika! $v))

  -- Binary operations
  | `(koika! $a && $b) => `(UAction.binop (.bits2 .and) (koika! $a) (koika! $b))
  | `(koika! $a || $b) => `(UAction.binop (.bits2 .or) (koika! $a) (koika! $b))
  | `(koika! $a ^^ $b) => `(UAction.binop (.bits2 .xor) (koika! $a) (koika! $b))
  | `(koika! $a + $b) => `(UAction.binop (.bits2 .plus) (koika! $a) (koika! $b))
  | `(koika! $a - $b) => `(UAction.binop (.bits2 .minus) (koika! $a) (koika! $b))
  | `(koika! $a * $b) => `(UAction.binop (.bits2 .mul) (koika! $a) (koika! $b))
  | `(koika! $a == $b) => `(UAction.binop (.eq false) (koika! $a) (koika! $b))
  | `(koika! $a != $b) => `(UAction.binop (.eq true) (koika! $a) (koika! $b))
  | `(koika! $a >> $b) => `(UAction.binop (.bits2 .lsr) (koika! $a) (koika! $b))
  | `(koika! $a >>> $b) => `(UAction.binop (.bits2 .asr) (koika! $a) (koika! $b))
  | `(koika! $a << $b) => `(UAction.binop (.bits2 .lsl) (koika! $a) (koika! $b))
  | `(koika! $a < $b) => `(UAction.binop (.bits2 (.compare false .lt)) (koika! $a) (koika! $b))
  | `(koika! $a <s $b) => `(UAction.binop (.bits2 (.compare true .lt)) (koika! $a) (koika! $b))
  | `(koika! $a <= $b) => `(UAction.binop (.bits2 (.compare false .le)) (koika! $a) (koika! $b))
  | `(koika! $a > $b) => `(UAction.binop (.bits2 (.compare false .gt)) (koika! $a) (koika! $b))
  | `(koika! $a >s $b) => `(UAction.binop (.bits2 (.compare true .gt)) (koika! $a) (koika! $b))
  | `(koika! $a >= $b) => `(UAction.binop (.bits2 (.compare false .ge)) (koika! $a) (koika! $b))
  | `(koika! $a ++ $b) => `(UAction.binop (.bits2 .concat) (koika! $a) (koika! $b))

  -- Unary operations
  | `(koika! ! $a) => `(UAction.unop (.bits1 .not) (koika! $a))

  -- Bit operations
  | `(koika! $a [ $b ]) => `(UAction.binop (.bits2 .sel) (koika! $a) (koika! $b))
  | `(koika! $a [ $b :+ $w:term ]) => `(UAction.binop (.bits2 (.indexedSlice $w)) (koika! $a) (koika! $b))

  -- Extension operations
  | `(koika! zeroExtend ($a, $w:term)) => `(UAction.unop (.bits1 (.zextL $w)) (koika! $a))
  | `(koika! sext ($a, $w:term)) => `(UAction.unop (.bits1 (.sext $w)) (koika! $a))
  | `(koika! kignore ($a)) => `(UAction.unop (.conv .ignore) (koika! $a))
  | `(koika! kpack ($a)) => `(UAction.unop (.conv .pack) (koika! $a))
  | `(koika! kunpack ($t:term, $v)) => `(UAction.unop (.conv (.unpack $t)) (koika! $v))

  -- Struct operations
  | `(koika! kget ($v, $f:ident)) => do
      let nameStr := Syntax.mkStrLit f.getId.toString
      `(UAction.unop (.struct1 (.getField $nameStr)) (koika! $v))
  | `(koika! ksubst ($v, $f:ident, $a)) => do
      let nameStr := Syntax.mkStrLit f.getId.toString
      `(UAction.binop (.struct2 (.substField $nameStr)) (koika! $v) (koika! $a))

  -- Array operations
  | `(koika! aref ($v, $i:term)) =>
      `(UAction.unop (.array1 (.getElement $i)) (koika! $v))
  | `(koika! asubst ($v, $i:term, $a)) =>
      `(UAction.binop (.array2 (.substElement $i)) (koika! $v) (koika! $a))


/-! ## Scheduler Syntax -/

declare_syntax_cat koika_sched

syntax ident "|>" koika_sched : koika_sched
syntax "done" : koika_sched

syntax "sched!" koika_sched : term

macro_rules
  | `(sched! done) => `(Scheduler.done)
  | `(sched! $r:ident |> $s) => do
      let nameStr := Syntax.mkStrLit r.getId.toString
      `(Scheduler.cons $nameStr (sched! $s))

end Koika.DSL
