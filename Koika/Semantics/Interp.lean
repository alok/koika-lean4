/-
  Koika/Semantics/Interp.lean - Port of coq/TypedSemantics.v
  Interpreter for typed Kôika programs
-/

import Koika.Types
import Koika.Primitives
import Koika.Syntax
import Koika.TypedSyntax
import Koika.Semantics.Logs

namespace Koika

/-! ## Interpreter for Typed Actions -/

section Interp

variable {reg_t ext_fn_t : Type} [DecidableEq reg_t]
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Register environment: a value for each register -/
abbrev RegEnv := (r : reg_t) → (R r).denote

/-- External function implementations -/
abbrev ExtEnv := (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote

/-- Log type specialized to register denotations -/
abbrev InterpLog := SimpleLog (fun r => (R r).denote)

/-- Read a register value -/
def readReg (env : RegEnv R) (schedLog actLog : InterpLog R) (port : Port) (r : reg_t)
    : (R r).denote :=
  match port with
  | .p0 => env r
  | .p1 =>
      match (actLog.append schedLog).latestWrite0 r with
      | some v => v
      | none => env r

/-- Interpret a typed action -/
partial def interpAction
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (schedLog : InterpLog R)
    (actLog : InterpLog R)
    (ctx : TContext sig)
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    : Option (InterpLog R × tau.denote × TContext sig) :=
  match a with
  | .fail _ => none
  | .var m => some (actLog, ctx.get m, ctx)
  | .const v => some (actLog, v, ctx)
  | .assign m e =>
      match interpAction env extEnv schedLog actLog ctx e with
      | none => none
      | some (log', v, ctx') =>
          some (log', (0 : BitVec 0), ctx'.set m v)
  | .seq a b =>
      match interpAction env extEnv schedLog actLog ctx a with
      | none => none
      | some (log', _, ctx') =>
          interpAction env extEnv schedLog log' ctx' b
  | .bind v e body =>
      match interpAction env extEnv schedLog actLog ctx e with
      | none => none
      | some (log', val, ctx') =>
          match interpAction env extEnv schedLog log' (.cons _ val ctx') body with
          | none => none
          | some (log'', result, .cons _ _ ctx'') =>
              some (log'', result, ctx'')
  | .if cond tbranch fbranch =>
      match interpAction env extEnv schedLog actLog ctx cond with
      | none => none
      | some (log', condVal, ctx') =>
          if condVal.getLsbD 0 then
            interpAction env extEnv schedLog log' ctx' tbranch
          else
            interpAction env extEnv schedLog log' ctx' fbranch
  | .read port r =>
      if schedLog.mayRead port r then
        let val := readReg R env schedLog actLog port r
        let log' := actLog.cons r .read port none
        some (log', val, ctx)
      else none
  | .write port r valAction =>
      match interpAction env extEnv schedLog actLog ctx valAction with
      | none => none
      | some (log', val, ctx') =>
          if schedLog.mayWrite log' port r then
            let log'' := log'.cons r .write port (some val)
            some (log'', (0 : BitVec 0), ctx')
          else none
  | .unop fn arg =>
      match interpAction env extEnv schedLog actLog ctx arg with
      | none => none
      | some (log', argVal, ctx') =>
          -- Apply the primitive operation
          some (log', sorry, ctx')  -- TODO: implement primitive semantics
  | .binop fn arg1 arg2 =>
      match interpAction env extEnv schedLog actLog ctx arg1 with
      | none => none
      | some (log', arg1Val, ctx') =>
          match interpAction env extEnv schedLog log' ctx' arg2 with
          | none => none
          | some (log'', arg2Val, ctx'') =>
              -- Apply the primitive operation
              some (log'', sorry, ctx'')  -- TODO: implement primitive semantics
  | .extCall fn arg =>
      match interpAction env extEnv schedLog actLog ctx arg with
      | none => none
      | some (log', argVal, ctx') =>
          some (log', extEnv fn argVal, ctx')

/-- Interpret a rule (closed action returning unit) -/
def interpRule
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (schedLog : InterpLog R)
    (rl : Rule reg_t ext_fn_t R Sigma)
    : Option (InterpLog R) :=
  match interpAction R Sigma env extEnv schedLog .empty .empty rl with
  | some (log, _, _) => some log
  | none => none

end Interp

/-! ## Scheduler Interpretation -/

section Scheduler

variable {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Interpret a scheduler -/
partial def interpScheduler
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (schedLog : InterpLog R)
    (s : Scheduler Unit rule_name_t)
    : InterpLog R :=
  match s with
  | .done => schedLog
  | .cons ruleName rest =>
      match interpRule R Sigma env extEnv schedLog (rules ruleName) with
      | some ruleLog => interpScheduler env extEnv rules (ruleLog.append schedLog) rest
      | none => interpScheduler env extEnv rules schedLog rest  -- Rule failed, continue
  | .try_ ruleName s1 s2 =>
      match interpRule R Sigma env extEnv schedLog (rules ruleName) with
      | some ruleLog => interpScheduler env extEnv rules (ruleLog.append schedLog) s1
      | none => interpScheduler env extEnv rules schedLog s2
  | .pos _ s => interpScheduler env extEnv rules schedLog s

/-- Run a complete cycle: interpret scheduler and commit updates -/
def interpCycle
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (s : Scheduler Unit rule_name_t)
    : RegEnv R :=
  let log := interpScheduler R Sigma env extEnv rules .empty s
  commitUpdate env log

end Scheduler

end Koika
