/-
  Koika/Semantics/CompactInterp.lean - Port of coq/CompactSemantics.v
  Interpreter for typed Kôika programs using compact logs

  Original Coq source: coq/CompactSemantics.v
  This provides an alternative interpreter that uses CompactLog instead of SimpleLog
  for more efficient log operations.
-/

import Koika.Types
import Koika.Primitives
import Koika.Syntax
import Koika.TypedSyntax
import Koika.Semantics.CompactLogs
import Koika.Semantics.Interp

namespace Koika

/-! ## Compact Log Interpreter

This interpreter is similar to the standard interpreter but uses CompactLog
instead of SimpleLog for more efficient tracking of read/write operations.
-/

section CompactInterp

variable {reg_t ext_fn_t : Type} [DecidableEq reg_t]
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

-- Use RegEnv and ExtEnv from Koika.Semantics.Interp

/-- Compact log type specialized to register denotations -/
abbrev CompactInterpLog := CompactLog (fun r => (R r).denote)

/-- Update a single register's log entry -/
def updateLog (log : CompactInterpLog R) (idx : reg_t)
    (f : CompactLogEntry ((R idx).denote) → CompactLogEntry ((R idx).denote))
    : CompactInterpLog R :=
  fun r => if h : r = idx then h ▸ f (h ▸ log r) else log r

/-- Helper for interp_args: interpret a context of action arguments -/
partial def interpArgs
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (schedLog : CompactInterpLog R)
    (actLog : CompactInterpLog R)
    (ctx : TContext sig)
    (args : TContext argSig)
    : Option (CompactInterpLog R × TContext argSig × TContext sig) :=
  match args with
  | .empty => some (actLog, .empty, ctx)
  | .cons tau v ctx_rest =>
      -- Process the rest first (right to left evaluation)
      match interpArgs env extEnv schedLog actLog ctx ctx_rest with
      | none => none
      | some (log', results, ctx') =>
          -- Then process the current argument if it's an action
          -- Note: In the Coq version, args are actions, but in our typed representation
          -- they're already values in the context. This is a simplification.
          some (log', .cons tau v results, ctx')

/-- Interpret a typed action using compact logs -/
partial def compactInterpAction
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (schedLog : CompactInterpLog R)
    (actLog : CompactInterpLog R)
    (ctx : TContext sig)
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    : Option (CompactInterpLog R × tau.denote × TContext sig) :=
  match a with
  | .fail _ => none

  | .var m => some (actLog, ctx.get m, ctx)

  | .const v => some (actLog, v, ctx)

  | .seq a1 a2 =>
      match compactInterpAction env extEnv schedLog actLog ctx a1 with
      | none => none
      | some (log', _, ctx') =>
          compactInterpAction env extEnv schedLog log' ctx' a2

  | .assign m e =>
      match compactInterpAction env extEnv schedLog actLog ctx e with
      | none => none
      | some (log', v, ctx') =>
          some (log', (0 : BitVec 0), ctx'.set m v)

  | .bind _v e body =>
      match compactInterpAction env extEnv schedLog actLog ctx e with
      | none => none
      | some (log', val, ctx') =>
          match compactInterpAction env extEnv schedLog log' (.cons _ val ctx') body with
          | none => none
          | some (log'', result, .cons _ _ ctx'') =>
              some (log'', result, ctx'')

  | .if cond tbranch fbranch =>
      match compactInterpAction env extEnv schedLog actLog ctx cond with
      | none => none
      | some (log', condVal, ctx') =>
          if condVal.getLsbD 0 then
            compactInterpAction env extEnv schedLog log' ctx' tbranch
          else
            compactInterpAction env extEnv schedLog log' ctx' fbranch

  | .read .p0 idx =>
      if CompactLog.mayRead0 schedLog idx then
        let log' := updateLog R actLog idx fun rl =>
          { lread0 := true
            lread1 := rl.lread1
            lwrite0 := rl.lwrite0
            lwrite1 := rl.lwrite1 }
        some (log', env idx, ctx)
      else none

  | .read .p1 idx =>
      if CompactLog.mayRead1 schedLog idx then
        let log' := updateLog R actLog idx fun rl =>
          { lread0 := rl.lread0
            lread1 := true
            lwrite0 := rl.lwrite0
            lwrite1 := rl.lwrite1 }
        let val := match (actLog idx).lwrite0, (schedLog idx).lwrite0 with
          | some v, _ => v
          | _, some v => v
          | _, _ => env idx
        some (log', val, ctx)
      else none

  | .write .p0 idx valAction =>
      match compactInterpAction env extEnv schedLog actLog ctx valAction with
      | none => none
      | some (log', val, ctx') =>
          if CompactLog.mayWrite0 schedLog log' idx then
            let log'' := updateLog R log' idx fun rl =>
              { lread0 := rl.lread0
                lread1 := rl.lread1
                lwrite0 := some val
                lwrite1 := rl.lwrite1 }
            some (log'', (0 : BitVec 0), ctx')
          else none

  | .write .p1 idx valAction =>
      match compactInterpAction env extEnv schedLog actLog ctx valAction with
      | none => none
      | some (log', val, ctx') =>
          if CompactLog.mayWrite1 schedLog log' idx then
            let log'' := updateLog R log' idx fun rl =>
              { lread0 := rl.lread0
                lread1 := rl.lread1
                lwrite0 := rl.lwrite0
                lwrite1 := some val }
            some (log'', (0 : BitVec 0), ctx')
          else none

  | .unop fn arg =>
      match compactInterpAction env extEnv schedLog actLog ctx arg with
      | none => none
      | some (log', argVal, ctx') =>
          some (log', Apply.fn1 fn argVal, ctx')

  | .binop fn arg1 arg2 =>
      match compactInterpAction env extEnv schedLog actLog ctx arg1 with
      | none => none
      | some (log', arg1Val, ctx') =>
          match compactInterpAction env extEnv schedLog log' ctx' arg2 with
          | none => none
          | some (log'', arg2Val, ctx'') =>
              some (log'', Apply.fn2 fn arg1Val arg2Val, ctx'')

  | .extCall fn arg =>
      match compactInterpAction env extEnv schedLog actLog ctx arg with
      | none => none
      | some (log', argVal, ctx') =>
          some (log', extEnv fn argVal, ctx')

/-- Interpret a rule (closed action returning unit) using compact logs -/
def compactInterpRule
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (schedLog : CompactInterpLog R)
    (rl : Rule reg_t ext_fn_t R Sigma)
    : Option (CompactInterpLog R) :=
  match compactInterpAction R Sigma env extEnv schedLog CompactLog.empty .empty rl with
  | some (log, _, _) => some log
  | none => none

end CompactInterp

/-! ## Scheduler Interpretation with Compact Logs -/

section CompactScheduler

variable {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Interpret a scheduler using compact logs -/
partial def interpSchedulerCompact
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (schedLog : CompactInterpLog R)
    (s : Scheduler Unit rule_name_t)
    : CompactInterpLog R :=
  let interpTry (ruleName : rule_name_t) (s1 s2 : Scheduler Unit rule_name_t) :=
    match compactInterpRule R Sigma env extEnv schedLog (rules ruleName) with
    | some ruleLog =>
        let newSchedLog := CompactLog.append ruleLog schedLog
        interpSchedulerCompact env extEnv rules newSchedLog s1
    | none =>
        interpSchedulerCompact env extEnv rules schedLog s2
  match s with
  | .done => schedLog
  | .cons ruleName rest => interpTry ruleName rest rest
  | .try_ ruleName s1 s2 => interpTry ruleName s1 s2
  | .pos _ s => interpSchedulerCompact env extEnv rules schedLog s

/-- Run a complete cycle using compact logs: interpret scheduler and commit updates -/
def interpCycleCompact
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (s : Scheduler Unit rule_name_t)
    : RegEnv R :=
  let log := interpSchedulerCompact R Sigma env extEnv rules CompactLog.empty s
  CompactLog.commitUpdate env log

end CompactScheduler

end Koika
