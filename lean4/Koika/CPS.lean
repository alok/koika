/-
  Koika/CPS.lean - Port of coq/CPS.v
  Continuation-passing semantics and weakest precondition calculus

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/CPS.v
-/

import Koika.Types
import Koika.Primitives
import Koika.TypedSyntax
import Koika.Syntax
import Koika.Semantics.Logs
import Koika.Semantics.Interp

namespace Koika.CPS

/-! ## CPS Types

Core types for continuation-passing style interpretation.
-/

/-- Log type for register accesses -/
abbrev Log (reg_t : Type) (R : reg_t → Ty) :=
  SimpleLog (fun r => (R r).denote)

/-! ## Continuation Types -/

/-- Result of interpreting an action -/
structure ActionResult (reg_t : Type) (R : reg_t → Ty)
    (sig : List (String × Ty)) (tau : Ty) where
  log : Log reg_t R
  value : tau.denote
  ctx : TContext sig

/-- Action continuation -/
abbrev ActionCont (reg_t : Type) (R : reg_t → Ty)
    (sig : List (String × Ty)) (tau : Ty) (α : Type) :=
  Option (ActionResult reg_t R sig tau) → α

/-- Rule continuation -/
abbrev RuleCont (reg_t : Type) (R : reg_t → Ty) (α : Type) :=
  Option (Log reg_t R) → α

/-- Scheduler continuation -/
abbrev SchedulerCont (reg_t : Type) (R : reg_t → Ty) (α : Type) :=
  Log reg_t R → α

/-- Cycle continuation: takes final register state -/
abbrev CycleCont (reg_t : Type) (R : reg_t → Ty) (α : Type) :=
  ((r : reg_t) → (R r).denote) → α

/-! ## CPS Interpreter Types -/

/-- Action interpreter in CPS style -/
abbrev ActionInterp (reg_t : Type) (R : reg_t → Ty)
    (sig : List (String × Ty)) (α : Type) :=
  TContext sig → Log reg_t R → α

/-- Generic interpreter -/
abbrev Interp (reg_t : Type) (R : reg_t → Ty) (α : Type) :=
  Log reg_t R → α

/-! ## Helper Functions -/

section Helpers

variable {reg_t : Type} [DecidableEq reg_t]
variable {R : reg_t → Ty}

/-- Read register value based on port and logs -/
def readReg (regState : (r : reg_t) → (R r).denote)
    (schedLog actLog : Log reg_t R) (port : Port) (r : reg_t)
    : (R r).denote :=
  match port with
  | .p0 => regState r
  | .p1 =>
      match (actLog.append schedLog).latestWrite0 r with
      | some v => v
      | none => regState r

end Helpers

/-! ## CPS Interpretation

The CPS interpreter passes a continuation through interpretation,
allowing flexible composition and enabling WP reasoning.
-/

section Interp

variable {reg_t ext_fn_t : Type}
variable [DecidableEq reg_t]
variable {R : reg_t → Ty}
variable {Sigma : ext_fn_t → ExternalSig}

/-- Interpret an action in CPS style -/
partial def interpActionCPS
    (regState : (reg : reg_t) → (R reg).denote)
    (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    {sig : List (String × Ty)} {tau : Ty}
    (schedLog : Log reg_t R)
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    {α : Type} [Inhabited α]
    (k : ActionCont reg_t R sig tau α)
    (gamma : TContext sig)
    (actLog : Log reg_t R)
    : α :=
  match a with
  | .fail _ => k none

  | .var m => k (some ⟨actLog, gamma.get m, gamma⟩)

  | .const v => k (some ⟨actLog, v, gamma⟩)

  | .seq a1 a2 =>
      interpActionCPS regState extFn schedLog a1
        (fun res =>
          match res with
          | some ⟨log', _, gamma'⟩ =>
              interpActionCPS regState extFn schedLog a2 k gamma' log'
          | none => k none) gamma actLog

  | .assign m ex =>
      interpActionCPS regState extFn schedLog ex
        (fun res =>
          match res with
          | some ⟨log', v, gamma'⟩ =>
              k (some ⟨log', (0 : BitVec 0), gamma'.set m v⟩)
          | none => k none) gamma actLog

  | .bind _ ex body =>
      interpActionCPS regState extFn schedLog ex
        (fun res =>
          match res with
          | some ⟨log', val, gamma'⟩ =>
              -- Extend context with bound value (type inferred from val)
              let extGamma : TContext _ := .cons _ val gamma'
              interpActionCPS regState extFn schedLog body
                (fun res' =>
                  match res' with
                  | some ⟨log'', result, .cons _ _ gamma''⟩ =>
                      -- Pop the bound variable from context
                      k (some ⟨log'', result, gamma''⟩)
                  | none => k none) extGamma log'
          | none => k none) gamma actLog

  | .if cond tbranch fbranch =>
      interpActionCPS regState extFn schedLog cond
        (fun res =>
          match res with
          | some ⟨log', v, gamma'⟩ =>
              if v.getLsbD 0 then
                interpActionCPS regState extFn schedLog tbranch k gamma' log'
              else
                interpActionCPS regState extFn schedLog fbranch k gamma' log'
          | none => k none) gamma actLog

  | .read port r =>
      if schedLog.mayRead port r then
        let val := readReg regState schedLog actLog port r
        let log' := actLog.cons r .read port none
        k (some ⟨log', val, gamma⟩)
      else k none

  | .write port r value =>
      interpActionCPS regState extFn schedLog value
        (fun res =>
          match res with
          | some ⟨log', val, gamma'⟩ =>
              if schedLog.mayWrite log' port r then
                let log'' := log'.cons r .write port (some val)
                k (some ⟨log'', (0 : BitVec 0), gamma'⟩)
              else k none
          | none => k none) gamma actLog

  | .unop fn arg =>
      interpActionCPS regState extFn schedLog arg
        (fun res =>
          match res with
          | some ⟨log', v, gamma'⟩ =>
              k (some ⟨log', Apply.fn1 fn v, gamma'⟩)
          | none => k none) gamma actLog

  | .binop fn arg1 arg2 =>
      interpActionCPS regState extFn schedLog arg1
        (fun res =>
          match res with
          | some ⟨log', v1, gamma'⟩ =>
              interpActionCPS regState extFn schedLog arg2
                (fun res =>
                  match res with
                  | some ⟨log'', v2, gamma''⟩ =>
                      k (some ⟨log'', Apply.fn2 fn v1 v2, gamma''⟩)
                  | none => k none) gamma' log'
          | none => k none) gamma actLog

  | .extCall fn arg =>
      interpActionCPS regState extFn schedLog arg
        (fun res =>
          match res with
          | some ⟨log', v, gamma'⟩ =>
              k (some ⟨log', extFn fn v, gamma'⟩)
          | none => k none) gamma actLog

/-- Interpret a rule in CPS style -/
def interpRuleCPS
    (regState : (reg : reg_t) → (R reg).denote)
    (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    (rl : Action reg_t ext_fn_t R Sigma [] (.bits 0))
    {α : Type} [Inhabited α]
    (k : RuleCont reg_t R α)
    (schedLog : Log reg_t R)
    : α :=
  interpActionCPS regState extFn schedLog rl
    (fun res =>
      match res with
      | some ⟨log', _, _⟩ => k (some log')
      | none => k none) TContext.empty SimpleLog.empty

/-- Interpret a scheduler in CPS style -/
partial def interpSchedulerCPS
    {rule_name_t : Type}
    (regState : (reg : reg_t) → (R reg).denote)
    (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    (rules : rule_name_t → Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (s : Scheduler Unit rule_name_t)
    {α : Type} [Inhabited α]
    (k : SchedulerCont reg_t R α)
    (schedLog : Log reg_t R)
    : α :=
  match s with
  | .done => k schedLog
  | .cons rl s' =>
      interpRuleCPS regState extFn (rules rl)
        (fun res =>
          match res with
          | some log' =>
              interpSchedulerCPS regState extFn rules s' k (log'.append schedLog)
          | none =>
              interpSchedulerCPS regState extFn rules s' k schedLog) schedLog
  | .try_ rl s1 s2 =>
      interpRuleCPS regState extFn (rules rl)
        (fun res =>
          match res with
          | some log' =>
              interpSchedulerCPS regState extFn rules s1 k (log'.append schedLog)
          | none =>
              interpSchedulerCPS regState extFn rules s2 k schedLog) schedLog
  | .pos _ s' =>
      interpSchedulerCPS regState extFn rules s' k schedLog

/-- Run scheduler from empty log -/
def runSchedulerCPS
    {rule_name_t : Type}
    (regState : (reg : reg_t) → (R reg).denote)
    (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    (rules : rule_name_t → Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (s : Scheduler Unit rule_name_t)
    {α : Type} [Inhabited α]
    (k : SchedulerCont reg_t R α)
    : α :=
  interpSchedulerCPS regState extFn rules s k SimpleLog.empty

/-- Interpret a complete cycle in CPS style -/
def interpCycleCPS
    {rule_name_t : Type}
    (regState : (reg : reg_t) → (R reg).denote)
    (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    (rules : rule_name_t → Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (s : Scheduler Unit rule_name_t)
    {α : Type} [Inhabited α]
    (k : CycleCont reg_t R α)
    : α :=
  runSchedulerCPS regState extFn rules s fun log =>
    k (commitUpdate regState log)

end Interp

/-! ## Weakest Precondition Calculus

The WP calculus allows reasoning about program behavior.
-/

section WP

variable {reg_t ext_fn_t : Type}
variable [DecidableEq reg_t]
variable {R : reg_t → Ty}
variable {Sigma : ext_fn_t → ExternalSig}

/-- Weakest precondition for an action -/
def wpAction
    (regState : (reg : reg_t) → (R reg).denote)
    (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    {sig : List (String × Ty)} {tau : Ty}
    (schedLog : Log reg_t R)
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    (post : ActionCont reg_t R sig tau Prop)
    (gamma : TContext sig)
    (actLog : Log reg_t R)
    : Prop :=
  interpActionCPS regState extFn schedLog a post gamma actLog

/-- Weakest precondition for a rule -/
def wpRule
    (regState : (reg : reg_t) → (R reg).denote)
    (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    (rl : Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (post : RuleCont reg_t R Prop)
    (schedLog : Log reg_t R)
    : Prop :=
  interpRuleCPS regState extFn rl post schedLog

/-- Weakest precondition for a scheduler -/
def wpScheduler
    {rule_name_t : Type}
    (regState : (reg : reg_t) → (R reg).denote)
    (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    (rules : rule_name_t → Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (s : Scheduler Unit rule_name_t)
    (post : SchedulerCont reg_t R Prop)
    : Prop :=
  runSchedulerCPS regState extFn rules s post

/-- Weakest precondition for a cycle -/
def wpCycle
    {rule_name_t : Type}
    (regState : (reg : reg_t) → (R reg).denote)
    (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    (rules : rule_name_t → Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (s : Scheduler Unit rule_name_t)
    (post : CycleCont reg_t R Prop)
    : Prop :=
  interpCycleCPS regState extFn rules s post

end WP

/-! ## Correctness Theorems

These theorems establish equivalence between CPS and direct-style interpreters.
The proofs are deferred (sorry) but the structure mirrors the Coq original.
-/

section Proofs

variable {reg_t ext_fn_t : Type}
variable [DecidableEq reg_t]
variable {R : reg_t → Ty}
variable {Sigma : ext_fn_t → ExternalSig}
variable (regState : (reg : reg_t) → (R reg).denote)
variable (extFn : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)

/-- CPS action interpretation is equivalent to direct-style interpretation.
    Proof deferred - the structure follows from the interpreter definitions. -/
theorem interpActionCPS_correct
    {sig : List (String × Ty)} {tau : Ty}
    (schedLog : Log reg_t R)
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    {α : Type} [Inhabited α] (k : ActionCont reg_t R sig tau α)
    (gamma : TContext sig)
    (actLog : Log reg_t R)
    : interpActionCPS regState extFn schedLog a k gamma actLog =
      k (Koika.interpAction R Sigma regState extFn schedLog actLog gamma a
         |>.map fun ⟨l, v, g⟩ => ⟨l, v, g⟩) := by
  sorry

/-- CPS rule interpretation is equivalent to direct-style interpretation. -/
theorem interpRuleCPS_correct
    (rl : Action reg_t ext_fn_t R Sigma [] (.bits 0))
    {α : Type} [Inhabited α] (k : RuleCont reg_t R α)
    (schedLog : Log reg_t R)
    : interpRuleCPS regState extFn rl k schedLog =
      k (Koika.interpRule R Sigma regState extFn schedLog rl) := by
  sorry

/-- CPS scheduler interpretation is equivalent to direct-style interpretation. -/
theorem interpSchedulerCPS_correct
    {rule_name_t : Type}
    (rules : rule_name_t → Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (s : Scheduler Unit rule_name_t)
    {α : Type} [Inhabited α] (k : SchedulerCont reg_t R α)
    (schedLog : Log reg_t R)
    : interpSchedulerCPS regState extFn rules s k schedLog =
      k (Koika.interpScheduler R Sigma regState extFn rules schedLog s) := by
  sorry

/-- CPS cycle interpretation is equivalent to direct-style interpretation. -/
theorem interpCycleCPS_correct
    {rule_name_t : Type}
    (rules : rule_name_t → Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (s : Scheduler Unit rule_name_t)
    {α : Type} [Inhabited α] (k : CycleCont reg_t R α)
    : interpCycleCPS regState extFn rules s k =
      k (Koika.interpCycle R Sigma regState extFn rules s) := by
  sorry

/-! ### WP Correctness Lemmas -/

/-- WP for actions is correct with respect to direct-style interpretation. -/
theorem wp_action_correct
    {sig : List (String × Ty)} {tau : Ty}
    (gamma : TContext sig)
    (schedLog actLog : Log reg_t R)
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    (post : ActionCont reg_t R sig tau Prop)
    : wpAction regState extFn schedLog a post gamma actLog ↔
      post (Koika.interpAction R Sigma regState extFn schedLog actLog gamma a
            |>.map fun ⟨l, v, g⟩ => ⟨l, v, g⟩) := by
  unfold wpAction
  rw [interpActionCPS_correct]

/-- WP for rules is correct with respect to direct-style interpretation. -/
theorem wp_rule_correct
    (schedLog : Log reg_t R)
    (rl : Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (post : RuleCont reg_t R Prop)
    : wpRule regState extFn rl post schedLog ↔
      post (Koika.interpRule R Sigma regState extFn schedLog rl) := by
  unfold wpRule
  rw [interpRuleCPS_correct]

/-- WP for schedulers is correct with respect to direct-style interpretation. -/
theorem wp_scheduler_correct
    {rule_name_t : Type}
    (rules : rule_name_t → Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (s : Scheduler Unit rule_name_t)
    (post : SchedulerCont reg_t R Prop)
    : wpScheduler regState extFn rules s post ↔
      post (Koika.interpScheduler R Sigma regState extFn rules .empty s) := by
  unfold wpScheduler runSchedulerCPS
  rw [interpSchedulerCPS_correct]

/-- WP for cycles is correct with respect to direct-style interpretation. -/
theorem wp_cycle_correct
    {rule_name_t : Type}
    (rules : rule_name_t → Action reg_t ext_fn_t R Sigma [] (.bits 0))
    (s : Scheduler Unit rule_name_t)
    (post : CycleCont reg_t R Prop)
    : wpCycle regState extFn rules s post ↔
      post (Koika.interpCycle R Sigma regState extFn rules s) := by
  unfold wpCycle
  rw [interpCycleCPS_correct]

end Proofs

end Koika.CPS
