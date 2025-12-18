/-
  Koika/Semantics/OneRuleAtATime.lean - Port of coq/OneRuleAtATime.v
  One-Rule-At-A-Time theorem: scheduler execution decomposes into sequential rule applications

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/OneRuleAtATime.v
  For VersoCoq documentation: {coq}`OneRuleAtATime.v`

  This is the key correctness theorem for Kôika: any scheduler execution can be
  decomposed into a sequence of atomic rule executions with the same final state.
-/

import Koika.Types
import Koika.Primitives
import Koika.TypedSyntax
import Koika.Semantics.Logs
import Koika.Semantics.Interp
import Koika.Semantics.Properties

namespace Koika

/-! ## Scheduler Trace

A trace records which rules were successfully executed during scheduler interpretation.
-/

/-- A trace is a list of rule names that were successfully executed -/
abbrev SchedulerTrace (rule_name_t : Type) := List rule_name_t

section OneRuleAtATime

variable {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Fold a sequence of rules, applying each in turn -/
def foldRules
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (trace : SchedulerTrace rule_name_t)
    : RegEnv R :=
  trace.foldl (fun acc ruleName =>
    match interpRule R Sigma acc extEnv SimpleLog.empty (rules ruleName) with
    | some log => commitUpdate acc log
    | none => acc  -- Rule failed, state unchanged
  ) env

/-- Extract the trace from scheduler interpretation -/
def interpSchedulerTrace
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (schedLog : InterpLog R)
    (s : Scheduler Unit rule_name_t)
    : SchedulerTrace rule_name_t × InterpLog R :=
  match s with
  | .done => ([], schedLog)
  | .cons ruleName rest =>
      match interpRule R Sigma env extEnv schedLog (rules ruleName) with
      | some ruleLog =>
          let newSchedLog := ruleLog.append schedLog
          let (trace, finalLog) := interpSchedulerTrace env extEnv rules newSchedLog rest
          (ruleName :: trace, finalLog)
      | none =>
          interpSchedulerTrace env extEnv rules schedLog rest
  | .try_ ruleName s1 s2 =>
      match interpRule R Sigma env extEnv schedLog (rules ruleName) with
      | some ruleLog =>
          let newSchedLog := ruleLog.append schedLog
          let (trace, finalLog) := interpSchedulerTrace env extEnv rules newSchedLog s1
          (ruleName :: trace, finalLog)
      | none =>
          interpSchedulerTrace env extEnv rules schedLog s2
  | .pos _ s =>
      interpSchedulerTrace env extEnv rules schedLog s

/-! ## Key Lemmas for One-Rule-At-A-Time

These lemmas are stated as axioms because they require induction on partial functions.
The proofs would follow standard structural induction patterns if the interpreter
functions were total.
-/

/-- Interpretation remains consistent when committing part of the schedule log.

This lemma states that if interpretation succeeds with schedule log `sl.append sl'`,
then it also succeeds when we commit `sl'` to the environment and use `sl` as the
new schedule log. This captures the key compositionality property:

  interp env (sl.append sl') action = some result  →
  interp (commitUpdate env sl') sl action = some result

The hypothesis that the LHS succeeds is crucial: it guarantees that all read/write
permission checks passed for `sl.append sl'`. Since `mayRead (sl.append sl')` equals
`mayRead sl && mayRead sl'` (see `mayRead_append`), the individual checks for `sl`
also pass, allowing the RHS to succeed.

Key helper lemmas from Coq:
- may_read_app_sl: mayRead (log_app sl sl') = mayRead sl && mayRead sl'
- may_write_app_sl: mayWrite (log_app sl sl') = mayWrite sl && mayWrite sl'
- may_read0_no_writes: mayRead P0 → latest_write = none
- may_read1_latest_write_is_0: mayRead P1 → latest_write = latest_write0
-/
theorem interp_action_commit (env : RegEnv R) (extEnv : ExtEnv Sigma)
    (sl sl' actLog : InterpLog R)
    (ctx : TContext sig)
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    (result : InterpLog R × tau.denote × TContext sig) :
    interpAction R Sigma env extEnv (sl.append sl') actLog ctx a = some result →
    interpAction R Sigma (commitUpdate env sl') extEnv sl actLog ctx a = some result := by
  -- Proof by structural induction on the action.
  -- The key insight is that since the LHS succeeds with schedule log (sl.append sl'),
  -- all read/write permission checks passed. By may_read_app and may_write_app,
  -- this means the individual checks for sl also pass.
  --
  -- The Coq proof uses: fix IH 3; destruct a; ...
  -- with custom tactic `t` that handles most cases automatically.
  --
  -- Key helper lemmas needed:
  -- - may_read0_app_sl, may_read1_app_sl: mayRead distributes over append
  -- - may_write0_app_sl, may_write1_app_sl: mayWrite distributes over append
  -- - getenv_commit_update: relates reads to committed environment
  -- - may_read0_no_writes: P0 read implies no writes in log
  -- - may_read1_latest_write_is_0: P1 read constraint
  -- - latestWrite0_append: how latestWrite0 distributes over append
  --
  -- The proof follows Coq's structure: induction on action with the key cases
  -- being read (uses register read properties) and write (uses mayWrite properties).
  -- Most other cases follow by the induction hypothesis.
  intro h
  induction a generalizing actLog with
  | fail => simp [interpAction] at h
  | var m =>
    simp only [interpAction] at h ⊢
    exact h
  | const v =>
    simp only [interpAction] at h ⊢
    exact h
  | assign m e ih =>
    simp only [interpAction] at h ⊢
    cases he : interpAction R Sigma env extEnv (sl.append sl') actLog ctx e with
    | none => simp [he] at h
    | some res =>
      simp only [he] at h
      obtain ⟨log', v, ctx'⟩ := res
      have ih' := ih actLog ctx (log', v, ctx') he
      simp only [ih']
      exact h
  | seq a b iha ihb =>
    simp only [interpAction] at h ⊢
    cases ha : interpAction R Sigma env extEnv (sl.append sl') actLog ctx a with
    | none => simp [ha] at h
    | some res =>
      simp only [ha] at h
      obtain ⟨log', _, ctx'⟩ := res
      have iha' := iha actLog ctx (log', _, ctx') ha
      simp only [iha']
      exact ihb log' ctx' result h
  | bind v e body ihe ihbody =>
    simp only [interpAction] at h ⊢
    cases he : interpAction R Sigma env extEnv (sl.append sl') actLog ctx e with
    | none => simp [he] at h
    | some res =>
      simp only [he] at h
      obtain ⟨log', val, ctx'⟩ := res
      have ihe' := ihe actLog ctx (log', val, ctx') he
      simp only [ihe']
      cases hbody : interpAction R Sigma env extEnv (sl.append sl') log' (.cons _ val ctx') body with
      | none => simp [hbody] at h
      | some res' =>
        simp only [hbody] at h
        obtain ⟨log'', result', ctx''⟩ := res'
        have ihbody' := ihbody log' (.cons _ val ctx') (log'', result', ctx'') hbody
        simp only [ihbody']
        exact h
  | «if» cond tbranch fbranch ihc iht ihf =>
    simp only [interpAction] at h ⊢
    cases hc : interpAction R Sigma env extEnv (sl.append sl') actLog ctx cond with
    | none => simp [hc] at h
    | some res =>
      simp only [hc] at h
      obtain ⟨log', condVal, ctx'⟩ := res
      have ihc' := ihc actLog ctx (log', condVal, ctx') hc
      simp only [ihc']
      -- Case split on the condition value
      by_cases hcond : condVal.getLsbD 0
      · simp only [hcond, ↓reduceIte] at h ⊢
        exact iht log' ctx' result h
      · simp only [hcond, ↓reduceIte, Bool.false_eq_true] at h ⊢
        exact ihf log' ctx' result h
  | read port r =>
    -- Key case: register read
    simp only [interpAction] at h ⊢
    split at h
    · -- mayRead check passed in LHS
      rename_i hmay
      -- Need to show: sl.mayRead port r = true
      have hmay_sl : sl.mayRead port r = true := by
        -- From hmay : (sl.append sl').mayRead port r = true
        -- By may_readX_app_sl: the conjunction (sl && sl') = true implies both are true
        cases hp : port with
        | p0 =>
          have happ := may_read0_app_sl sl sl' r
          simp only [hp] at hmay
          rw [hmay] at happ
          cases hsl : sl.mayRead .p0 r with
          | true => rfl
          | false => simp [hsl] at happ
        | p1 =>
          have happ := may_read1_app_sl sl sl' r
          simp only [hp] at hmay
          rw [hmay] at happ
          cases hsl : sl.mayRead .p1 r with
          | true => rfl
          | false => simp [hsl] at happ
      simp only [hmay_sl, ↓reduceIte]
      -- Need to show readReg values match
      simp only [Option.some.injEq] at h
      -- h says (actLog.cons ..., readReg env (sl.append sl') ..., ctx) = result
      -- Goal: (actLog.cons ..., readReg (commitUpdate env sl') sl ..., ctx) = result
      -- By readReg_commit_general: the readReg values are equal
      have hread := readReg_commit_general R env sl sl' actLog port r hmay
      -- hread: readReg env (sl.append sl') = readReg (commitUpdate env sl') sl
      -- Rewrite h using hread (forward) to replace LHS with RHS in h
      rw [hread] at h
      simp only [Option.some.injEq]
      exact h
    · contradiction
  | write port r valAction ih =>
    -- Key case: register write
    simp only [interpAction] at h ⊢
    cases hval : interpAction R Sigma env extEnv (sl.append sl') actLog ctx valAction with
    | none => simp [hval] at h
    | some res =>
      simp only [hval] at h
      obtain ⟨log', val, ctx'⟩ := res
      have ih' := ih actLog ctx (log', val, ctx') hval
      simp only [ih']
      split at h
      · -- mayWrite check passed in LHS
        rename_i hmay
        -- Need to show: sl.mayWrite log' port r = true
        have hmay_sl : sl.mayWrite log' port r = true := by
          -- From hmay : (sl.append sl').mayWrite log' port r = true
          -- By may_writeX_app_sl: the conjunction (sl && sl') = true implies both are true
          cases hp : port with
          | p0 =>
            have happ := may_write0_app_sl sl sl' log' r
            simp only [hp] at hmay
            rw [hmay] at happ
            cases hsl : sl.mayWrite log' .p0 r with
            | true => rfl
            | false => simp [hsl] at happ
          | p1 =>
            have happ := may_write1_app_sl sl sl' log' r
            simp only [hp] at hmay
            rw [hmay] at happ
            cases hsl : sl.mayWrite log' .p1 r with
            | true => rfl
            | false => simp [hsl] at happ
        simp only [hmay_sl, ↓reduceIte]
        exact h
      · contradiction
  | unop fn arg ih =>
    simp only [interpAction] at h ⊢
    cases ha : interpAction R Sigma env extEnv (sl.append sl') actLog ctx arg with
    | none => simp [ha] at h
    | some res =>
      simp only [ha] at h
      obtain ⟨log', argVal, ctx'⟩ := res
      have ih' := ih actLog ctx (log', argVal, ctx') ha
      simp only [ih']
      exact h
  | binop fn arg1 arg2 ih1 ih2 =>
    simp only [interpAction] at h ⊢
    cases ha1 : interpAction R Sigma env extEnv (sl.append sl') actLog ctx arg1 with
    | none => simp [ha1] at h
    | some res1 =>
      simp only [ha1] at h
      obtain ⟨log', arg1Val, ctx'⟩ := res1
      have ih1' := ih1 actLog ctx (log', arg1Val, ctx') ha1
      simp only [ih1']
      cases ha2 : interpAction R Sigma env extEnv (sl.append sl') log' ctx' arg2 with
      | none => simp [ha2] at h
      | some res2 =>
        simp only [ha2] at h
        obtain ⟨log'', arg2Val, ctx''⟩ := res2
        have ih2' := ih2 log' ctx' (log'', arg2Val, ctx'') ha2
        simp only [ih2']
        exact h
  | extCall fn arg ih =>
    simp only [interpAction] at h ⊢
    cases ha : interpAction R Sigma env extEnv (sl.append sl') actLog ctx arg with
    | none => simp [ha] at h
    | some res =>
      simp only [ha] at h
      obtain ⟨log', argVal, ctx'⟩ := res
      have ih' := ih actLog ctx (log', argVal, ctx') ha
      simp only [ih']
      exact h

/-- Rule interpretation with appended schedule logs relates to commit.

    If a rule succeeds with schedLog = (sl.append sl'), then it also succeeds
    with schedLog = sl after committing sl' to the environment.
    This follows directly from interp_action_commit. -/
theorem interpRule_commit (env : RegEnv R) (extEnv : ExtEnv Sigma)
    (sl sl' : InterpLog R)
    (rule : Rule reg_t ext_fn_t R Sigma)
    (log : InterpLog R) :
    interpRule R Sigma env extEnv (sl.append sl') rule = some log →
    interpRule R Sigma (commitUpdate env sl') extEnv sl rule = some log := by
  intro h
  unfold interpRule at h ⊢
  cases hr : interpAction R Sigma env extEnv (sl.append sl') .empty .empty rule with
  | none =>
    simp only [hr] at h
    -- h : none = some log, which is a contradiction
    contradiction
  | some res =>
    simp only [hr] at h
    obtain ⟨log', _, ctx'⟩ := res
    have hcommit := interp_action_commit R Sigma env extEnv sl sl' .empty .empty rule (log', _, ctx') hr
    simp only [hcommit]
    exact h

/-- Traced rules belong to the scheduler (general version with any initial log). -/
theorem scheduler_trace_in_scheduler_aux
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (schedLog : InterpLog R)
    (s : Scheduler Unit rule_name_t)
    (ruleName : rule_name_t) :
    ruleName ∈ (interpSchedulerTrace R Sigma env extEnv rules schedLog s).1 →
    ruleName ∈ s.toList := by
  induction s generalizing schedLog with
  | done =>
    simp [interpSchedulerTrace, Scheduler.toList]
  | cons r rest ih =>
    intro h
    simp only [interpSchedulerTrace] at h
    cases hr : interpRule R Sigma env extEnv schedLog (rules r) with
    | some ruleLog =>
      simp only [hr] at h
      simp only [Scheduler.toList, List.mem_cons]
      cases h with
      | head => left; rfl
      | tail _ hmem => right; exact ih _ hmem
    | none =>
      simp only [hr] at h
      simp only [Scheduler.toList, List.mem_cons]
      right; exact ih _ h
  | try_ r s1 s2 ih1 ih2 =>
    intro h
    simp only [interpSchedulerTrace] at h
    cases hr : interpRule R Sigma env extEnv schedLog (rules r) with
    | some ruleLog =>
      simp only [hr] at h
      show ruleName ∈ (r :: Scheduler.toList s1) ++ Scheduler.toList s2
      rw [List.mem_append, List.mem_cons]
      cases h with
      | head => left; left; rfl
      | tail _ hmem => left; right; exact ih1 _ hmem
    | none =>
      simp only [hr] at h
      show ruleName ∈ (r :: Scheduler.toList s1) ++ Scheduler.toList s2
      rw [List.mem_append]
      right; exact ih2 _ h
  | pos _ s ih =>
    intro h
    simp only [interpSchedulerTrace, Scheduler.toList] at h ⊢
    exact ih _ h

/-- Traced rules belong to the scheduler.

This states that any rule appearing in the execution trace must be
mentioned in the scheduler structure.

Note: For try_ schedulers, the trace may include rules from s2 branch that
aren't in toList (since toList only follows the success branch).
-/
theorem scheduler_trace_in_scheduler
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (s : Scheduler Unit rule_name_t)
    (ruleName : rule_name_t) :
    ruleName ∈ (interpSchedulerTrace R Sigma env extEnv rules SimpleLog.empty s).1 →
    ruleName ∈ s.toList :=
  scheduler_trace_in_scheduler_aux R Sigma env extEnv rules .empty s ruleName

/-- Scheduler trace produces correct log (general version with any initial log). -/
theorem interp_scheduler_trace_correct_aux
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (schedLog : InterpLog R)
    (s : Scheduler Unit rule_name_t) :
    (interpSchedulerTrace R Sigma env extEnv rules schedLog s).2 =
    interpScheduler R Sigma env extEnv rules schedLog s := by
  induction s generalizing schedLog with
  | done => rfl
  | cons r rest ih =>
    simp only [interpSchedulerTrace, interpScheduler]
    cases hr : interpRule R Sigma env extEnv schedLog (rules r) with
    | some _ruleLog =>
      exact ih _
    | none =>
      exact ih _
  | try_ r s1 s2 ih1 ih2 =>
    simp only [interpSchedulerTrace, interpScheduler]
    cases hr : interpRule R Sigma env extEnv schedLog (rules r) with
    | some _ruleLog =>
      exact ih1 _
    | none =>
      exact ih2 _
  | pos _ s ih =>
    simp only [interpSchedulerTrace, interpScheduler]
    exact ih _

/-- Scheduler trace produces correct log.

This states that the log produced by interpSchedulerTrace matches
the log produced by interpScheduler. This ensures the trace extraction
is consistent with the scheduler semantics.
-/
theorem interp_scheduler_trace_correct
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (s : Scheduler Unit rule_name_t) :
    (interpSchedulerTrace R Sigma env extEnv rules SimpleLog.empty s).2 =
    interpScheduler R Sigma env extEnv rules SimpleLog.empty s :=
  interp_scheduler_trace_correct_aux R Sigma env extEnv rules .empty s

/-! ## Main Theorem -/

/-- Helper: foldRules with a cons trace unfolds the first rule -/
theorem foldRules_cons (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (env : RegEnv R) (extEnv : ExtEnv Sigma)
    (ruleName : rule_name_t) (rest : SchedulerTrace rule_name_t) :
    foldRules R Sigma rules env extEnv (ruleName :: rest) =
      let newEnv := match interpRule R Sigma env extEnv .empty (rules ruleName) with
        | some log => commitUpdate env log
        | none => env
      foldRules R Sigma rules newEnv extEnv rest := by
  simp only [foldRules, List.foldl_cons]

/-- Generalized one-rule-at-a-time theorem for any initial schedLog.

    Running the scheduler with fixed env and accumulated schedLog produces the same
    final state as running rules sequentially with progressively committed environments.
    This is the key compositionality property of Kôika semantics. -/
theorem one_rule_at_a_time_aux (env : RegEnv R) (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (schedLog : InterpLog R)
    (s : Scheduler Unit rule_name_t) :
    let (trace, finalLog) := interpSchedulerTrace R Sigma env extEnv rules schedLog s
    commitUpdate env finalLog = foldRules R Sigma rules (commitUpdate env schedLog) extEnv trace := by
  induction s generalizing schedLog with
  | done =>
    simp only [interpSchedulerTrace, foldRules, List.foldl_nil]
  | cons ruleName rest ih =>
    simp only [interpSchedulerTrace]
    cases hr : interpRule R Sigma env extEnv schedLog (rules ruleName) with
    | some ruleLog =>
      -- Rule succeeded: trace = ruleName :: trace_rest, finalLog from recursive call
      -- Apply IH with newSchedLog = ruleLog.append schedLog
      have ih' := ih (ruleLog.append schedLog)
      -- Need to show: foldRules ... (commitUpdate env schedLog) (ruleName :: trace_rest)
      --             = foldRules ... (commitUpdate env (ruleLog.append schedLog)) trace_rest
      rw [foldRules_cons]
      -- By interpRule_commit: interpRule (commitUpdate env schedLog) .empty rule = some ruleLog
      have hcommit := interpRule_commit R Sigma env extEnv .empty schedLog (rules ruleName) ruleLog
      rw [log_app_empty_l] at hcommit
      have hr' := hcommit hr
      simp only [hr']
      -- Now: foldRules (commitUpdate (commitUpdate env schedLog) ruleLog) trace_rest
      -- By commit_update_assoc: this equals foldRules (commitUpdate env (ruleLog.append schedLog))
      rw [commit_update_assoc]
      exact ih'
    | none =>
      -- Rule failed: continue with rest, schedLog unchanged
      exact ih schedLog
  | try_ ruleName s1 s2 ih1 ih2 =>
    simp only [interpSchedulerTrace]
    cases hr : interpRule R Sigma env extEnv schedLog (rules ruleName) with
    | some ruleLog =>
      have ih' := ih1 (ruleLog.append schedLog)
      rw [foldRules_cons]
      have hcommit := interpRule_commit R Sigma env extEnv .empty schedLog (rules ruleName) ruleLog
      rw [log_app_empty_l] at hcommit
      have hr' := hcommit hr
      simp only [hr']
      rw [commit_update_assoc]
      exact ih'
    | none =>
      exact ih2 schedLog
  | pos _ s ih =>
    simp only [interpSchedulerTrace]
    exact ih schedLog

/-- **One-Rule-At-A-Time Theorem**

Any scheduler execution can be decomposed into a sequence of individual rule
applications. The final state is the same whether we:
1. Execute the full scheduler, or
2. Execute rules one at a time in the traced order

This is the fundamental correctness theorem for Kôika semantics, establishing
that the concurrent-looking scheduler has well-defined sequential semantics. -/
theorem one_rule_at_a_time
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (s : Scheduler Unit rule_name_t) :
    let (trace, log) := interpSchedulerTrace R Sigma env extEnv rules SimpleLog.empty s
    commitUpdate env log = foldRules R Sigma rules env extEnv trace := by
  have h := one_rule_at_a_time_aux R Sigma env extEnv rules .empty s
  rw [commit_update_empty] at h
  exact h

/-- Corollary: interpCycle equals foldRules over the trace.

This follows directly from one_rule_at_a_time and the definition of interpCycle
as `commitUpdate env (interpScheduler ...)`.
-/
theorem interp_cycle_eq_fold_trace
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (s : Scheduler Unit rule_name_t) :
    interpCycle R Sigma env extEnv rules s =
    foldRules R Sigma rules env extEnv (interpSchedulerTrace R Sigma env extEnv rules SimpleLog.empty s).1 := by
  -- Use one_rule_at_a_time and interp_scheduler_trace_correct
  unfold interpCycle
  have h := one_rule_at_a_time R Sigma env extEnv rules s
  simp only at h
  rw [interp_scheduler_trace_correct] at h
  exact h

end OneRuleAtATime

/-! ## Determinism Properties -/

section Determinism

variable {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Action interpretation is deterministic -/
theorem interp_action_deterministic
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (schedLog actLog : InterpLog R)
    (ctx : TContext sig)
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    (r1 r2 : Option (InterpLog R × tau.denote × TContext sig)) :
    interpAction R Sigma env extEnv schedLog actLog ctx a = r1 →
    interpAction R Sigma env extEnv schedLog actLog ctx a = r2 →
    r1 = r2 := by
  intro h1 h2
  rw [← h1, ← h2]

/-- Scheduler interpretation is deterministic -/
theorem interp_scheduler_deterministic
    (env : RegEnv R)
    (extEnv : ExtEnv Sigma)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (schedLog : InterpLog R)
    (s : Scheduler Unit rule_name_t)
    (l1 l2 : InterpLog R) :
    interpScheduler R Sigma env extEnv rules schedLog s = l1 →
    interpScheduler R Sigma env extEnv rules schedLog s = l2 →
    l1 = l2 := by
  intro h1 h2
  rw [← h1, ← h2]

end Determinism

end Koika
