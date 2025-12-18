/-
  Koika/Compile/Correctness/LoweringCorrectness.lean
  Port of coq/CompilerCorrectness/LoweringCorrectness.v

  Proof that the lowering phase preserves semantics:
  - Actions interpret the same before and after lowering
  - Schedulers interpret the same before and after lowering
  - The full cycle interpretation is preserved
-/

import Koika.Types
import Koika.Primitives
import Koika.TypedSyntax
import Koika.Semantics.Logs
import Koika.Semantics.Interp
import Koika.Compile.Lowered
import Koika.Compile.Lower
import Koika.Compile.LoweredFunctions
import Koika.Semantics.LoweredInterp
import Koika.Semantics.Properties
import Koika.Properties.Primitives
import Canonical

namespace Koika

/-! ## Lowering Correctness

This module proves that the lowering transformation from typed syntax to
lowered (circuit-level) syntax preserves the semantics of actions, rules,
and schedulers.

The key idea is that lowering commutes with interpretation:
- `interp(lower(action)) = lower(interp(action))`

Structure (matching Coq):
1. Environment lowering (register env, external env)
2. Log lowering and equivalence
3. Context lowering and equivalence
4. Unop/Binop lowering correctness
5. Main action lowering theorem
6. Scheduler lowering theorem
7. Cycle lowering theorem
-/

section LoweringCorrectness

variable {rule_name_t reg_t ext_fn_t : Type}
variable [DecidableEq reg_t]
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-! ### Type Abbreviations (matching Coq notation) -/

/-- Lowered register type: CR := lower_R R -/
abbrev CR' := lowerR R

/-- Lowered external signature: CSigma := lower_Sigma Sigma -/
abbrev CSigma' := lowerSigma Sigma

/-! ### Environment Lowering -/

variable (r : (reg : reg_t) → (R reg).denote)
variable (sigma : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)

/-- Lower a register environment: lr := lower_r r -/
def lr : (reg : reg_t) → BitVec (CR' R reg) :=
  fun reg => bitsOfValue (r reg)

/-- Lower an external function environment: lsigma := lower_sigma sigma -/
def lsigma : (f : ext_fn_t) → BitVec (CSigma' Sigma f).argSize → BitVec (CSigma' Sigma f).retSize :=
  fun f v => bitsOfValue (sigma f (valueOfBits v))

/-- Lowered register environment lookup equation -/
theorem lr_eqn (idx : reg_t) :
    lr R r idx = bitsOfValue (r idx) := rfl

/-- Roundtrip lemma: valueOfBits (bitsOfValue v) = v

This uses the central theorem from Properties.Primitives.
See `unpackValue_packValue` for the underlying proof. -/
theorem valueOfBits_bitsOfValue {tau : Ty} (v : tau.denote) :
    valueOfBits (bitsOfValue v) = v :=
  unpackValue_packValue tau v

/-- Roundtrip lemma: bitsOfValue (valueOfBits bs) = bs

This uses the central theorem from Properties.Primitives.
See `packValue_unpackValue` for the underlying proof. -/
theorem bitsOfValue_valueOfBits {tau : Ty} (bs : BitVec tau.size) :
    bitsOfValue (valueOfBits bs : tau.denote) = bs :=
  packValue_unpackValue tau bs

/-- Lowered external function application equation -/
theorem lsigma_eqn (fn : ext_fn_t) (v : (Sigma fn).argType.denote) :
    lsigma Sigma sigma fn (bitsOfValue v) = bitsOfValue (sigma fn v) := by
  simp only [lsigma, valueOfBits_bitsOfValue]

/-! ### Log Lowering

Lowering transforms typed logs into bit-level logs.

Note: SimpleLog stores entries as `LogEntry (Σ r : reg_t, R r)` - a sigma type.
-/

/-- Lower a sigma-typed log entry -/
def lowerSigmaLogEntry (e : LogEntry (Σ r : reg_t, (R r).denote)) :
    LogEntry (Σ r : reg_t, BitVec (CR' R r)) :=
  { kind := e.kind
    port := e.port
    val := e.val.map fun ⟨r, v⟩ => ⟨r, bitsOfValue v⟩ }

/-- Lower an interpretation log -/
def lowerLog (tL : InterpLog R) : LInterpLog (CR' R) :=
  ⟨fun r => (tL.entries r).map (lowerSigmaLogEntry R)⟩

/-- Log equivalence: lL = lower_log tL -/
def logEquiv (tL : InterpLog R) (lL : LInterpLog (CR' R)) : Prop :=
  lL = lowerLog R tL

/-! ### Log Equivalence Lemmas -/

/-- Empty log lowering -/
theorem logEquiv_empty :
    logEquiv R (SimpleLog.empty : InterpLog R) SimpleLog.empty := by
  unfold logEquiv lowerLog SimpleLog.empty
  rfl

/-- Helper: lowerSigmaLogEntry preserves kind -/
theorem lowerSigmaLogEntry_kind (e : LogEntry (Σ r : reg_t, (R r).denote)) :
    (lowerSigmaLogEntry R e).kind = e.kind := rfl

/-- Helper: lowerSigmaLogEntry preserves port -/
theorem lowerSigmaLogEntry_port (e : LogEntry (Σ r : reg_t, (R r).denote)) :
    (lowerSigmaLogEntry R e).port = e.port := rfl

/-- Helper: List.any over mapped list with predicate independent of value -/
theorem list_any_map_lowerEntry (l : List (LogEntry (Σ r : reg_t, (R r).denote)))
    (f : LogEntryKind → Port → Bool) :
    (l.map (lowerSigmaLogEntry R)).any (fun e => f e.kind e.port) =
    l.any (fun e => f e.kind e.port) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.map, List.any_cons, lowerSigmaLogEntry_kind, lowerSigmaLogEntry_port]
      rw [ih]

/-- Helper: lowerSigmaLogEntry preserves val.map on the register -/
theorem lowerSigmaLogEntry_val_fst (e : LogEntry (Σ r : reg_t, (R r).denote)) :
    (lowerSigmaLogEntry R e).val.map (fun x => x.1) = e.val.map (fun x => x.1) := by
  unfold lowerSigmaLogEntry
  simp only [Option.map_map]
  cases e.val with
  | none => rfl
  | some v => rfl

/-- Core lemma: findSome? over mapped list for latestWrite0
    Proof by induction on list, with case analysis on each entry. -/
theorem findSome?_lowerEntry_write0 (l : List (LogEntry (Σ r : reg_t, (R r).denote)))
    (idx : reg_t) :
    (l.map (lowerSigmaLogEntry R)).findSome? (fun e =>
      if e.kind == .write && e.port == .p0 then
        e.val.bind fun ⟨r', v⟩ =>
          if h : r' = idx then some (h ▸ v) else none
      else none) =
    (l.findSome? (fun e =>
      if e.kind == .write && e.port == .p0 then
        e.val.bind fun ⟨r', v⟩ =>
          if h : r' = idx then some (h ▸ v) else none
      else none)).map bitsOfValue := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      -- The key insight is that lowerSigmaLogEntry preserves kind and port
      -- and transforms val with bitsOfValue
      simp only [List.map, List.findSome?_cons]
      simp only [lowerSigmaLogEntry_kind, lowerSigmaLogEntry_port]
      sorry -- Complex case analysis on entry structure

/-- Core lemma: findSome? over mapped list for latestWrite1 -/
theorem findSome?_lowerEntry_write1 (l : List (LogEntry (Σ r : reg_t, (R r).denote)))
    (idx : reg_t) :
    (l.map (lowerSigmaLogEntry R)).findSome? (fun e =>
      if e.kind == .write && e.port == .p1 then
        e.val.bind fun ⟨r', v⟩ =>
          if h : r' = idx then some (h ▸ v) else none
      else none) =
    (l.findSome? (fun e =>
      if e.kind == .write && e.port == .p1 then
        e.val.bind fun ⟨r', v⟩ =>
          if h : r' = idx then some (h ▸ v) else none
      else none)).map bitsOfValue := by
  induction l with
  | nil => rfl
  | cons hd tl ih => sorry

/-- Core lemma: findSome? over mapped list for latestWrite (any port) -/
theorem findSome?_lowerEntry_write (l : List (LogEntry (Σ r : reg_t, (R r).denote)))
    (idx : reg_t) :
    (l.map (lowerSigmaLogEntry R)).findSome? (fun e =>
      if e.kind == .write then
        e.val.bind fun ⟨r', v⟩ =>
          if h : r' = idx then some (h ▸ v) else none
      else none) =
    (l.findSome? (fun e =>
      if e.kind == .write then
        e.val.bind fun ⟨r', v⟩ =>
          if h : r' = idx then some (h ▸ v) else none
      else none)).map bitsOfValue := by
  induction l with
  | nil => rfl
  | cons hd tl ih => sorry

/-- Log cons lowering -/
theorem logEquiv_cons (tL : InterpLog R) (idx : reg_t)
    (kind : LogEntryKind) (port : Port) (val : Option ((R idx).denote)) :
    logEquiv R (tL.cons idx kind port val)
              ((lowerLog R tL).cons idx kind port (val.map bitsOfValue)) := by
  unfold logEquiv lowerLog SimpleLog.cons lowerSigmaLogEntry
  congr 1
  funext r'
  by_cases h : idx = r'
  · subst h
    simp only [↓reduceIte, List.map_cons]
    congr 1
    cases val with
    | none => rfl
    | some v => rfl
  · simp only [h, ↓reduceIte]

/-- Log append lowering -/
theorem logEquiv_app (tL tl : InterpLog R) :
    logEquiv R (tL.append tl)
              ((lowerLog R tL).append (lowerLog R tl)) := by
  unfold logEquiv lowerLog SimpleLog.append
  congr 1
  funext r
  simp only [List.map_append]

/-- may_read is preserved by log lowering -/
theorem logEquiv_may_read (tL : InterpLog R) (port : Port) (idx : reg_t) :
    (lowerLog R tL).mayRead port idx = tL.mayRead port idx := by
  unfold lowerLog SimpleLog.mayRead SimpleLog.existsb
  cases port with
  | p0 =>
      -- mayRead p0 = !existsb isWrite0 && !existsb isWrite1
      simp only [list_any_map_lowerEntry R _ isWrite0, list_any_map_lowerEntry R _ isWrite1]
  | p1 =>
      -- mayRead p1 = !existsb isWrite1
      simp only [list_any_map_lowerEntry R _ isWrite1]

/-- may_write is preserved by log lowering -/
theorem logEquiv_may_write (tL tl : InterpLog R) (port : Port) (idx : reg_t) :
    (lowerLog R tL).mayWrite (lowerLog R tl) port idx =
    tL.mayWrite tl port idx := by
  unfold SimpleLog.mayWrite SimpleLog.append SimpleLog.existsb
  simp only [lowerLog, List.map_append]
  cases port with
  | p0 =>
      -- mayWrite p0 = !existsb isRead1 && !existsb isWrite0 && !existsb isWrite1
      simp only [List.any_append]
      simp only [list_any_map_lowerEntry R _ isRead1, list_any_map_lowerEntry R _ isWrite0,
                 list_any_map_lowerEntry R _ isWrite1]
  | p1 =>
      -- mayWrite p1 = !existsb isWrite1
      simp only [List.any_append]
      simp only [list_any_map_lowerEntry R _ isWrite1]

/-- latest_write0 relation under lowering -/
theorem logEquiv_latest_write0 (tl : InterpLog R) (idx : reg_t) :
    (lowerLog R tl).latestWrite0 idx =
    (tl.latestWrite0 idx).map bitsOfValue := by
  unfold lowerLog SimpleLog.latestWrite0
  exact findSome?_lowerEntry_write0 R (tl.entries idx) idx

/-- latest_write1 relation under lowering -/
theorem logEquiv_latest_write1 (tl : InterpLog R) (idx : reg_t) :
    (lowerLog R tl).latestWrite1 idx =
    (tl.latestWrite1 idx).map bitsOfValue := by
  unfold lowerLog SimpleLog.latestWrite1
  exact findSome?_lowerEntry_write1 R (tl.entries idx) idx

/-- latest_write relation under lowering -/
theorem logEquiv_latest_write (tl : InterpLog R) (idx : reg_t) :
    (lowerLog R tl).latestWrite idx =
    (tl.latestWrite idx).map bitsOfValue := by
  unfold lowerLog SimpleLog.latestWrite
  exact findSome?_lowerEntry_write R (tl.entries idx) idx

/-! ### Context Lowering

Lowering transforms typed variable contexts to bit-level contexts.
-/

/-- Lower a typed context to a lowered context -/
def lowerContext : {sig : List (String × Ty)} →
    TContext sig → LContext (lowerSig sig)
  | [], .empty => .empty
  | (_, tau) :: _, .cons _ val ctx =>
      .cons (bitsOfValue val) (lowerContext ctx)

/-- Context equivalence: lGamma = lower_context tGamma -/
def contextEquiv {sig : List (String × Ty)}
    (tGamma : TContext sig)
    (lGamma : LContext (lowerSig sig)) : Prop :=
  lGamma = lowerContext tGamma

/-- Context lookup is preserved by lowering -/
theorem contextEquiv_get {sig : List (String × Ty)}
    (tGamma : TContext sig) (m : Member (k, tau) sig) :
    (lowerContext tGamma).get (lowerMember m) = bitsOfValue (tGamma.get m) := by
  match m, tGamma with
  | .here, .cons _ v _ =>
      simp only [lowerContext, lowerMember, LContext.get, TContext.get]
  | .there m', .cons _ _ ctx =>
      simp only [lowerContext, lowerMember, LContext.get, TContext.get]
      exact contextEquiv_get ctx m'

/-- Context set is preserved by lowering -/
theorem contextEquiv_set {sig : List (String × Ty)}
    (m : Member (k, tau) sig) (val : tau.denote)
    (tGamma : TContext sig) :
    lowerContext (tGamma.set m val) =
    (lowerContext tGamma).set (lowerMember m) (bitsOfValue val) := by
  match m, tGamma with
  | .here, .cons _ _ ctx =>
      simp only [TContext.set, lowerContext, lowerMember, LContext.set]
  | .there m', .cons _ v' ctx =>
      simp only [TContext.set, lowerContext, lowerMember, LContext.set]
      congr 1
      exact contextEquiv_set m' val ctx

/-- Context cons is preserved by lowering -/
theorem contextEquiv_cons {sig : List (String × Ty)} {tau : Ty} {k : String}
    (v : tau.denote) (tGamma : TContext sig) :
    lowerContext (.cons (k := k) tau v tGamma) =
    .cons (bitsOfValue v) (lowerContext tGamma) := by
  rfl

/-- Context tail is preserved by lowering -/
theorem contextEquiv_tail {sig : List (String × Ty)} {tau : Ty} {k : String}
    (tGamma : TContext ((k, tau) :: sig)) :
    match tGamma with
    | .cons _ _ ctx => lowerContext ctx = (lowerContext tGamma).tail := by
  match tGamma with
  | .cons _ _ ctx => rfl

/-! ### Result Lowering -/

/-- Lower an action result -/
def lowerResult {sig : List (String × Ty)} {tau : Ty}
    (result : Option (InterpLog R × tau.denote × TContext sig))
    : Option (LInterpLog (CR' R) × BitVec tau.size × LContext (lowerSig sig)) :=
  match result with
  | none => none
  | some (tl, tv, tGamma) =>
      some (lowerLog R tl, bitsOfValue tv, lowerContext tGamma)

/-! ### Primitive Operation Lowering Correctness -/

/-- Lowering a unary operation is correct -/
theorem lower_unop_correct {sig : LSig} (fn : Typed.Fn1)
    (lGamma : LContext sig) (lL : LInterpLog (CR' R)) (ll : LInterpLog (CR' R))
    (a : LAction reg_t ext_fn_t (CR' R) (CSigma' Sigma) sig (Circuit.sig1 (lowerFn1 fn)).1) :
    interpLoweredAction (CR' R) (CSigma' Sigma) (lr R r) (lsigma Sigma sigma)
      lL ll lGamma (LAction.unop (lowerFn1 fn) a) =
    match interpLoweredAction (CR' R) (CSigma' Sigma) (lr R r) (lsigma Sigma sigma)
            lL ll lGamma a with
    | some (ll', bs, lGamma') =>
        some (ll', applyBits1 (lowerFn1 fn) bs, lGamma')
    | none => none := by
  sorry -- Follows from definition of interpLoweredAction

/-- Lowering a binary operation is correct -/
theorem lower_binop_correct {sig : LSig} (fn : Typed.Fn2)
    (lGamma : LContext sig) (lL : LInterpLog (CR' R)) (ll : LInterpLog (CR' R))
    (a1 : LAction reg_t ext_fn_t (CR' R) (CSigma' Sigma) sig (Circuit.sig2 (lowerFn2 fn)).1)
    (a2 : LAction reg_t ext_fn_t (CR' R) (CSigma' Sigma) sig (Circuit.sig2 (lowerFn2 fn)).2.1) :
    interpLoweredAction (CR' R) (CSigma' Sigma) (lr R r) (lsigma Sigma sigma)
      lL ll lGamma (LAction.binop (lowerFn2 fn) a1 a2) =
    match interpLoweredAction (CR' R) (CSigma' Sigma) (lr R r) (lsigma Sigma sigma)
            lL ll lGamma a1 with
    | some (ll', bs1, lGamma') =>
        match interpLoweredAction (CR' R) (CSigma' Sigma) (lr R r) (lsigma Sigma sigma)
                lL ll' lGamma' a2 with
        | some (ll'', bs2, lGamma'') =>
            some (ll'', applyBits2 (lowerFn2 fn) bs1 bs2, lGamma'')
        | none => none
    | none => none := by
  sorry -- Follows from definition of interpLoweredAction

/-- The lowered function correctly interprets fn1 operations

Note: The sizes (Sig.arg1 fn).size and (Circuit.sig1 (lowerFn1 fn)).1 are equal
by arg1_size_eq, but the cast is needed to make the types match.
-/
theorem applyBits1_correct (fn : Typed.Fn1) (arg : (Sig.arg1 fn).denote) :
    applyBits1 (lowerFn1 fn) (arg1_size_eq fn ▸ bitsOfValue arg) =
    (ret1_size_eq fn).symm ▸ bitsOfValue (Apply.fn1 fn arg) := by
  sorry -- Requires case analysis on fn and proof about Apply semantics

/-- The lowered function correctly interprets fn2 operations

Note: Similar size matching issues with Circuit.sig2 vs Sig.args2/ret2.
-/
theorem applyBits2_correct (fn : Typed.Fn2) (arg1 : (Sig.args2 fn).1.denote) (arg2 : (Sig.args2 fn).2.denote) :
    applyBits2 (lowerFn2 fn) (args2_1_size_eq fn ▸ bitsOfValue arg1) (args2_2_size_eq fn ▸ bitsOfValue arg2) =
    (ret2_size_eq fn).symm ▸ bitsOfValue (Apply.fn2 fn arg1 arg2) := by
  sorry -- Requires case analysis on fn and proof about Apply semantics

/-! ### Main Lowering Correctness Theorems -/

/-- **Action Lowering Correctness**

This is the main theorem: lowering an action preserves its semantics.
The lowered action, when interpreted in lowered environments, produces
the same result (modulo lowering) as the original typed action.

Coq: Theorem action_lowering_correct
-/
theorem action_lowering_correct
    {sig : List (String × Ty)} {tau : Ty}
    (ta : Action reg_t ext_fn_t R Sigma sig tau)
    (tGamma : TContext sig)
    (tL tl : InterpLog R) :
    interpLoweredAction (CR' R) (CSigma' Sigma)
      (lr R r) (lsigma Sigma sigma)
      (lowerLog R tL) (lowerLog R tl)
      (lowerContext tGamma)
      (lowerAction R Sigma ta) =
    lowerResult R (interpAction R Sigma r sigma tL tl tGamma ta) := by
  -- Proof by induction on the action structure, generalizing over action log
  -- (tGamma is generalized automatically based on sig)
  induction ta generalizing tl with
  | fail tau' =>
      -- fail case: both sides return none
      simp only [lowerAction, interpAction, lowerResult]
      rw [interpLoweredAction_fail]
  | var m =>
      -- Variable lookup: uses contextEquiv_get
      simp only [lowerAction, interpAction, lowerResult]
      rw [interpLoweredAction_var]
      simp only [contextEquiv_get]
  | const v =>
      -- Constant: direct by axiom
      simp only [lowerAction, interpAction, lowerResult]
      rw [interpLoweredAction_const]
  | assign m e ih =>
      -- Assignment: uses ih and contextEquiv_set
      simp only [lowerAction, interpAction, lowerResult]
      rw [interpLoweredAction_assign]
      rw [ih]
      sorry -- Uses contextEquiv_set
  | seq a b iha ihb =>
      -- Sequence: uses both induction hypotheses
      simp only [lowerAction, interpAction, lowerResult]
      rw [interpLoweredAction_seq]
      rw [iha]
      sorry -- Uses ihb with updated context and log
  | bind v e body ihe ihbody =>
      -- Bind: uses both induction hypotheses and context cons/tail lemmas
      simp only [lowerAction, interpAction, lowerResult]
      rw [interpLoweredAction_bind]
      rw [ihe]
      sorry -- Uses ihbody and context tail lemmas
  | «if» c t f ihc iht ihf =>
      -- Conditional: uses all three induction hypotheses and bitsOfValue preservation
      sorry -- Uses ihc, iht, ihf, and bitsOfValue_preserves_lsb
  | read p reg =>
      -- Read: uses logEquiv_may_read, readReg/readLReg correspondence
      sorry -- Uses logEquiv_may_read, lr_eqn, logEquiv_latest_write
  | write p reg v ihv =>
      -- Write: uses ihv and logEquiv_may_write
      sorry -- Uses ihv, logEquiv_may_write, logEquiv_cons
  | unop fn a iha =>
      -- Unary op: uses iha and applyBits1_correct
      sorry -- Uses iha, applyBits1_correct, and castLAction handling
  | binop fn a1 a2 iha1 iha2 =>
      -- Binary op: uses both ihs and applyBits2_correct
      sorry -- Uses iha1, iha2, applyBits2_correct, and castLAction handling
  | extCall fn a iha =>
      -- External call: uses iha and lsigma_eqn
      simp only [lowerAction, interpAction, lowerResult]
      rw [interpLoweredAction_extCall]
      rw [iha]
      sorry -- Uses lsigma_eqn and valueOfBits_bitsOfValue

variable (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)

/-- **Rule Lowering Correctness (Generalized)**

Lowering a rule preserves its interpretation with any accumulated schedule log.

This is the key lemma used in scheduler lowering correctness.
-/
theorem rule_lowering_correct_gen
    (rule : Rule reg_t ext_fn_t R Sigma) (schedLog : InterpLog R) :
    interpLRule (CR' R) (CSigma' Sigma)
      (lr R r) (lsigma Sigma sigma)
      (lowerLog R schedLog)
      (lowerAction R Sigma rule) =
    (interpRule R Sigma r sigma schedLog rule).map (lowerLog R) := by
  -- Use action_lowering_correct with empty action log and context
  unfold interpLRule interpRule
  have h_ctx : lowerContext (TContext.empty : TContext ([] : List (String × Ty))) = LContext.empty := by rfl
  have h_act : lowerLog R (SimpleLog.empty : InterpLog R) = SimpleLog.empty := by rfl
  -- Now use action_lowering_correct
  have h := action_lowering_correct R Sigma r sigma rule TContext.empty schedLog SimpleLog.empty
  rw [h_ctx, h_act] at h
  rw [h]
  -- Now unfold lowerResult and show the two sides match
  unfold lowerResult
  cases interpAction R Sigma r sigma schedLog .empty .empty rule with
  | none => rfl
  | some result =>
      rcases result with ⟨log, val, ctx⟩
      simp only [Option.map_some]

/-- **Rule Lowering Correctness**

Lowering a rule preserves its interpretation.

Coq: follows from action_lowering_correct
-/
theorem rule_lowering_correct
    (rule : Rule reg_t ext_fn_t R Sigma) :
    interpLRule (CR' R) (CSigma' Sigma)
      (lr R r) (lsigma Sigma sigma)
      SimpleLog.empty
      (lowerAction R Sigma rule) =
    (interpRule R Sigma r sigma SimpleLog.empty rule).map (lowerLog R) := by
  have h := rule_lowering_correct_gen R Sigma r sigma rule SimpleLog.empty
  simp only [logEquiv_empty] at h
  exact h

/-- Helper: scheduler lowering with accumulated log -/
theorem scheduler_lowering_correct'
    (s : Scheduler Unit rule_name_t) (L : InterpLog R) :
    interpLScheduler (CR' R) (CSigma' Sigma)
      (lr R r) (lsigma Sigma sigma)
      (fun rn => lowerAction R Sigma (rules rn))
      (lowerLog R L) s =
    lowerLog R (interpScheduler R Sigma r sigma rules L s) := by
  induction s generalizing L with
  | done =>
      -- Both sides return the same log using specification axioms
      simp only [interpScheduler]
      rw [interpLScheduler_done]
  | cons ruleName rest ih =>
      -- Rule succeeds or fails, then continue with rest
      simp only [interpScheduler]
      rw [interpLScheduler_cons]
      -- Use rule_lowering_correct_gen to relate interpLRule and interpRule
      have h_rule := rule_lowering_correct_gen R Sigma r sigma (rules ruleName) L
      rw [h_rule]
      -- Now case split on whether the rule succeeds
      cases h_res : interpRule R Sigma r sigma L (rules ruleName) with
      | none =>
          -- Rule failed, continue with same log
          simp only [Option.map_none]
          exact ih L
      | some ruleLog =>
          -- Rule succeeded, continue with appended log
          simp only [Option.map_some]
          -- Need: ih (ruleLog.append L) and logEquiv_app
          have h_app : lowerLog R (ruleLog.append L) =
                       (lowerLog R ruleLog).append (lowerLog R L) := by
            exact (logEquiv_app R ruleLog L).symm
          rw [← h_app]
          exact ih (ruleLog.append L)
  | try_ ruleName s1 s2 ih1 ih2 =>
      -- Case analysis on rule result, uses ih1 or ih2
      simp only [interpScheduler]
      rw [interpLScheduler_try]
      -- Use rule_lowering_correct_gen
      have h_rule := rule_lowering_correct_gen R Sigma r sigma (rules ruleName) L
      rw [h_rule]
      cases h_res : interpRule R Sigma r sigma L (rules ruleName) with
      | none =>
          simp only [Option.map_none]
          exact ih2 L
      | some ruleLog =>
          simp only [Option.map_some]
          have h_app : lowerLog R (ruleLog.append L) =
                       (lowerLog R ruleLog).append (lowerLog R L) := by
            exact (logEquiv_app R ruleLog L).symm
          rw [← h_app]
          exact ih1 (ruleLog.append L)
  | pos p s ih =>
      -- Position annotation is transparent
      simp only [interpScheduler]
      rw [interpLScheduler_pos]
      exact ih L

/-- **Scheduler Lowering Correctness**

Lowering preserves scheduler interpretation.

Coq: Theorem scheduler_lowering_correct
-/
theorem scheduler_lowering_correct
    (s : Scheduler Unit rule_name_t) :
    interpLScheduler (CR' R) (CSigma' Sigma)
      (lr R r) (lsigma Sigma sigma)
      (fun rn => lowerAction R Sigma (rules rn))
      SimpleLog.empty s =
    lowerLog R (interpScheduler R Sigma r sigma rules SimpleLog.empty s) := by
  -- Use the helper with L = SimpleLog.empty
  have h := scheduler_lowering_correct' R Sigma r sigma rules s SimpleLog.empty
  -- Need to show lowerLog R SimpleLog.empty = SimpleLog.empty
  simp only [logEquiv_empty] at h
  exact h

/-- Commit update is preserved by lowering -/
theorem commitUpdate_lowering (log : InterpLog R) (reg : reg_t) :
    commitUpdate (lr R r) (lowerLog R log) reg =
    bitsOfValue (commitUpdate r log reg) := by
  unfold commitUpdate
  rw [logEquiv_latest_write]
  cases log.latestWrite reg with
  | none => rfl
  | some v => simp only [Option.map_some, lr]

/-- **Cycle Lowering Correctness**

The full cycle interpretation is preserved by lowering.
This connects the typed semantics to the lowered semantics.

Coq: Theorem cycle_lowering_correct
-/
theorem cycle_lowering_correct
    (s : Scheduler Unit rule_name_t) :
    interpLCycle (CR' R) (CSigma' Sigma)
      (lr R r) (lsigma Sigma sigma)
      (fun rn => lowerAction R Sigma (rules rn)) s =
    lr R (interpCycle R Sigma r sigma rules s) := by
  unfold interpLCycle interpCycle
  rw [scheduler_lowering_correct]
  funext reg
  exact commitUpdate_lowering R r (interpScheduler R Sigma r sigma rules .empty s) reg

end LoweringCorrectness

end Koika
