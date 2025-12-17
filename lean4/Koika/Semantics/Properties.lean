/-
  Koika/Semantics/Properties.lean - Port of coq/SemanticProperties.v
  Properties and lemmas about semantic log operations

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/SemanticProperties.v
  For VersoCoq documentation: {coq}`SemanticProperties.v`
-/

import Koika.Types
import Koika.Primitives
import Koika.TypedSyntax
import Koika.Semantics.Logs
import Koika.Semantics.Interp

namespace Koika

/-! ## List Lemmas -/

/-- Searching in an appended list returns the first list's result if found -/
theorem list_find_opt_app {A : Type} (f : A → Bool) (l1 l2 : List A) :
    (l1 ++ l2).find? (fun a => f a) =
      match l1.find? (fun a => f a) with
      | some x => some x
      | none => l2.find? (fun a => f a) := by
  induction l1 with
  | nil => simp
  | cons h t ih =>
    simp only [List.cons_append, List.find?_cons]
    split <;> simp_all

/-! ## Log Append Properties -/

section LogProperties

variable {reg_t : Type} [DecidableEq reg_t]
variable {V : reg_t → Type}

/-- Log append is associative -/
theorem log_app_assoc (l1 l2 l3 : SimpleLog V) :
    (l1.append l2).append l3 = l1.append (l2.append l3) := by
  unfold SimpleLog.append
  simp [List.append_assoc]

/-- Empty log is left identity for append -/
theorem log_app_empty_l (l : SimpleLog V) :
    SimpleLog.empty.append l = l := by
  unfold SimpleLog.append SimpleLog.empty
  simp

/-- Empty log is right identity for append -/
theorem log_app_empty_r (l : SimpleLog V) :
    l.append SimpleLog.empty = l := by
  unfold SimpleLog.append SimpleLog.empty
  simp

end LogProperties

/-! ## Log Forall/Exists Properties -/

section LogPredicates

variable {reg_t : Type} [DecidableEq reg_t]
variable {V : reg_t → Type}

/-- Forall over appended logs is conjunction of foralls -/
theorem log_forallb_app (f : LogEntryKind → Port → Bool) (l1 l2 : SimpleLog V) (r : reg_t) :
    (l1.append l2).forallb r f = (l1.forallb r f && l2.forallb r f) := by
  unfold SimpleLog.append SimpleLog.forallb
  simp [List.all_append]

/-- Exists over appended logs is disjunction of exists -/
theorem log_existsb_app (f : LogEntryKind → Port → Bool) (l1 l2 : SimpleLog V) (r : reg_t) :
    (l1.append l2).existsb r f = (l1.existsb r f || l2.existsb r f) := by
  unfold SimpleLog.append SimpleLog.existsb
  simp [List.any_append]

end LogPredicates

/-! ## May Read/Write Properties -/

section MayReadWrite

variable {reg_t : Type} [DecidableEq reg_t]
variable {V : reg_t → Type}

/-- May read port 0 in appended logs -/
@[grind] theorem may_read0_app_sl (l1 l2 : SimpleLog V) (idx : reg_t) :
    (l1.append l2).mayRead .p0 idx =
      (l1.mayRead .p0 idx && l2.mayRead .p0 idx) := by
  unfold SimpleLog.mayRead
  simp only [log_existsb_app]
  -- !((a || b)) && !((c || d)) = (!a && !b) && (!c && !d) = (!a && !c) && (!b && !d)
  cases l1.existsb idx isWrite0 <;> cases l1.existsb idx isWrite1 <;>
  cases l2.existsb idx isWrite0 <;> cases l2.existsb idx isWrite1 <;> simp

/-- May read port 1 in appended logs -/
@[grind] theorem may_read1_app_sl (l1 l2 : SimpleLog V) (idx : reg_t) :
    (l1.append l2).mayRead .p1 idx =
      (l1.mayRead .p1 idx && l2.mayRead .p1 idx) := by
  unfold SimpleLog.mayRead
  simp only [log_existsb_app]
  cases l1.existsb idx isWrite1 <;> cases l2.existsb idx isWrite1 <;> simp

/-- Helper: existsb distributes over append -/
@[grind] theorem existsb_append (l1 l2 : SimpleLog V) (idx : reg_t) (f : LogEntryKind → Port → Bool) :
    (l1.append l2).existsb idx f = (l1.existsb idx f || l2.existsb idx f) := by
  unfold SimpleLog.append SimpleLog.existsb
  simp only [List.any_append]

/-- May write port 0 in appended logs -/
@[grind] theorem may_write0_app_sl (l1 l2 actLog : SimpleLog V) (idx : reg_t) :
    (l1.append l2).mayWrite actLog .p0 idx =
      (l1.mayWrite actLog .p0 idx && l2.mayWrite actLog .p0 idx) := by
  unfold SimpleLog.mayWrite
  simp only [existsb_append]
  -- After unfolding, both sides involve checking actLog, l1, l2 for various predicates
  -- LHS: !((al || l1 || l2)) && !((bl || l1' || l2')) && !((cl || l1'' || l2''))
  -- RHS: (!(al || l1) && !(bl || l1') && !(cl || l1'')) && (!(al || l2) && !(bl || l2') && !(cl || l2''))
  -- These are equivalent by Boolean algebra
  cases actLog.existsb idx isRead1 <;>
  cases actLog.existsb idx isWrite0 <;>
  cases actLog.existsb idx isWrite1 <;>
  cases l1.existsb idx isRead1 <;>
  cases l1.existsb idx isWrite0 <;>
  cases l1.existsb idx isWrite1 <;>
  cases l2.existsb idx isRead1 <;>
  cases l2.existsb idx isWrite0 <;>
  cases l2.existsb idx isWrite1 <;>
  simp

/-- May write port 1 in appended logs -/
@[grind] theorem may_write1_app_sl (l1 l2 actLog : SimpleLog V) (idx : reg_t) :
    (l1.append l2).mayWrite actLog .p1 idx =
      (l1.mayWrite actLog .p1 idx && l2.mayWrite actLog .p1 idx) := by
  unfold SimpleLog.mayWrite
  simp only [existsb_append]
  cases actLog.existsb idx isWrite1 <;>
  cases l1.existsb idx isWrite1 <;>
  cases l2.existsb idx isWrite1 <;>
  simp

/-- Helper: no Write1 entries implies latestWrite1 is none -/
@[grind] theorem no_existsb_write1_implies_latestWrite1_none (l : SimpleLog V) (idx : reg_t) :
    l.existsb idx isWrite1 = false → l.latestWrite1 idx = none := by
  intro hno
  unfold SimpleLog.latestWrite1
  rw [List.findSome?_eq_none_iff]
  intro e he
  unfold SimpleLog.existsb isWrite1 at hno
  simp only [List.any_eq_false] at hno
  have hentry := hno e he
  -- If the entry is a write at port 1, we get a contradiction
  -- Otherwise, the if-condition is false
  split
  case isTrue h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hentry
    exact absurd h hentry
  case isFalse => rfl

/-- May read port 0 implies no prior writes at port 1 -/
@[grind] theorem may_read0_no_writes (l : SimpleLog V) (idx : reg_t) :
    l.mayRead .p0 idx = true →
    l.latestWrite1 idx = none := by
  intro h
  unfold SimpleLog.mayRead at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  apply no_existsb_write1_implies_latestWrite1_none
  exact h.2

/-- May read port 1 reflects only port 0 writes when no conflicts -/
@[grind] theorem may_read1_latest_write_is_0 (l : SimpleLog V) (idx : reg_t) :
    l.mayRead .p1 idx = true →
    l.latestWrite1 idx = none := by
  intro h
  unfold SimpleLog.mayRead at h
  simp only [Bool.not_eq_true'] at h
  apply no_existsb_write1_implies_latestWrite1_none
  exact h

end MayReadWrite

/-! ## Latest Write Properties -/

section LatestWrite

variable {reg_t : Type} [DecidableEq reg_t]
variable {V : reg_t → Type}

/-- Latest write to port 0 in empty log -/
theorem latest_write0_empty (idx : reg_t) :
    SimpleLog.latestWrite0 (R := V) SimpleLog.empty idx = none := by
  unfold SimpleLog.latestWrite0 SimpleLog.empty
  simp

/-- Latest write to port 1 in empty log -/
theorem latest_write1_empty (idx : reg_t) :
    SimpleLog.latestWrite1 (R := V) SimpleLog.empty idx = none := by
  unfold SimpleLog.latestWrite1 SimpleLog.empty
  simp

/-- Latest write finds most recent write at given port -/
@[grind] theorem latest_write0_cons_write (l : SimpleLog V) (idx : reg_t) (v : V idx) :
    (l.cons idx .write .p0 (some v)).latestWrite0 idx = some v := by
  unfold SimpleLog.latestWrite0 SimpleLog.cons
  simp only [↓reduceIte, List.findSome?_cons]
  simp only [Option.map, Option.bind, ↓reduceDIte]
  have h1 : (LogEntryKind.write == LogEntryKind.write) = true := rfl
  have h2 : (Port.p0 == Port.p0) = true := rfl
  simp only [h1, h2, Bool.true_and, ↓reduceIte]

/-- Latest write skips non-matching entries -/
@[grind] theorem latest_write0_cons_neq (l : SimpleLog V) (idx idx' : reg_t) (k : LogEntryKind) (p : Port) (v : Option (V idx)) :
    idx ≠ idx' →
    (l.cons idx k p v).latestWrite0 idx' = l.latestWrite0 idx' := by
  intro h
  unfold SimpleLog.latestWrite0 SimpleLog.cons
  simp only [h, ite_false]

end LatestWrite

/-! ## Commit Update Properties -/

section CommitUpdate

variable {reg_t : Type} [DecidableEq reg_t]
variable (R : reg_t → Ty)

/-- Helper: latestWrite distributes over append (first log takes priority) -/
@[grind] theorem latestWrite_append (l1 l2 : SimpleLog V) (r : reg_t) :
    (l1.append l2).latestWrite r = (l1.latestWrite r).or (l2.latestWrite r) := by
  unfold SimpleLog.latestWrite SimpleLog.append
  simp only [List.findSome?_append]

/-- Commit update follows last-writer-wins semantics (l2 overrides l1) -/
@[grind] theorem commit_update_assoc (env : RegEnv R) (l1 l2 : InterpLog R) :
    commitUpdate (commitUpdate env l1) l2 =
    commitUpdate env (l2.append l1) := by
  ext r
  unfold commitUpdate
  simp only [latestWrite_append]
  cases h2 : l2.latestWrite r <;> cases h1 : l1.latestWrite r <;> simp [Option.or]

/-- Commit update with empty log is identity -/
theorem commit_update_empty (env : RegEnv R) :
    commitUpdate env SimpleLog.empty = env := by
  unfold commitUpdate
  ext r
  simp [SimpleLog.latestWrite, SimpleLog.empty]

/-- Get environment after commit update - matches commitUpdate definition -/
@[grind] theorem getenv_commit_update (env : RegEnv R) (l : InterpLog R) (idx : reg_t) :
    commitUpdate env l idx =
      (l.latestWrite idx).getD (env idx) := by
  unfold commitUpdate
  cases l.latestWrite idx <;> simp [Option.getD]

end CommitUpdate

/-! ## LatestWrite0 Properties -/

section LatestWrite0

variable {reg_t : Type} [DecidableEq reg_t]
variable {V : reg_t → Type}

/-- LatestWrite0 distributes over append (first log takes priority) -/
@[grind] theorem latestWrite0_append (l1 l2 : SimpleLog V) (r : reg_t) :
    (l1.append l2).latestWrite0 r =
      (l1.latestWrite0 r).or (l2.latestWrite0 r) := by
  unfold SimpleLog.latestWrite0 SimpleLog.append
  simp only [List.findSome?_append]

/-- LatestWrite1 distributes over append (first log takes priority) -/
@[grind] theorem latestWrite1_append (l1 l2 : SimpleLog V) (r : reg_t) :
    (l1.append l2).latestWrite1 r =
      (l1.latestWrite1 r).or (l2.latestWrite1 r) := by
  unfold SimpleLog.latestWrite1 SimpleLog.append
  simp only [List.findSome?_append]

/-- Helper: findSome? with equivalent predicates -/
theorem findSome_eq_of_pred_eq {α β : Type} (f g : α → Option β) (l : List α) :
    (∀ a ∈ l, f a = g a) → l.findSome? f = l.findSome? g := by
  intro h
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?_cons]
    have hmem : x ∈ x :: xs := by simp
    rw [h x hmem]
    cases hfx : g x with
    | some v => rfl
    | none =>
      apply ih
      intro a ha
      have hmem' : a ∈ x :: xs := by simp [ha]
      exact h a hmem'

/-- If no write1 entries, latestWrite equals latestWrite0 -/
@[grind] theorem latestWrite_eq_latestWrite0_of_no_write1 (l : SimpleLog V) (r : reg_t) :
    l.existsb r isWrite1 = false →
    l.latestWrite r = l.latestWrite0 r := by
  intro hno
  unfold SimpleLog.latestWrite SimpleLog.latestWrite0
  apply findSome_eq_of_pred_eq
  intro e he
  unfold SimpleLog.existsb isWrite1 at hno
  simp only [List.any_eq_false, Bool.and_eq_true] at hno
  have hno_e := hno e he
  -- hno_e : ¬((e.kind == .write) = true ∧ (e.port == .p1) = true)
  -- Two cases based on whether e.kind = write ∧ e.port = p0
  by_cases hkind : (e.kind == LogEntryKind.write) = true
  · -- e.kind == write
    by_cases hport : (e.port == Port.p0) = true
    · -- e.port == p0: both sides give same result
      simp only [hkind, hport, Bool.true_and, ↓reduceIte]
    · -- e.port ≠ p0, so e.port == p1
      cases hp : e.port with
      | p0 =>
        -- Contradiction: hport says (e.port == p0) = false but hp says e.port = p0
        have : (Port.p0 == Port.p0) = true := rfl
        rw [hp] at hport
        exact absurd this (by simp [hport])
      | p1 =>
        -- But we have no write1 entries
        have hport1 : (e.port == Port.p1) = true := by rw [hp]; rfl
        exact absurd ⟨hkind, hport1⟩ hno_e
  · -- e.kind ≠ write: both sides give none
    have hbeq : (e.kind == LogEntryKind.write) = false := by
      cases h : (e.kind == LogEntryKind.write) with
      | true => exact absurd h hkind
      | false => rfl
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, Bool.false_and]

/-- LatestWrite0 of empty log is none -/
@[grind] theorem latestWrite0_empty (r : reg_t) :
    (SimpleLog.empty (R := V)).latestWrite0 r = none := by
  unfold SimpleLog.latestWrite0 SimpleLog.empty
  simp

/-- Appending empty log on right doesn't change latestWrite0 -/
@[grind] theorem latestWrite0_append_empty (l : SimpleLog V) (r : reg_t) :
    (l.append SimpleLog.empty).latestWrite0 r = l.latestWrite0 r := by
  rw [latestWrite0_append, latestWrite0_empty]
  simp only [Option.or_none]

end LatestWrite0

/-! ## Read Register Commit Properties -/

section ReadRegCommit

variable {reg_t ext_fn_t : Type} [DecidableEq reg_t]
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Port 0 read with commit: if no writes in schedLog for r, reads are equal -/
theorem readReg_p0_commit (env : RegEnv R) (schedLog actLog : InterpLog R) (r : reg_t) :
    schedLog.mayRead .p0 r = true →
    readReg R env schedLog actLog .p0 r =
    readReg R (commitUpdate env schedLog) .empty actLog .p0 r := by
  intro hmay
  unfold readReg
  -- LHS = env r
  -- RHS = commitUpdate env schedLog r
  -- Need to show these are equal
  unfold SimpleLog.mayRead at hmay
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmay
  obtain ⟨hno0, hno1⟩ := hmay
  -- No write0 or write1 in schedLog means latestWrite = none
  unfold commitUpdate
  have hnowrite : schedLog.latestWrite r = none := by
    unfold SimpleLog.latestWrite
    rw [List.findSome?_eq_none_iff]
    intro e he
    unfold SimpleLog.existsb at hno0 hno1
    unfold isWrite0 at hno0
    unfold isWrite1 at hno1
    simp only [List.any_eq_false, Bool.and_eq_true] at hno0 hno1
    have hno0' := hno0 e he
    have hno1' := hno1 e he
    by_cases hkind : (e.kind == LogEntryKind.write) = true
    · -- e.kind == write, but can't be at p0 or p1
      cases hp : e.port with
      | p0 =>
        have hport0 : (e.port == Port.p0) = true := by rw [hp]; rfl
        exact absurd ⟨hkind, hport0⟩ hno0'
      | p1 =>
        have hport1 : (e.port == Port.p1) = true := by rw [hp]; rfl
        exact absurd ⟨hkind, hport1⟩ hno1'
    · -- e.kind ≠ write
      have hbeq : (e.kind == LogEntryKind.write) = false := by
        cases h : (e.kind == LogEntryKind.write) with
        | true => exact absurd h hkind
        | false => rfl
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
  simp [hnowrite]

/-- Port 1 read with commit: reads are equal when schedLog has no write1 -/
theorem readReg_p1_commit (env : RegEnv R) (schedLog actLog : InterpLog R) (r : reg_t) :
    schedLog.mayRead .p1 r = true →
    readReg R env schedLog actLog .p1 r =
    readReg R (commitUpdate env schedLog) .empty actLog .p1 r := by
  intro hmay
  unfold readReg
  -- LHS = (actLog.append schedLog).latestWrite0 r or env r
  -- RHS = (actLog.append .empty).latestWrite0 r or commitUpdate env schedLog r
  --     = actLog.latestWrite0 r or commitUpdate env schedLog r
  rw [latestWrite0_append, latestWrite0_append_empty]
  unfold SimpleLog.mayRead at hmay
  simp only [Bool.not_eq_true'] at hmay
  -- hmay : schedLog.existsb r isWrite1 = false
  -- This means schedLog.latestWrite r = schedLog.latestWrite0 r
  cases ha : actLog.latestWrite0 r with
  | some v =>
    -- Both sides return v
    simp only [Option.or, ha, Option.getD_some]
  | none =>
    -- LHS = schedLog.latestWrite0 r or env r
    -- RHS = commitUpdate env schedLog r
    simp only [Option.or, ha, Option.getD_none]
    unfold commitUpdate
    have heq : schedLog.latestWrite r = schedLog.latestWrite0 r := by
      apply latestWrite_eq_latestWrite0_of_no_write1
      exact hmay
    rw [heq]
    cases schedLog.latestWrite0 r <;> rfl

/-- Combined read register commit theorem -/
theorem readReg_commit (env : RegEnv R) (schedLog actLog : InterpLog R) (port : Port) (r : reg_t) :
    schedLog.mayRead port r = true →
    readReg R env schedLog actLog port r =
    readReg R (commitUpdate env schedLog) .empty actLog port r := by
  intro hmay
  cases port with
  | p0 => exact readReg_p0_commit R env schedLog actLog r hmay
  | p1 => exact readReg_p1_commit R env schedLog actLog r hmay

end ReadRegCommit

/-! ## General ReadReg Commit Properties -/

section ReadRegCommitGeneral

variable {reg_t ext_fn_t : Type} [DecidableEq reg_t]
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Helper: if mayRead (sl.append sl') P0 r, then sl' has no writes to r -/
theorem latestWrite_sl'_none_of_mayRead_p0 (sl sl' : InterpLog R) (r : reg_t) :
    (sl.append sl').mayRead .p0 r = true →
    sl'.latestWrite r = none := by
  intro hmay
  unfold SimpleLog.mayRead at hmay
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmay
  obtain ⟨hno0, hno1⟩ := hmay
  -- From log_existsb_app: (sl.append sl').existsb f = sl.existsb f || sl'.existsb f
  simp only [existsb_append, Bool.or_eq_false_iff] at hno0 hno1
  obtain ⟨_, hsl'_no0⟩ := hno0
  obtain ⟨_, hsl'_no1⟩ := hno1
  -- sl' has no write0 or write1 entries
  unfold SimpleLog.latestWrite
  rw [List.findSome?_eq_none_iff]
  intro e he
  unfold SimpleLog.existsb at hsl'_no0 hsl'_no1
  unfold isWrite0 at hsl'_no0
  unfold isWrite1 at hsl'_no1
  simp only [List.any_eq_false, Bool.and_eq_true] at hsl'_no0 hsl'_no1
  have hno0' := hsl'_no0 e he
  have hno1' := hsl'_no1 e he
  by_cases hkind : (e.kind == LogEntryKind.write) = true
  · -- e.kind == write, but can't be at p0 or p1
    cases hp : e.port with
    | p0 =>
      have hport0 : (e.port == Port.p0) = true := by rw [hp]; rfl
      exact absurd ⟨hkind, hport0⟩ hno0'
    | p1 =>
      have hport1 : (e.port == Port.p1) = true := by rw [hp]; rfl
      exact absurd ⟨hkind, hport1⟩ hno1'
  · -- e.kind ≠ write
    have hbeq : (e.kind == LogEntryKind.write) = false := by
      cases h : (e.kind == LogEntryKind.write) with
      | true => exact absurd h hkind
      | false => rfl
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]

/-- Helper: if mayRead (sl.append sl') P1 r, then sl' has no write1 entries -/
theorem latestWrite1_sl'_none_of_mayRead_p1 (sl sl' : InterpLog R) (r : reg_t) :
    (sl.append sl').mayRead .p1 r = true →
    sl'.existsb r isWrite1 = false := by
  intro hmay
  unfold SimpleLog.mayRead at hmay
  simp only [Bool.not_eq_true'] at hmay
  simp only [existsb_append, Bool.or_eq_false_iff] at hmay
  exact hmay.2

/-- Helper: log append is associative -/
@[grind] theorem log_append_assoc (l1 l2 l3 : SimpleLog V) :
    (l1.append l2).append l3 = l1.append (l2.append l3) := by
  unfold SimpleLog.append
  simp [List.append_assoc]

/-- General read register commit: relates reading from (sl.append sl') to reading from sl after commit -/
theorem readReg_commit_general (env : RegEnv R) (sl sl' actLog : InterpLog R) (port : Port) (r : reg_t) :
    (sl.append sl').mayRead port r = true →
    readReg R env (sl.append sl') actLog port r =
    readReg R (commitUpdate env sl') sl actLog port r := by
  intro hmay
  cases port with
  | p0 =>
    -- Port 0: LHS = env r, RHS = commitUpdate env sl' r
    -- Need to show env r = commitUpdate env sl' r
    -- Since mayRead P0 passed, sl' has no writes, so commitUpdate env sl' r = env r
    unfold readReg
    have hnowrite := latestWrite_sl'_none_of_mayRead_p0 R sl sl' r hmay
    unfold commitUpdate
    simp [hnowrite]
  | p1 =>
    -- Port 1: LHS = (actLog.append (sl.append sl')).latestWrite0 r or env r
    --         RHS = (actLog.append sl).latestWrite0 r or commitUpdate env sl' r
    unfold readReg
    -- Using associativity: actLog.append (sl.append sl') = (actLog.append sl).append sl'
    have hassoc : actLog.append (sl.append sl') = (actLog.append sl).append sl' := by
      unfold SimpleLog.append
      simp [List.append_assoc]
    rw [hassoc, latestWrite0_append]
    -- LHS = ((actLog.append sl).latestWrite0 r).or (sl'.latestWrite0 r) or env r
    -- RHS = (actLog.append sl).latestWrite0 r or commitUpdate env sl' r
    -- where commitUpdate env sl' r = sl'.latestWrite r or env r
    have hno1 := latestWrite1_sl'_none_of_mayRead_p1 R sl sl' r hmay
    have heq : sl'.latestWrite r = sl'.latestWrite0 r := by
      apply latestWrite_eq_latestWrite0_of_no_write1
      exact hno1
    unfold commitUpdate
    rw [heq]
    -- Now both sides are: (actLog.append sl).latestWrite0 r .or sl'.latestWrite0 r .getD env r
    cases h1 : (actLog.append sl).latestWrite0 r with
    | some v =>
      simp only [Option.or, h1, Option.getD_some]
    | none =>
      simp only [Option.or, h1, Option.getD_none]
      cases h2 : sl'.latestWrite0 r with
      | some v => simp only [Option.getD_some]
      | none => simp only [Option.getD_none]

end ReadRegCommitGeneral

/-! ## MayRead/MayWrite Commit Properties -/

section MayReadWriteCommit

variable {reg_t : Type} [DecidableEq reg_t]
variable {V : reg_t → Type}

/-- mayRead with empty schedLog is always true for both ports -/
@[grind] theorem mayRead_empty (port : Port) (r : reg_t) :
    (SimpleLog.empty (R := V)).mayRead port r = true := by
  cases port <;> simp [SimpleLog.mayRead, SimpleLog.existsb, SimpleLog.empty]

/-- If schedLog.mayRead port r, then empty.mayRead port r (trivially true) -/
theorem mayRead_commit_impl (schedLog : SimpleLog V) (port : Port) (r : reg_t) :
    schedLog.mayRead port r = true →
    (SimpleLog.empty (R := V)).mayRead port r = true := by
  intro _
  exact mayRead_empty port r

/-- mayWrite with empty schedLog depends only on actLog -/
@[grind] theorem mayWrite_empty (actLog : SimpleLog V) (port : Port) (r : reg_t) :
    (SimpleLog.empty (R := V)).mayWrite actLog port r = actLog.mayWrite .empty port r := by
  simp [SimpleLog.mayWrite, SimpleLog.append, SimpleLog.empty, SimpleLog.existsb]

end MayReadWriteCommit

end Koika
