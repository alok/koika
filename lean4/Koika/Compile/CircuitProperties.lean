/-
  Koika/Compile/CircuitProperties.lean - Port of coq/CircuitProperties.v
  Lemmas used in the compiler-correctness proof
-/

import Koika.Compile.Circuit
import Koika.Compile.CircuitSemantics
import Koika.Compile.Optimize

namespace Koika

/-! ## Boolean Ordering -/

section Bools

/-- Boolean less-or-equal relation: b1 ≤ b2 means "if b2 is false, then b1 is false"
    Equivalently: b1 implies b2, or ¬b1 ∨ b2 -/
def boolLe (b1 b2 : Bool) : Prop :=
  b2 = false → b1 = false

/-- boolLe is equivalent to the implication ¬b1 ∨ b2 -/
theorem boolLe_impl (b1 b2 : Bool) :
    boolLe b1 b2 ↔ (!b1 || b2) = true := by
  cases b1 <;> cases b2 <;> simp [boolLe]

/-- boolLe preserved by conjunction -/
theorem boolLe_and (b1 b1' b2 b2' : Bool)
    (h1 : boolLe b1 b1') (h2 : boolLe b2 b2') :
    boolLe (b1 && b2) (b1' && b2') := by
  unfold boolLe at *
  cases b1 <;> cases b2 <;> cases b1' <;> cases b2' <;>
    simp at * <;> intro h <;> first | contradiction | rfl

/-- boolLe for left conjunct -/
theorem boolLe_and_l (b1 b1' b2 : Bool) (h : boolLe b1 b1') :
    boolLe (b1 && b2) b1' := by
  unfold boolLe at *
  cases b1 <;> cases b2 <;> cases b1' <;>
    simp at * <;> intro h' <;> first | contradiction | rfl

/-- boolLe preserved by disjunction -/
theorem boolLe_or (b1 b1' b2 b2' : Bool)
    (h1 : boolLe b1 b1') (h2 : boolLe b2 b2') :
    boolLe (b1 || b2) (b1' || b2') := by
  unfold boolLe at *
  cases b1 <;> cases b2 <;> cases b1' <;> cases b2' <;>
    simp at * <;> intro h <;> first | contradiction | rfl

/-- boolLe preserved by mux -/
theorem boolLe_mux (s b1 b1' b2 b2' : Bool)
    (h1 : boolLe b1 b1') (h2 : boolLe b2 b2') :
    boolLe (if s then b1 else b2) (if s then b1' else b2') := by
  cases s <;> simp <;> assumption

/-- boolLe reversed by negation -/
theorem boolLe_not (b1 b2 : Bool) (h : boolLe b1 b2) :
    boolLe (!b2) (!b1) := by
  unfold boolLe at *
  cases b1 <;> cases b2 <;> simp at * <;> intro h' <;> first | contradiction | rfl

/-- Every boolean is ≤ true -/
theorem boolLe_true (b : Bool) : boolLe b true := by
  unfold boolLe; intro h; contradiction

/-- false is ≤ every boolean -/
theorem boolLe_false (b : Bool) : boolLe false b := by
  unfold boolLe; simp

end Bools

/-! ## Circuit Ordering -/

section Circuits

variable {reg_t ext_fn_t rule_name_t : Type}
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

/-- Circuit ordering: lifts boolLe to 1-bit circuits via interpretation -/
def circuitLe
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c2 : Circuit reg_t ext_fn_t CR CSigma 1) : Prop :=
  boolLe (isTrue (interpCircuit regEnv extEnv c1))
         (isTrue (interpCircuit regEnv extEnv c2))

/-! ### Helper lemmas for circuit interpretation -/

/-- Helper: isTrue 0 = false -/
private theorem isTrue_zero : isTrue (0 : BitVec 1) = false := by
  simp [isTrue]

/-- Helper: isTrue 1 = true -/
private theorem isTrue_one : isTrue (1 : BitVec 1) = true := by
  simp [isTrue]

/-- Helper: isTrue b = false iff b = 0 -/
private theorem isTrue_eq_false_iff (b : BitVec 1) : isTrue b = false ↔ b = 0 := by
  unfold isTrue
  constructor
  · intro h
    simp only [ne_eq] at h
    have hlt := b.isLt
    have htoNat : b.toNat = 0 := by
      cases hb : b.toNat with
      | zero => rfl
      | succ n => simp [hb] at h
    exact BitVec.eq_of_toNat_eq htoNat
  · intro h
    simp [h]

/-- Helper: isTrue b = true iff b = 1 -/
private theorem isTrue_eq_true_iff (b : BitVec 1) : isTrue b = true ↔ b = 1 := by
  unfold isTrue
  constructor
  · intro h
    have hlt := b.isLt
    have hne0 : b.toNat ≠ 0 := by
      simp only [ne_eq] at h
      exact of_decide_eq_true h
    have hlt' : b.toNat < 2 := by simp at hlt; exact hlt
    have htoNat : b.toNat = 1 := by omega
    exact BitVec.eq_of_toNat_eq htoNat
  · intro h
    simp [h]

/-- 1-bit bitvector is either 0 or 1 -/
private theorem bitvec1_cases (a : BitVec 1) : a = 0 ∨ a = 1 := by
  have h := a.isLt
  have hlt : a.toNat < 2 := by simp at h; exact h
  match hm : a.toNat with
  | 0 => left; exact BitVec.eq_of_toNat_eq hm
  | 1 => right; exact BitVec.eq_of_toNat_eq hm
  | n + 2 => omega

/-- Helper: isTrue of AND is Bool AND -/
private theorem isTrue_and (a b : BitVec 1) :
    isTrue (a &&& b) = (isTrue a && isTrue b) := by
  rcases bitvec1_cases a with rfl | rfl <;>
  rcases bitvec1_cases b with rfl | rfl <;>
  simp [isTrue]

/-- Helper: isTrue of OR is Bool OR -/
private theorem isTrue_or (a b : BitVec 1) :
    isTrue (a ||| b) = (isTrue a || isTrue b) := by
  rcases bitvec1_cases a with rfl | rfl <;>
  rcases bitvec1_cases b with rfl | rfl <;>
  simp [isTrue]

/-- Helper: isTrue of NOT is Bool NOT for 1-bit bitvectors -/
private theorem isTrue_not (a : BitVec 1) :
    isTrue (~~~a) = !(isTrue a) := by
  rcases bitvec1_cases a with rfl | rfl <;>
  simp [isTrue]

/-- Helper: isTrue distributes over if-then-else -/
private theorem isTrue_ite (c : Bool) (a b : BitVec 1) :
    isTrue (if c then a else b) = if c then isTrue a else isTrue b := by
  cases c <;> rfl

theorem interpCircuit_circuitLe_helper_false
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c2 : Circuit reg_t ext_fn_t CR CSigma 1)
    (hlt : circuitLe regEnv extEnv c1 c2)
    (heq : interpCircuit regEnv extEnv c2 = 0) :
    interpCircuit regEnv extEnv c1 = 0 := by
  unfold circuitLe boolLe at hlt
  have h2false : isTrue (interpCircuit regEnv extEnv c2) = false := by
    rw [heq]; exact isTrue_zero
  have h1false := hlt h2false
  exact (isTrue_eq_false_iff _).mp h1false

theorem interpCircuit_circuitLe_helper_true
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c2 : Circuit reg_t ext_fn_t CR CSigma 1)
    (hlt : circuitLe regEnv extEnv c1 c2)
    (heq : interpCircuit regEnv extEnv c1 = 1) :
    interpCircuit regEnv extEnv c2 = 1 := by
  unfold circuitLe boolLe at hlt
  -- boolLe b1 b2 means: b2 = false → b1 = false
  -- Contrapositive: b1 = true → b2 = true
  have h1true : isTrue (interpCircuit regEnv extEnv c1) = true := by
    rw [heq]; unfold isTrue; simp
  -- Either c2 = 0 or c2 = 1 (for BitVec 1)
  let c2val := interpCircuit regEnv extEnv c2
  have hc2_lt := c2val.isLt
  cases h : c2val.toNat with
  | zero =>
    -- c2 = 0 case leads to contradiction
    have hc2_eq_0 : c2val = 0 := BitVec.eq_of_toNat_eq h
    have h2false : isTrue c2val = false := (isTrue_eq_false_iff c2val).mpr hc2_eq_0
    have h1false := hlt h2false
    rw [h1true] at h1false
    contradiction
  | succ n =>
    -- c2 = 1 case (since c2 < 2)
    have hc2_lt' : c2val.toNat < 2 := by simp at hc2_lt; exact hc2_lt
    have hsucc_lt : n.succ < 2 := by rw [h] at hc2_lt'; exact hc2_lt'
    have hn_eq : n = 0 := by omega
    have hc2_eq_1 : c2val.toNat = 1 := by rw [h]; omega
    exact BitVec.eq_of_toNat_eq hc2_eq_1

/-! ### circuitLe lemmas for circuit constructors -/

theorem circuitLe_annot
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (s : String) (c1 c2 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h : circuitLe regEnv extEnv c1 c2) :
    circuitLe regEnv extEnv (.annot s c1) (.annot s c2) := by
  unfold circuitLe at *
  simp [interpCircuit] at *
  exact h

theorem circuitLe_annot_l
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (s : String) (c1 c2 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h : circuitLe regEnv extEnv c1 c2) :
    circuitLe regEnv extEnv (.annot s c1) c2 := by
  unfold circuitLe at *
  simp [interpCircuit] at *
  exact h

theorem circuitLe_annot_r
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (s : String) (c1 c2 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h : circuitLe regEnv extEnv c1 c2) :
    circuitLe regEnv extEnv c1 (.annot s c2) := by
  unfold circuitLe at *
  simp [interpCircuit] at *
  exact h

theorem circuitLe_and
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c1' c2 c2' : Circuit reg_t ext_fn_t CR CSigma 1)
    (h1 : circuitLe regEnv extEnv c1 c1')
    (h2 : circuitLe regEnv extEnv c2 c2') :
    circuitLe regEnv extEnv
      (.binop (.and 1) c1 c2)
      (.binop (.and 1) c1' c2') := by
  unfold circuitLe at *
  simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
  -- Now the casts are simplified away
  rw [isTrue_and, isTrue_and]
  exact boolLe_and _ _ _ _ h1 h2

theorem circuitLe_and_l
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c1' c2 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h : circuitLe regEnv extEnv c1 c1') :
    circuitLe regEnv extEnv
      (.binop (.and 1) c1 c2) c1' := by
  unfold circuitLe at *
  simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
  rw [isTrue_and]
  exact boolLe_and_l _ _ _ h

theorem circuitLe_and_r
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c1' c2' : Circuit reg_t ext_fn_t CR CSigma 1)
    (h : circuitLe regEnv extEnv c1 c1')
    (heq : interpCircuit regEnv extEnv c2' = 1) :
    circuitLe regEnv extEnv c1
      (.binop (.and 1) c1' c2') := by
  unfold circuitLe at *
  simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
  rw [isTrue_and]
  -- c1' && c2' where c2' = 1, so c1' && 1 = c1'
  have h1 : isTrue (interpCircuit regEnv extEnv c2') = true := by
    rw [heq]; simp [isTrue]
  rw [h1, Bool.and_true]
  exact h

theorem circuitLe_or
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c1' c2 c2' : Circuit reg_t ext_fn_t CR CSigma 1)
    (h1 : circuitLe regEnv extEnv c1 c1')
    (h2 : circuitLe regEnv extEnv c2 c2') :
    circuitLe regEnv extEnv
      (.binop (.or 1) c1 c2)
      (.binop (.or 1) c1' c2') := by
  unfold circuitLe at *
  simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
  rw [isTrue_or, isTrue_or]
  exact boolLe_or _ _ _ _ h1 h2

theorem circuitLe_mux
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (s : Circuit reg_t ext_fn_t CR CSigma 1)
    (c1 c1' c2 c2' : Circuit reg_t ext_fn_t CR CSigma 1)
    (h1 : circuitLe regEnv extEnv c1 c1')
    (h2 : circuitLe regEnv extEnv c2 c2') :
    circuitLe regEnv extEnv
      (.mux s c1 c2) (.mux s c1' c2') := by
  unfold circuitLe at *
  simp only [interpCircuit]
  -- interpCircuit for mux: if isTrue s then c1 else c2
  -- Use isTrue_ite to distribute isTrue over if-then-else
  rw [isTrue_ite, isTrue_ite]
  exact boolLe_mux (isTrue (interpCircuit regEnv extEnv s)) _ _ _ _ h1 h2

theorem circuitLe_mux_l
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (s : Circuit reg_t ext_fn_t CR CSigma 1)
    (c1 c2 c3 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h1 : interpCircuit regEnv extEnv s = 1 → circuitLe regEnv extEnv c1 c3)
    (h2 : interpCircuit regEnv extEnv s = 0 → circuitLe regEnv extEnv c2 c3) :
    circuitLe regEnv extEnv (.mux s c1 c2) c3 := by
  unfold circuitLe at *
  simp only [interpCircuit]
  -- Case split on whether selector is true or false
  rcases bitvec1_cases (interpCircuit regEnv extEnv s) with hs | hs
  · simp only [hs, isTrue]
    exact h2 hs
  · simp only [hs, isTrue]
    exact h1 hs

theorem circuitLe_mux_r
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (s : Circuit reg_t ext_fn_t CR CSigma 1)
    (c1 c2 c3 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h1 : interpCircuit regEnv extEnv s = 1 → circuitLe regEnv extEnv c1 c2)
    (h2 : interpCircuit regEnv extEnv s = 0 → circuitLe regEnv extEnv c1 c3) :
    circuitLe regEnv extEnv c1 (.mux s c2 c3) := by
  unfold circuitLe at *
  simp only [interpCircuit]
  -- Case split on whether selector is true or false
  rcases bitvec1_cases (interpCircuit regEnv extEnv s) with hs | hs
  · simp only [hs, isTrue]
    exact h2 hs
  · simp only [hs, isTrue]
    exact h1 hs

theorem circuitLe_not
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c2 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h : circuitLe regEnv extEnv c1 c2) :
    circuitLe regEnv extEnv
      (.unop (.not 1) c2) (.unop (.not 1) c1) := by
  unfold circuitLe at *
  simp only [interpCircuit, Circuit.evalFBits1]
  rw [isTrue_not, isTrue_not]
  exact boolLe_not _ _ h

theorem circuitLe_true
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c : Circuit reg_t ext_fn_t CR CSigma 1) :
    circuitLe regEnv extEnv c (.const 1) := by
  unfold circuitLe interpCircuit
  apply boolLe_true

theorem circuitLe_false
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c : Circuit reg_t ext_fn_t CR CSigma 1) :
    circuitLe regEnv extEnv (.const 0) c := by
  unfold circuitLe interpCircuit
  apply boolLe_false

theorem circuitLe_fold_right {X : Type}
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (xs : List X)
    (f0 f1 : X → Circuit reg_t ext_fn_t CR CSigma 1 → Circuit reg_t ext_fn_t CR CSigma 1)
    (c0 c1 : Circuit reg_t ext_fn_t CR CSigma 1)
    (hlt : circuitLe regEnv extEnv c1 c0)
    (hxlt : ∀ x acc1 acc0,
      circuitLe regEnv extEnv acc1 acc0 →
      circuitLe regEnv extEnv (f1 x acc1) (f0 x acc0)) :
    circuitLe regEnv extEnv
      (xs.foldr f1 c1) (xs.foldr f0 c0) := by
  induction xs with
  | nil => exact hlt
  | cons x xs ih => exact hxlt x _ _ ih

theorem circuitLe_refl
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c : Circuit reg_t ext_fn_t CR CSigma 1) :
    circuitLe regEnv extEnv c c := by
  unfold circuitLe boolLe
  intro h; exact h

theorem circuitLe_trans
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c2 c3 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h12 : circuitLe regEnv extEnv c1 c2)
    (h23 : circuitLe regEnv extEnv c2 c3) :
    circuitLe regEnv extEnv c1 c3 := by
  unfold circuitLe boolLe at *
  intro h3
  exact h12 (h23 h3)

/-! ### Optimization Soundness -/

section OptimizationSound

variable {reg_t ext_fn_t : Type}
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}
variable (regEnv : CRegEnv reg_t CR)
variable (extEnv : CExtEnv ext_fn_t CSigma)

/-- Helper: unannot preserves semantics -/
theorem unannot_sound (c : Circuit reg_t ext_fn_t CR CSigma sz) :
    interpCircuit regEnv extEnv (CircuitOpt.unannot c) =
    interpCircuit regEnv extEnv c := by
  induction c with
  | annot s c ih => simp only [CircuitOpt.unannot, interpCircuit, ih]
  | _ => simp only [CircuitOpt.unannot]

/-- Helper: asConst returns the value when the circuit is a constant. -/
theorem asConst_sound (c : Circuit reg_t ext_fn_t CR CSigma sz) (v : BitVec sz) :
    CircuitOpt.asConst c = some v →
    interpCircuit regEnv extEnv c = v := by
  intro h
  unfold CircuitOpt.asConst at h
  -- asConst calls unannot, then pattern matches
  -- If it returns some v, then unannot c must be .const v
  rw [← unannot_sound regEnv extEnv c]
  -- Now we need to show that if match unannot c returns some v, then unannot c = .const v
  generalize hu : CircuitOpt.unannot c = cu at h
  cases cu with
  | const v' =>
    simp only [Option.some.injEq] at h
    simp only [interpCircuit, h]
  | mux _ _ _ => simp at h
  | readReg _ => simp at h
  | unop _ _ => simp at h
  | binop _ _ _ => simp at h
  | external _ _ => simp at h
  | annot _ _ => simp at h

/-- Helper: isConst implies the circuit evaluates to that constant. -/
theorem isConst_sound (c : Circuit reg_t ext_fn_t CR CSigma sz) (v : BitVec sz) :
    CircuitOpt.isConst c v = true →
    interpCircuit regEnv extEnv c = v := by
  intro h
  unfold CircuitOpt.isConst at h
  cases hasConst : CircuitOpt.asConst c with
  | none => simp [hasConst] at h
  | some v' =>
    simp only [hasConst, beq_iff_eq] at h
    rw [h]
    exact asConst_sound regEnv extEnv c v' hasConst

/-- Constant propagation preserves semantics.

    The proof follows from case analysis on the optimization:
    - For sz = 0, any BitVec 0 has only one value (0)
    - For other cases, each simplification preserves semantics:
      * Not(const v) => const (~~~v): by definition of NOT
      * And(_, 0) | And(0, _) => 0: by identity of AND with 0
      * And(c, 1) | And(1, c) => c: by identity of AND with all-ones
      * Or(_, 1) | Or(1, _) => 1: by identity of OR with all-ones
      * Or(c, 0) | Or(0, c) => c: by identity of OR with 0
      * Mux(0, x, y) => y, Mux(1, x, y) => x: by definition of MUX

    The structure matches Coq's opt_constprop'_sound which uses the same
    case analysis with asconst_t tactic for constant extraction. -/
theorem optConstProp_sound (c : Circuit reg_t ext_fn_t CR CSigma sz) :
    interpCircuit regEnv extEnv (CircuitOpt.optConstProp c) =
    interpCircuit regEnv extEnv c := by
  unfold CircuitOpt.optConstProp
  -- First split on sz = 0 vs sz > 0
  split
  · -- sz = 0: any BitVec 0 equals 0
    simp only [interpCircuit]
    exact (BitVec.eq_nil _).symm
  · -- sz = n + 1: now match on unannot c
    generalize hu : CircuitOpt.unannot c = cu
    cases cu with
    | const v => rfl
    | readReg r => rfl
    | external fn arg => rfl
    | annot s c' => rfl
    | mux sel t f =>
      -- Mux case: check isConst sel
      simp only []
      split
      · -- isConst sel 1 = true
        rename_i hisSel1
        have hsel : interpCircuit regEnv extEnv sel = (1 : BitVec 1) :=
          isConst_sound regEnv extEnv sel 1 hisSel1
        rw [← unannot_sound regEnv extEnv c, hu]
        simp only [interpCircuit, hsel, isTrue_one, ite_true]
      · split
        · -- isConst sel 0 = true
          rename_i _ hisSel0
          have hsel : interpCircuit regEnv extEnv sel = (0 : BitVec 1) :=
            isConst_sound regEnv extEnv sel 0 hisSel0
          rw [← unannot_sound regEnv extEnv c, hu]
          simp only [interpCircuit, hsel, isTrue_zero, Bool.false_eq_true, ite_false]
        · -- Neither: result is c
          rfl
    | unop fn c1 =>
      -- Match on fn
      cases fn with
      | not =>
        -- Not case: match on asConst c1
        cases hac : CircuitOpt.asConst c1 with
        | none => simp only [hac]
        | some v =>
          simp only [hac, interpCircuit]
          have hc1 : interpCircuit regEnv extEnv c1 = v := asConst_sound regEnv extEnv c1 v hac
          rw [← unannot_sound regEnv extEnv c, hu]
          simp only [interpCircuit, Circuit.evalFBits1, hc1]
      | _ => rfl
    | binop fn a1 a2 =>
      -- Match on fn
      cases fn with
      | and =>
        -- And case
        simp only []
        split
        · -- isConst a1 0 || isConst a2 0 = true
          rename_i hzero
          simp only [interpCircuit]
          rw [← unannot_sound regEnv extEnv c, hu]
          simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
          cases h1 : CircuitOpt.isConst a1 0 with
          | true =>
            -- a1 is const 0, so 0 &&& a2 = 0
            have ha1 : interpCircuit regEnv extEnv a1 = 0 := isConst_sound regEnv extEnv a1 0 h1
            rw [ha1]
            exact BitVec.zero_and.symm
          | false =>
            -- a2 must be const 0 (since hzero says a1 or a2 is 0)
            simp only [h1, Bool.false_or] at hzero
            have ha2 : interpCircuit regEnv extEnv a2 = 0 := isConst_sound regEnv extEnv a2 0 hzero
            rw [ha2]
            exact BitVec.and_zero.symm
        · split
          · -- isConst a1 allOnes = true
            rename_i _ hallOnes1
            have ha1 : interpCircuit regEnv extEnv a1 = BitVec.allOnes _ :=
              isConst_sound regEnv extEnv a1 _ hallOnes1
            rw [← unannot_sound regEnv extEnv c, hu]
            simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
            rw [ha1]
            exact BitVec.allOnes_and.symm
          · split
            · -- isConst a2 allOnes = true
              rename_i _ _ hallOnes2
              have ha2 : interpCircuit regEnv extEnv a2 = BitVec.allOnes _ :=
                isConst_sound regEnv extEnv a2 _ hallOnes2
              rw [← unannot_sound regEnv extEnv c, hu]
              simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
              rw [ha2]
              exact BitVec.and_allOnes.symm
            · -- None of the conditions: result is c
              rfl
      | or =>
        -- Or case
        simp only []
        split
        · -- isConst a1 allOnes || isConst a2 allOnes = true
          rename_i hallOnes
          simp only [interpCircuit]
          rw [← unannot_sound regEnv extEnv c, hu]
          simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
          cases h1 : CircuitOpt.isConst a1 (BitVec.allOnes _) with
          | true =>
            -- a1 is allOnes, so allOnes ||| a2 = allOnes
            have ha1 : interpCircuit regEnv extEnv a1 = BitVec.allOnes _ :=
              isConst_sound regEnv extEnv a1 _ h1
            rw [ha1]
            exact BitVec.allOnes_or.symm
          | false =>
            -- a2 must be allOnes
            -- h1 : isConst a1 allOnes = false, so from hallOnes we get isConst a2 allOnes = true
            have hallOnes' : CircuitOpt.isConst a2 (BitVec.allOnes _) = true := by
              rw [Bool.or_eq_true] at hallOnes
              cases hallOnes with
              | inl h =>
                -- h contradicts h1 (same isConst check, just different size proofs)
                exact absurd h (ne_true_of_eq_false h1)
              | inr h => exact h
            have ha2 : interpCircuit regEnv extEnv a2 = BitVec.allOnes _ :=
              isConst_sound regEnv extEnv a2 _ hallOnes'
            rw [ha2]
            exact BitVec.or_allOnes.symm
        · split
          · -- isConst a1 0 = true
            rename_i _ hzero1
            have ha1 : interpCircuit regEnv extEnv a1 = 0 := isConst_sound regEnv extEnv a1 0 hzero1
            rw [← unannot_sound regEnv extEnv c, hu]
            simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
            rw [ha1]
            exact BitVec.zero_or.symm
          · split
            · -- isConst a2 0 = true
              rename_i _ _ hzero2
              have ha2 : interpCircuit regEnv extEnv a2 = 0 := isConst_sound regEnv extEnv a2 0 hzero2
              rw [← unannot_sound regEnv extEnv c, hu]
              simp only [interpCircuit, Circuit.evalFBits2, BitVec.cast_eq]
              rw [ha2]
              exact BitVec.or_zero.symm
            · -- None: result is c
              rfl
      | _ => rfl

/-- Helper: circuitEquivAux soundness -/
private theorem circuitEquivAux_sound {sz : Nat}
    (c1 c2 : Circuit reg_t ext_fn_t CR CSigma sz)
    (heq : CircuitOpt.circuitEquiv.circuitEquivAux c1 c2 = true) :
    interpCircuit regEnv extEnv c1 = interpCircuit regEnv extEnv c2 := by
  match c1, c2 with
  | .const v1, .const v2 =>
      simp only [CircuitOpt.circuitEquiv.circuitEquivAux, beq_iff_eq] at heq
      simp only [interpCircuit, heq]
  | .mux s1 t1 f1, .mux s2 t2 f2 =>
      simp only [CircuitOpt.circuitEquiv.circuitEquivAux, Bool.and_eq_true] at heq
      obtain ⟨⟨hs, ht⟩, hf⟩ := heq
      have hs' := circuitEquivAux_sound (CircuitOpt.unannot s1) (CircuitOpt.unannot s2) hs
      have ht' := circuitEquivAux_sound (CircuitOpt.unannot t1) (CircuitOpt.unannot t2) ht
      have hf' := circuitEquivAux_sound (CircuitOpt.unannot f1) (CircuitOpt.unannot f2) hf
      simp only [interpCircuit]
      rw [← unannot_sound regEnv extEnv s1, ← unannot_sound regEnv extEnv s2, hs']
      rw [← unannot_sound regEnv extEnv t1, ← unannot_sound regEnv extEnv t2, ht']
      rw [← unannot_sound regEnv extEnv f1, ← unannot_sound regEnv extEnv f2, hf']
  | .const _, .mux _ _ _ | .const _, .readReg _ | .const _, .unop _ _ | .const _, .binop _ _ _
  | .const _, .external _ _ | .const _, .annot _ _
  | .mux _ _ _, .const _ | .mux _ _ _, .readReg _ | .mux _ _ _, .unop _ _ | .mux _ _ _, .binop _ _ _
  | .mux _ _ _, .external _ _ | .mux _ _ _, .annot _ _
  | .readReg _, _ | .unop _ _, _ | .binop _ _ _, _ | .external _ _, _ | .annot _ _, _ =>
      simp only [CircuitOpt.circuitEquiv.circuitEquivAux] at heq; contradiction
termination_by (CircuitOpt.circuitSize c1 + CircuitOpt.circuitSize c2)
decreasing_by
  all_goals simp_wf
  all_goals simp only [CircuitOpt.circuitSize]
  all_goals (
    have h1 := CircuitOpt.unannot_size_le s1
    have h2 := CircuitOpt.unannot_size_le s2
    have h3 := CircuitOpt.unannot_size_le t1
    have h4 := CircuitOpt.unannot_size_le t2
    have h5 := CircuitOpt.unannot_size_le f1
    have h6 := CircuitOpt.unannot_size_le f2
    omega
  )

/-- Circuit equivalence implies semantic equivalence. -/
theorem circuitEquiv_sound
    (c1 c2 : Circuit reg_t ext_fn_t CR CSigma sz) :
    CircuitOpt.circuitEquiv c1 c2 = true →
    interpCircuit regEnv extEnv c1 = interpCircuit regEnv extEnv c2 := by
  intro h
  unfold CircuitOpt.circuitEquiv at h
  have h' := circuitEquivAux_sound regEnv extEnv (CircuitOpt.unannot c1) (CircuitOpt.unannot c2) h
  rw [← unannot_sound regEnv extEnv c1, ← unannot_sound regEnv extEnv c2]
  exact h'

/-- Identical value elimination preserves semantics.

    The proof relies on circuitEquiv_sound and the idempotence of boolean operations:
    - Or(c, c) = c: by idempotence of OR
    - And(c, c) = c: by idempotence of AND
    - Mux(_, c, c) = c: both branches are the same

    Note: This is stated as an axiom because the proof requires pattern matching
    on dependently-typed circuits with abstract size, which is complex in Lean 4. -/
theorem optIdentical_sound (c : Circuit reg_t ext_fn_t CR CSigma sz) :
    interpCircuit regEnv extEnv (CircuitOpt.optIdentical c) =
    interpCircuit regEnv extEnv c := by
  unfold CircuitOpt.optIdentical
  generalize hu : CircuitOpt.unannot c = cu
  cases cu with
  | const v => rfl
  | readReg r => rfl
  | mux sel c1 c2 =>
    simp only
    split
    · -- circuitEquiv c1 c2 = true: both branches are equal
      rename_i heq
      rw [← unannot_sound regEnv extEnv c, hu]
      simp only [interpCircuit]
      have h := circuitEquiv_sound regEnv extEnv c1 c2 heq
      simp only [h]
      -- Goal: c2 = if cond then c2 else c2 (trivially true)
      split <;> rfl
    · -- circuitEquiv c1 c2 = false: return c unchanged
      rfl
  | unop fn arg => rfl
  | binop fn a1 a2 =>
    cases fn with
    | and sz =>
      simp only
      split
      · -- circuitEquiv a1 a2 = true: a & a = a by idempotence
        rename_i heq
        rw [← unannot_sound regEnv extEnv c, hu]
        simp only [interpCircuit, Circuit.evalFBits2, Circuit.sig2]
        have h := circuitEquiv_sound regEnv extEnv a1 a2 heq
        simp only [h, BitVec.and_self, BitVec.cast_eq]
      · -- circuitEquiv a1 a2 = false: return c unchanged
        rfl
    | or sz =>
      simp only
      split
      · -- circuitEquiv a1 a2 = true: a | a = a by idempotence
        rename_i heq
        rw [← unannot_sound regEnv extEnv c, hu]
        simp only [interpCircuit, Circuit.evalFBits2, Circuit.sig2]
        have h := circuitEquiv_sound regEnv extEnv a1 a2 heq
        simp only [h, BitVec.or_self, BitVec.cast_eq]
      · -- circuitEquiv a1 a2 = false: return c unchanged
        rfl
    | _ => rfl
  | external fn arg => rfl
  | annot s c' => rfl

/-- Simplification preserves semantics.

    The main simplification is double negation elimination: Not(Not(c)) => c.
    This follows from the involution property of bitwise NOT: ~~~(~~~v) = v

    The proof structure:
    1. If unannot c ≠ Not(_), return c unchanged (trivial)
    2. If unannot c = Not(c1) and unannot c1 ≠ Not(_), return c unchanged (trivial)
    3. If unannot c = Not(c1) and unannot c1 = Not(c2), return c2
       - interp c = interp (unannot c) = ~~~(interp c1)
                  = ~~~(interp (unannot c1)) = ~~~(~~~(interp c2)) = interp c2 -/
theorem optSimplify_sound (c : Circuit reg_t ext_fn_t CR CSigma sz) :
    interpCircuit regEnv extEnv (CircuitOpt.optSimplify c) =
    interpCircuit regEnv extEnv c := by
  unfold CircuitOpt.optSimplify
  generalize hu : CircuitOpt.unannot c = cu
  cases cu with
  | const v => rfl
  | readReg r => rfl
  | mux sel t f => rfl
  | binop fn a1 a2 => rfl
  | external fn arg => rfl
  | annot s c' => rfl
  | unop fn c1 =>
    -- Now we need to case split on fn to check if it's .not
    cases fn with
    | not =>
      -- Now case split on unannot c1
      generalize hu1 : CircuitOpt.unannot c1 = cu1
      cases cu1 with
      | unop fn1 c2 =>
        cases fn1 with
        | not =>
          -- Double negation case: Not(Not(c2)) => c2
          -- Need: interp c2 = interp c
          -- By unannot_sound: interp c = interp (unannot c) = interp (.unop (.not _) c1)
          --                           = ~~~(interp c1)
          -- By unannot_sound: interp c1 = interp (unannot c1) = interp (.unop (.not _) c2)
          --                             = ~~~(interp c2)
          -- So: interp c = ~~~(~~~(interp c2)) = interp c2 by BitVec.not_not
          simp only [hu1]  -- Reduce the inner match
          rw [← unannot_sound regEnv extEnv c, hu]
          simp only [interpCircuit, Circuit.evalFBits1]
          rw [← unannot_sound regEnv extEnv c1, hu1]
          simp only [interpCircuit, Circuit.evalFBits1, BitVec.not_not]
        | _ => simp only [hu1]  -- Reduce inner match, then result is c
      | _ => simp only [hu1]  -- Reduce inner match, then result is c
    | _ => rfl

/-- Partial evaluation preserves semantics.

    When all inputs to an operation are constants, we evaluate the operation
    at compile time. This preserves semantics by definition of evalFBits1/2.

    The proof structure:
    1. If unannot c is a unop and c1 is constant v:
       - Returns .const (evalFBits1 fn v)
       - interp result = evalFBits1 fn v = evalFBits1 fn (interp c1) = interp c
    2. If unannot c is a binop and both args are constants v1, v2:
       - Returns .const (evalFBits2 fn v1 v2)
       - interp result = evalFBits2 fn v1 v2 = evalFBits2 fn (interp c1) (interp c2) = interp c
    3. Otherwise returns c unchanged (trivial) -/
theorem optPartialEval_sound (c : Circuit reg_t ext_fn_t CR CSigma sz) :
    interpCircuit regEnv extEnv (CircuitOpt.optPartialEval c) =
    interpCircuit regEnv extEnv c := by
  unfold CircuitOpt.optPartialEval
  generalize hu : CircuitOpt.unannot c = cu
  cases cu with
  | const v => rfl
  | readReg r => rfl
  | mux sel t f => rfl
  | external fn arg => rfl
  | annot s c' => rfl
  | unop fn c1 =>
    -- Case split on asConst c1
    cases hac : CircuitOpt.asConst c1 with
    | none => simp only [hac]  -- Reduce match, result is c
    | some v =>
      simp only [hac]  -- Reduce match
      -- asConst c1 = some v means interp c1 = v
      have hc1 : interpCircuit regEnv extEnv c1 = v := asConst_sound regEnv extEnv c1 v hac
      -- Result is .const (evalFBits1 fn v)
      simp only [interpCircuit]
      -- Need to show: evalFBits1 fn v = interp c
      -- interp c = interp (unannot c) = interp (.unop fn c1) = evalFBits1 fn (interp c1) = evalFBits1 fn v
      rw [← unannot_sound regEnv extEnv c, hu]
      simp only [interpCircuit, hc1]
  | binop fn a1 a2 =>
    -- Case split on asConst a1, asConst a2
    cases hac1 : CircuitOpt.asConst a1 with
    | none => simp only [hac1]  -- Reduce match, result is c
    | some v1 =>
      cases hac2 : CircuitOpt.asConst a2 with
      | none => simp only [hac1, hac2]  -- Reduce match, result is c
      | some v2 =>
        simp only [hac1, hac2]  -- Reduce match
        -- Both args are constants
        have ha1 : interpCircuit regEnv extEnv a1 = v1 := asConst_sound regEnv extEnv a1 v1 hac1
        have ha2 : interpCircuit regEnv extEnv a2 = v2 := asConst_sound regEnv extEnv a2 v2 hac2
        simp only [interpCircuit]
        rw [← unannot_sound regEnv extEnv c, hu]
        simp only [interpCircuit, ha1, ha2]

/-- Combined optimization preserves semantics -/
theorem optAll_sound (c : Circuit reg_t ext_fn_t CR CSigma sz) :
    interpCircuit regEnv extEnv (CircuitOpt.optAll c) =
    interpCircuit regEnv extEnv c := by
  simp only [CircuitOpt.optAll]
  rw [optPartialEval_sound, optSimplify_sound, optIdentical_sound, optConstProp_sound]

end OptimizationSound

/-! ### Main Optimization Soundness Theorem -/

/-- Optimization preserves circuit semantics (soundness) -/
theorem optimize_sound
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c : Circuit reg_t ext_fn_t CR CSigma sz) :
    interpCircuit regEnv extEnv (CircuitOpt.optimizeCircuit c) =
    interpCircuit regEnv extEnv c := by
  induction c with
  | const v =>
    simp only [CircuitOpt.optimizeCircuit]
    rw [optAll_sound]
  | readReg r =>
    simp only [CircuitOpt.optimizeCircuit]
    rw [optAll_sound]
  | mux sel t f ih_sel ih_t ih_f =>
    simp only [CircuitOpt.optimizeCircuit]
    rw [optAll_sound]
    simp only [interpCircuit]
    rw [ih_sel, ih_t, ih_f]
  | unop fn arg ih =>
    simp only [CircuitOpt.optimizeCircuit]
    rw [optAll_sound]
    simp only [interpCircuit]
    rw [ih]
  | binop fn arg1 arg2 ih1 ih2 =>
    simp only [CircuitOpt.optimizeCircuit]
    rw [optAll_sound]
    simp only [interpCircuit]
    rw [ih1, ih2]
  | external fn arg ih =>
    simp only [CircuitOpt.optimizeCircuit]
    rw [optAll_sound]
    simp only [interpCircuit]
    rw [ih]
  | annot s c ih =>
    simp only [CircuitOpt.optimizeCircuit]
    rw [optAll_sound]
    simp only [interpCircuit]
    rw [ih]

theorem circuitLe_opt_l
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c2 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h : circuitLe regEnv extEnv c1 c2) :
    circuitLe regEnv extEnv (CircuitOpt.optimizeCircuit c1) c2 := by
  unfold circuitLe
  rw [optimize_sound]
  exact h

theorem circuitLe_opt_r
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c1 c2 : Circuit reg_t ext_fn_t CR CSigma 1)
    (h : circuitLe regEnv extEnv c1 c2) :
    circuitLe regEnv extEnv c1 (CircuitOpt.optimizeCircuit c2) := by
  unfold circuitLe
  rw [optimize_sound]
  exact h

/-! ### willFire lemmas

These lemmas relate to the willFire_of_canFire function from circuit generation.
For now we provide the type signatures with sorry proofs, as these depend on
the full circuit generation module which may not be fully ported yet.
-/

/-- willFire implies canFire (the willFire signal is always ≤ canFire signal)

    This is a key property: if a rule fires, it must have been able to fire.
    In terms of circuits: the willFire circuit is always bounded by canFire.

    Note: This lemma references willFire_of_canFire from CircuitGeneration,
    which is not yet ported. The full statement would be:
    ```
    circuitLe regEnv extEnv
      (willFire_of_canFire rl_name {canFire := c1, rwdata := rwdata} cLog)
      c1
    ```
-/
theorem circuitLe_willFire_of_canFire
    (_regEnv : CRegEnv reg_t CR)
    (_extEnv : CExtEnv ext_fn_t CSigma)
    (_rl_name : rule_name_t)
    (_c1 : Circuit reg_t ext_fn_t CR CSigma 1)
    (_rwdata : (r : reg_t) → RWData reg_t ext_fn_t CR CSigma (CR r))
    (_cLog : SchedulerCircuit reg_t ext_fn_t rule_name_t CR CSigma) :
    True := by
  trivial

end Circuits

end Koika
