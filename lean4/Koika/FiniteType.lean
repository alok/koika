/-
  Koika/FiniteType.lean - Port of coq/FiniteType.v
  Finiteness typeclass for types with finitely many elements
-/

namespace Koika

/-! ## FiniteType Class -/

/-- A typeclass for types with finitely many elements.
    Provides an index function and a list of all elements,
    with proofs that the indexing is bijective. -/
class FiniteType (T : Type) where
  /-- Map each element to a unique natural number index -/
  finite_index : T → Nat
  /-- List containing all elements of the type -/
  finite_elements : List T
  /-- Every element appears in the list at its index -/
  finite_surjective : ∀ a : T, finite_elements[finite_index a]? = some a
  /-- The indices are unique (no duplicates in the mapped indices) -/
  finite_injective : (finite_elements.map finite_index).Nodup

/-- If l is Nodup and f is injective, then (l.map f) is Nodup -/
theorem List.nodup_map_of_nodup_injective {α β : Type} (f : α → β) (l : List α)
    (hinj : Function.Injective f) (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hfx
      rw [List.mem_map] at hfx
      obtain ⟨y, hy, hfy⟩ := hfx
      have hxy : x = y := hinj hfy.symm
      rw [hxy] at h
      exact h.1 hy
    · exact ih h.2

/-! ## Basic Properties -/

/-- The index function is injective: equal indices imply equal elements -/
@[grind] theorem finite_index_injective {T : Type} [FT : FiniteType T] :
    ∀ t1 t2, FT.finite_index t1 = FT.finite_index t2 → t1 = t2 := by
  intro t1 t2 h
  have h1 := FT.finite_surjective t1
  have h2 := FT.finite_surjective t2
  rw [h] at h1
  rw [h1] at h2
  cases h2
  rfl

/-- Helper lemma: if map f l is nodup and f is injective, then l is nodup -/
theorem List.nodup_of_nodup_map' {α β : Type} (f : α → β) (l : List α)
    (hf : ∀ a b, a ∈ l → b ∈ l → f a = f b → a = b) (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    constructor
    · intro hx
      have : f x ∈ xs.map f := by
        rw [List.mem_map]
        exact ⟨x, hx, rfl⟩
      exact h.1 this
    · apply ih
      · intro a b ha hb
        apply hf
        exact List.mem_cons_of_mem x ha
        exact List.mem_cons_of_mem x hb
      · exact h.2

/-- The finite_elements list has no duplicates -/
@[grind] theorem finite_nodup {T : Type} [FT : FiniteType T] :
    FT.finite_elements.Nodup := by
  apply List.nodup_of_nodup_map' FT.finite_index
  · intro a b _ _
    exact finite_index_injective a b
  · exact FT.finite_injective

/-! ## Helper: Increasing Lists -/

/-- Check if a list of natural numbers is strictly increasing -/
def increasing : List Nat → Bool
  | [] => true
  | [_] => true
  | n1 :: n2 :: rest => (n1 < n2) && increasing (n2 :: rest)

/-- Helper: elements in increasing list are pairwise distinct -/
theorem increasing_pairwise_lt : ∀ l, increasing l = true →
    l.Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons x xs ih =>
    cases xs with
    | nil => intro _; exact List.pairwise_singleton _ _
    | cons y ys =>
      simp only [increasing, Bool.and_eq_true, decide_eq_true_eq]
      intro ⟨hxy, hrest⟩
      have pw := ih hrest
      constructor
      · intro z hz
        cases hz with
        | head => exact hxy
        | tail _ hz' =>
          have : y < z := List.rel_of_pairwise_cons pw hz'
          omega
      · exact pw

/-- Pairwise less-than implies nodup -/
theorem pairwise_lt_nodup : ∀ l : List Nat, l.Pairwise (· < ·) → l.Nodup := by
  intro l hp
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons]
    constructor
    · intro hx
      have := List.rel_of_pairwise_cons hp hx
      omega
    · exact ih (List.Pairwise.tail hp)

/-- Strictly increasing lists have no duplicates -/
@[grind] theorem increasing_nodup : ∀ l, increasing l = true → l.Nodup := by
  intro l h
  have hp := increasing_pairwise_lt l h
  exact pairwise_lt_nodup l hp

/-! ## Instances for Common Types -/

/-- Bool has exactly 2 elements -/
instance : FiniteType Bool where
  finite_index := fun b => if b then 1 else 0
  finite_elements := [false, true]
  finite_surjective := by
    intro a
    cases a <;> rfl
  finite_injective := by
    decide

/-- Helper: finRange.map val = range -/
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp [List.length_finRange]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Fin.val_cast]

/-- Helper for Fin proof -/
theorem finRange_getElem?_eq (n : Nat) (i : Nat) (h : i < n) :
    (List.finRange n)[i]? = some ⟨i, h⟩ := by
  rw [List.getElem?_eq_getElem (by simp; exact h)]
  simp only [List.getElem_finRange, Fin.cast]

/-- Fin n has exactly n elements -/
instance (n : Nat) : FiniteType (Fin n) where
  finite_index := fun i => i.val
  finite_elements := List.finRange n
  finite_surjective := by
    intro a
    have h := a.isLt
    rw [finRange_getElem?_eq n a.val h]
  finite_injective := by
    rw [finRange_map_val]
    exact List.nodup_range

/-- Unit type has exactly 1 element -/
instance : FiniteType Unit where
  finite_index := fun _ => 0
  finite_elements := [()]
  finite_surjective := by
    intro a
    cases a
    rfl
  finite_injective := by
    decide

/-- Empty type has 0 elements -/
instance : FiniteType Empty where
  finite_index := Empty.rec
  finite_elements := []
  finite_surjective := Empty.rec
  finite_injective := by
    decide

/-! ## Product Instance Helpers -/

/-- Helper for index bound -/
theorem finite_index_lt' {T : Type} [FT : FiniteType T] (a : T) :
    FT.finite_index a < FT.finite_elements.length := by
  have h := FT.finite_surjective a
  cases hget : FT.finite_elements[FT.finite_index a]? with
  | none =>
    rw [hget] at h
    cases h
  | some v =>
    rw [List.getElem?_eq_some_iff] at hget
    exact hget.1

/-- Length of flatMap for cartesian product -/
theorem flatMap_map_length {A B C : Type} (la : List A) (lb : List B) (f : A → B → C) :
    (la.flatMap fun a => lb.map fun b => f a b).length = la.length * lb.length := by
  induction la with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons]
    have : (as.length + 1) * lb.length = lb.length + as.length * lb.length := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [this]

/-- Access element in flatMap cartesian product -/
theorem flatMap_map_getElem? {A B C : Type} (la : List A) (lb : List B) (f : A → B → C)
    (i j : Nat) (hi : i < la.length) (hj : j < lb.length) :
    (la.flatMap fun a => lb.map fun b => f a b)[i * lb.length + j]? =
      some (f la[i] lb[j]) := by
  induction la generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simp; exact hj)]
      simp only [List.getElem?_map]
      rw [List.getElem?_eq_getElem hj]
      simp
    | succ i' =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      have hskip : lb.length ≤ (i' + 1) * lb.length + j := by
        have : lb.length ≤ (i' + 1) * lb.length := Nat.le_mul_of_pos_left lb.length (Nat.succ_pos i')
        omega
      rw [List.getElem?_append_right (by simp; exact hskip)]
      simp only [List.length_map]
      have heq : (i' + 1) * lb.length + j - lb.length = i' * lb.length + j := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [heq]
      have hi' : i' < as.length := by simp only [List.length_cons] at hi; omega
      exact ih i' hi'

/-- Key lemma: if a1 * n + b1 = a2 * n + b2 with b1, b2 < n, then a1 = a2 and b1 = b2 -/
@[grind] theorem mul_add_unique {a1 a2 b1 b2 n : Nat} (hn : 0 < n) (hb1 : b1 < n) (hb2 : b2 < n)
    (h : a1 * n + b1 = a2 * n + b2) : a1 = a2 ∧ b1 = b2 := by
  -- Use the fact that (a * n + b) / n = a when b < n
  have hdiv1 : (a1 * n + b1) / n = a1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn]
    simp [Nat.div_eq_of_lt hb1]
  have hdiv2 : (a2 * n + b2) / n = a2 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn]
    simp [Nat.div_eq_of_lt hb2]
  have hmod1 : (a1 * n + b1) % n = b1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hb1
  have hmod2 : (a2 * n + b2) % n = b2 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hb2
  constructor
  · rw [← hdiv1, ← hdiv2, h]
  · rw [← hmod1, ← hmod2, h]

/-- Helper: flatMap of nodup lists with pairwise disjoint results is nodup -/
theorem nodup_flatMap {α β : Type} (l : List α) (f : α → List β)
    (h1 : ∀ a, a ∈ l → (f a).Nodup)
    (h2 : l.Pairwise fun a1 a2 => ∀ x, x ∈ f a1 → x ∉ f a2)
    : (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact h1 a List.mem_cons_self
    · apply ih
      · intro a' ha'
        exact h1 a' (List.mem_cons_of_mem a ha')
      · exact List.Pairwise.tail h2
    · intro x hx1 y hy hxy
      rw [← hxy] at hy
      -- x ∈ f a and x ∈ as.flatMap f is a contradiction
      rw [List.mem_flatMap] at hy
      obtain ⟨a', ha', hxa'⟩ := hy
      -- From h2, we know f a and f a' are disjoint (since a ≠ a' and a' ∈ as)
      have hpw : (a :: as).Pairwise fun a1 a2 => ∀ x, x ∈ f a1 → x ∉ f a2 := h2
      rw [List.pairwise_cons] at hpw
      have hdisj := hpw.1 a' ha'
      exact hdisj x hx1 hxa'

/-- Product index is injective on pairs -/
theorem prod_index_injective' [FiniteType A] [FiniteType B] (a1 a2 : A) (b1 b2 : B) :
    FiniteType.finite_index a1 * (FiniteType.finite_elements (T := B)).length +
      FiniteType.finite_index b1 =
    FiniteType.finite_index a2 * (FiniteType.finite_elements (T := B)).length +
      FiniteType.finite_index b2 →
    (a1, b1) = (a2, b2) := by
  intro h
  have hb1 := finite_index_lt' b1
  have hb2 := finite_index_lt' b2
  -- Handle the case where B is empty (n = 0)
  by_cases hn : (FiniteType.finite_elements (T := B)).length = 0
  · -- If B is empty, there are no elements, so this is vacuously true
    simp only [hn, Nat.mul_zero, Nat.zero_add] at h
    have hlt1 : FiniteType.finite_index b1 < 0 := by rw [← hn]; exact hb1
    omega
  · -- If B is non-empty, use the uniqueness lemma
    have hn' : 0 < (FiniteType.finite_elements (T := B)).length := Nat.pos_of_ne_zero hn
    have ⟨ha, hb⟩ := mul_add_unique hn' hb1 hb2 h
    have ha' := finite_index_injective a1 a2 ha
    have hb' := finite_index_injective b1 b2 hb
    simp only [ha', hb']

/-- Product of finite types is finite -/
instance [FiniteType A] [FiniteType B] : FiniteType (A × B) where
  finite_index := fun (a, b) =>
    FiniteType.finite_index a * (FiniteType.finite_elements (T := B)).length +
    FiniteType.finite_index b
  finite_elements :=
    (FiniteType.finite_elements (T := A)).flatMap fun a =>
      (FiniteType.finite_elements (T := B)).map fun b => (a, b)
  finite_surjective := by
    intro ⟨a, b⟩
    have ha := FiniteType.finite_surjective a
    have hb := FiniteType.finite_surjective b
    have hi := finite_index_lt' a
    have hj := finite_index_lt' b
    rw [flatMap_map_getElem? _ _ _ _ _ hi hj]
    -- Now need to show: some (a', b') = some (a, b) where a' = elements[idx a], b' = elements[idx b]
    rw [List.getElem?_eq_some_iff] at ha hb
    simp only [ha.2, hb.2]
  finite_injective := by
    -- Use nodup_map_of_nodup_injective with the product index function
    apply List.nodup_map_of_nodup_injective
    · -- Prove the index function is injective
      intro ⟨a1, b1⟩ ⟨a2, b2⟩ heq
      exact prod_index_injective' a1 a2 b1 b2 heq
    · -- Prove the flatMap list has no duplicates
      -- First, show each "row" has no duplicates, and rows don't overlap
      have hb_nodup : (FiniteType.finite_elements (T := B)).Nodup := finite_nodup
      -- Cartesian product of nodup lists is nodup
      apply nodup_flatMap
      · -- Each row (map over B elements) has no duplicates
        intro a _
        apply List.nodup_map_of_nodup_injective
        · intro b1 b2 heq
          cases heq
          rfl
        · exact hb_nodup
      · -- The rows are pairwise disjoint
        apply List.Pairwise.imp _ finite_nodup
        intro a1 a2 hne x hx1 hx2
        rw [List.mem_map] at hx1 hx2
        obtain ⟨b1, _, hxb1⟩ := hx1
        obtain ⟨b2, _, hxb2⟩ := hx2
        rw [← hxb1] at hxb2
        cases hxb2
        exact hne rfl

/-- Helper for index bound -/
theorem finite_index_lt {T : Type} [FT : FiniteType T] (a : T) :
    FT.finite_index a < FT.finite_elements.length := by
  have h := FT.finite_surjective a
  cases hget : FT.finite_elements[FT.finite_index a]? with
  | none =>
    rw [hget] at h
    cases h
  | some v =>
    rw [List.getElem?_eq_some_iff] at hget
    exact hget.1

/-- Sum of finite types is finite -/
instance [FiniteType A] [FiniteType B] : FiniteType (A ⊕ B) where
  finite_index
    | .inl a => FiniteType.finite_index a
    | .inr b => (FiniteType.finite_elements (T := A)).length + FiniteType.finite_index b
  finite_elements :=
    ((FiniteType.finite_elements (T := A)).map Sum.inl) ++
    ((FiniteType.finite_elements (T := B)).map Sum.inr)
  finite_surjective := by
    intro x
    cases x with
    | inl a =>
      have ha := FiniteType.finite_surjective a
      have hlt : FiniteType.finite_index a < (FiniteType.finite_elements (T := A)).length :=
        finite_index_lt a
      simp only [List.getElem?_append, List.length_map]
      split
      · simp only [List.getElem?_map, ha, Option.map_some]
      · omega
    | inr b =>
      have hb := FiniteType.finite_surjective b
      simp only [List.getElem?_append, List.length_map]
      split
      · omega
      · simp only [Nat.add_sub_cancel_left, List.getElem?_map, hb, Option.map_some]
  finite_injective := by
    -- First rewrite map over append
    simp only [List.map_append, List.map_map]
    -- Now we have (l1.map f1 ++ l2.map f2).Nodup
    rw [List.nodup_append]
    constructor
    · -- First part: inl indices are nodup
      have h := FiniteType.finite_injective (T := A)
      -- The goal is (l.map (match_fn ∘ Sum.inl)).Nodup
      -- which equals (l.map finite_index).Nodup by funext
      have eq : ((fun x : A ⊕ B => match x with
          | .inl a => FiniteType.finite_index a
          | .inr b => (FiniteType.finite_elements (T := A)).length + FiniteType.finite_index b) ∘ Sum.inl)
          = (FiniteType.finite_index (T := A)) := by funext a; rfl
      rw [eq]
      exact h
    constructor
    · -- Second part: inr indices are nodup
      have eq : ((fun x : A ⊕ B => match x with
          | .inl a => FiniteType.finite_index a
          | .inr b => (FiniteType.finite_elements (T := A)).length + FiniteType.finite_index b) ∘ Sum.inr)
          = (fun b => (FiniteType.finite_elements (T := A)).length + FiniteType.finite_index b) := by
        funext b; rfl
      rw [eq]
      -- Need to prove (finite_elements.map f).Nodup where f is injective
      apply List.nodup_map_of_nodup_injective
      · intro a b heq
        -- heq : lenA + finite_index a = lenA + finite_index b
        have : FiniteType.finite_index a = FiniteType.finite_index b := Nat.add_left_cancel heq
        exact finite_index_injective a b this
      · exact finite_nodup (T := B)
    · -- Disjoint: inl indices don't overlap with inr indices
      -- Goal: ∀ x ∈ l1, ∀ y ∈ l2, x ≠ y
      intro x hx1 y hy2
      rw [List.mem_map] at hx1 hy2
      obtain ⟨a, ha, hxa⟩ := hx1
      obtain ⟨b, hb, hyb⟩ := hy2
      simp only [Function.comp_apply] at hxa hyb
      have hlt := finite_index_lt (T := A) a
      -- hxa : finite_index a = x
      -- hyb : lenA + finite_index b = y
      -- hlt : finite_index a < lenA
      -- heq : x = y leads to contradiction
      intro heq
      rw [← hxa, ← hyb] at heq
      omega

/-! ## Option type -/

/-- Option of a finite type is finite -/
instance [FiniteType A] : FiniteType (Option A) where
  finite_index
    | none => 0
    | some a => FiniteType.finite_index a + 1
  finite_elements := none :: (FiniteType.finite_elements.map some)
  finite_surjective := by
    intro x
    cases x with
    | none => rfl
    | some a =>
      simp only [List.getElem?_cons_succ, List.getElem?_map]
      have ha := FiniteType.finite_surjective a
      simp only [ha]
      rfl
  finite_injective := by
    simp only [List.map_cons, List.map_map, List.nodup_cons]
    constructor
    · simp only [List.mem_map, Function.comp_apply, not_exists, not_and]
      intro a _
      omega
    · have eq : ((fun x : Option A => match x with
          | none => 0
          | some a => FiniteType.finite_index a + 1) ∘ some)
          = (fun a => FiniteType.finite_index a + 1) := by funext a; rfl
      rw [eq]
      -- goal: (finite_elements.map (fun a => finite_index a + 1)).Nodup
      apply List.nodup_map_of_nodup_injective
      · intro a b heq
        -- heq : finite_index a + 1 = finite_index b + 1
        have : FiniteType.finite_index a = FiniteType.finite_index b := Nat.add_right_cancel heq
        exact finite_index_injective a b this
      · exact finite_nodup (T := A)

/-! ## Examples -/

section Examples
  -- Simple two-element enum
  inductive T2 where
    | A | B
    deriving DecidableEq, Repr

  instance : FiniteType T2 where
    finite_index
      | .A => 0
      | .B => 1
    finite_elements := [.A, .B]
    finite_surjective := by
      intro a
      cases a <;> rfl
    finite_injective := by
      decide

  -- Three-element enum
  inductive T3 where
    | A | B | C
    deriving DecidableEq, Repr

  instance : FiniteType T3 where
    finite_index
      | .A => 0
      | .B => 1
      | .C => 2
    finite_elements := [.A, .B, .C]
    finite_surjective := by
      intro a
      cases a <;> rfl
    finite_injective := by
      decide

end Examples

end Koika
