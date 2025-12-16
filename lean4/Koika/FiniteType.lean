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
  finite_surjective : ∀ a : T, finite_elements.get? (finite_index a) = some a
  /-- The indices are unique (no duplicates in the mapped indices) -/
  finite_injective : finite_elements.map finite_index |>.Nodup

/-! ## Basic Properties -/

/-- The index function is injective: equal indices imply equal elements -/
theorem finite_index_injective {T : Type} [FT : FiniteType T] :
    ∀ t1 t2, FT.finite_index t1 = FT.finite_index t2 → t1 = t2 := by
  intro t1 t2 h
  have h1 := FT.finite_surjective t1
  have h2 := FT.finite_surjective t2
  rw [h] at h1
  rw [h1] at h2
  cases h2
  rfl

/-- The finite_elements list has no duplicates -/
theorem finite_nodup {T : Type} [FT : FiniteType T] :
    FT.finite_elements.Nodup := by
  sorry  -- This follows from finite_injective and properties of map

/-! ## Helper: Increasing Lists -/

/-- Check if a list of natural numbers is strictly increasing -/
def increasing : List Nat → Bool
  | [] => true
  | [_] => true
  | n1 :: n2 :: rest => (n1 < n2) && increasing (n2 :: rest)

/-- Strictly increasing lists have no duplicates -/
theorem increasing_nodup : ∀ l, increasing l = true → l.Nodup := by
  sorry  -- Proof by induction on the list structure

/-! ## Instances for Common Types -/

/-- Bool has exactly 2 elements -/
instance : FiniteType Bool where
  finite_index := fun b => if b then 1 else 0
  finite_elements := [false, true]
  finite_surjective := by
    intro a
    cases a <;> simp [List.get?]
  finite_injective := by
    simp [List.map, List.Nodup]
    intro h
    cases h

/-- Fin n has exactly n elements -/
instance (n : Nat) : FiniteType (Fin n) where
  finite_index := fun i => i.val
  finite_elements := List.finRange n
  finite_surjective := by
    intro a
    simp [List.finRange, List.get?]
    sorry  -- Proof that finRange contains all Fin n values at correct indices
  finite_injective := by
    sorry  -- Proof that mapping Fin values to their .val produces no duplicates

/-- Unit type has exactly 1 element -/
instance : FiniteType Unit where
  finite_index := fun _ => 0
  finite_elements := [()]
  finite_surjective := by
    intro a
    cases a
    simp [List.get?]
  finite_injective := by
    simp [List.map, List.Nodup]

/-- Empty type has 0 elements -/
instance : FiniteType Empty where
  finite_index := fun e => Empty.rec e
  finite_elements := []
  finite_surjective := by
    intro a
    exact Empty.rec a
  finite_injective := by
    simp [List.map, List.Nodup]

/-- Product of finite types is finite -/
instance [FiniteType A] [FiniteType B] : FiniteType (A × B) where
  finite_index := fun (a, b) =>
    FiniteType.finite_index a * FiniteType.finite_elements.length (T := B) +
    FiniteType.finite_index b
  finite_elements :=
    FiniteType.finite_elements (T := A) |>.bind fun a =>
      FiniteType.finite_elements (T := B) |>.map fun b => (a, b)
  finite_surjective := by
    sorry  -- Cartesian product indexing proof
  finite_injective := by
    sorry  -- No duplicate indices in cartesian product

/-- Sum of finite types is finite -/
instance [FiniteType A] [FiniteType B] : FiniteType (A ⊕ B) where
  finite_index
    | .inl a => FiniteType.finite_index a
    | .inr b => FiniteType.finite_elements.length (T := A) + FiniteType.finite_index b
  finite_elements :=
    (FiniteType.finite_elements (T := A) |>.map Sum.inl) ++
    (FiniteType.finite_elements (T := B) |>.map Sum.inr)
  finite_surjective := by
    sorry  -- Sum type indexing proof
  finite_injective := by
    sorry  -- No duplicate indices in sum

/-! ## Option type -/

/-- Option of a finite type is finite -/
instance [FiniteType A] : FiniteType (Option A) where
  finite_index
    | none => 0
    | some a => FiniteType.finite_index a + 1
  finite_elements := none :: (FiniteType.finite_elements (T := A) |>.map some)
  finite_surjective := by
    sorry  -- Option indexing proof
  finite_injective := by
    sorry  -- No duplicate indices in Option

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
      cases a <;> simp [List.get?]
    finite_injective := by
      simp [List.map, List.Nodup]
      intro h
      cases h

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
      cases a <;> simp [List.get?]
    finite_injective := by
      simp [List.map, List.Nodup]
      intro h1 h2
      cases h1
      cases h2

end Examples

end Koika
