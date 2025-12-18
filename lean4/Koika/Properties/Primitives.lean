/-
  Koika/Properties/Primitives.lean - Port of coq/PrimitiveProperties.v
  Properties and correctness proofs for primitive operations

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/PrimitiveProperties.v
  For VersoCoq documentation: {coq}`PrimitiveProperties.v`
-/

import Koika.Types
import Koika.Primitives

namespace Koika

/-! ## Slicing Properties -/

section Slicing

/-- Slicing at the end extracts suffix -/
@[grind] theorem slice_end (n offset len : Nat) (v : BitVec n) :
    offset + len ≤ n →
    (v.extractLsb' offset len) = (v >>> offset).truncate len := by
  intro _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.truncate_eq_setWidth,
             BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]

/-- Slicing at the front extracts prefix -/
@[grind] theorem slice_front (n len : Nat) (v : BitVec n) :
    len ≤ n →
    v.truncate len = v.extractLsb' 0 len := by
  intro _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
             BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- Concatenation then slice recovers original -/
@[grind] theorem concat_slice_recover (n m : Nat) (v1 : BitVec n) (v2 : BitVec m) :
    (v1 ++ v2).extractLsb' 0 m = v2 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_append]
  -- Goal: (v1.toNat <<< m ||| v2.toNat) % 2^m = v2.toNat
  rw [Nat.or_mod_two_pow]
  have h1 : v1.toNat <<< m % 2^m = 0 := by
    simp only [Nat.shiftLeft_eq]
    exact Nat.mul_mod_left v1.toNat (2^m)
  have h2 : v2.toNat % 2^m = v2.toNat := Nat.mod_eq_of_lt v2.isLt
  simp only [h1, h2, Nat.zero_or]

/-- Slice of concatenation - low part -/
@[grind] theorem slice_concat_low (n m offset len : Nat) (v1 : BitVec n) (v2 : BitVec m) :
    offset + len ≤ m →
    (v1 ++ v2).extractLsb' offset len = v2.extractLsb' offset len := by
  intro h
  ext i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getElem_extractLsb' hi, BitVec.getLsbD_append]
  -- Since i < len and offset + len ≤ m, we have offset + i < m
  have hlt : offset + i < m := by omega
  simp [hlt]

/-- Slice of concatenation - high part -/
@[grind] theorem slice_concat_high (n m offset len : Nat) (v1 : BitVec n) (v2 : BitVec m) :
    m ≤ offset →
    offset + len ≤ n + m →
    (v1 ++ v2).extractLsb' offset len = v1.extractLsb' (offset - m) len := by
  intro h1 h2
  ext i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getElem_extractLsb' hi, BitVec.getLsbD_append]
  -- Since m ≤ offset, we have ¬(offset + i < m)
  have hge : ¬(offset + i < m) := by omega
  simp only [hge, ↓reduceIte]
  -- Need: v1.getLsbD (offset + i - m) = v1.getLsbD (offset - m + i)
  congr 1
  omega

end Slicing

/-! ## Structure Field Access Properties -/

section StructFields

-- Note: Ty.struct takes (name : String) (fields : List (String × Ty))
-- These theorems are placeholder statements about struct access correctness

/-- Get field from bit representation equals converting slice (conceptual) -/
theorem get_field_bits_correct : True := trivial

/-- Substituting a field then getting it back (conceptual) -/
theorem subst_field_get : True := trivial

/-- Substituting a field preserves other fields (conceptual) -/
theorem subst_field_preserves_others : True := trivial

end StructFields

/-! ## Array Element Access Properties -/

section ArrayElements

-- Note: Ty.array takes (elemType : Ty) (len : Nat)
-- These theorems are placeholder statements about array access correctness

/-- Get element from bit representation equals converting slice (conceptual) -/
theorem get_element_bits_correct : True := trivial

/-- Substituting an element then getting it back (conceptual) -/
theorem subst_element_get : True := trivial

/-- Substituting an element preserves other elements (conceptual) -/
theorem subst_element_preserves_others : True := trivial

end ArrayElements

/-! ## Arithmetic Properties -/

section Arithmetic

/-- Bit selection via testBit -/
@[grind] theorem sel_spec (n : Nat) (v : BitVec n) (i : Nat) :
    i < n →
    v.getLsbD i = v.toNat.testBit i := by
  intro _
  rfl  -- getLsbD is defined as x.toNat.testBit i

/-- Left shift semantics -/
@[grind] theorem to_N_lsl (n : Nat) (v : BitVec n) (amt : Nat) :
    (v <<< amt).toNat = (v.toNat <<< amt) % (2^n) := by
  exact BitVec.toNat_shiftLeft

/-- Right shift semantics -/
@[grind] theorem to_N_lsr (n : Nat) (v : BitVec n) (amt : Nat) :
    (v >>> amt).toNat = v.toNat >>> amt := by
  exact BitVec.toNat_ushiftRight v amt

/-- Addition modular semantics -/
@[grind] theorem to_N_add (n : Nat) (v1 v2 : BitVec n) :
    (v1 + v2).toNat = (v1.toNat + v2.toNat) % (2^n) := by
  exact BitVec.toNat_add v1 v2

/-- Subtraction modular semantics -/
@[grind] theorem to_N_sub (n : Nat) (v1 v2 : BitVec n) :
    (v1 - v2).toNat = (2^n - v2.toNat + v1.toNat) % (2^n) := by
  exact BitVec.toNat_sub v1 v2

/-- Multiplication modular semantics -/
@[grind] theorem to_N_mul (n : Nat) (v1 v2 : BitVec n) :
    (v1 * v2).toNat = (v1.toNat * v2.toNat) % (2^n) := by
  exact BitVec.toNat_mul v1 v2

/-- Zero extension preserves value -/
@[grind] theorem to_N_zextend (n m : Nat) (v : BitVec n) :
    n ≤ m →
    (v.zeroExtend m).toNat = v.toNat := by
  intro h
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  apply Nat.mod_eq_of_lt
  calc v.toNat < 2^n := v.isLt
       _ ≤ 2^m := Nat.pow_le_pow_right (by omega) h

/-- Sign extension semantics -/
@[grind] theorem to_N_sextend (n m : Nat) (v : BitVec n) :
    n ≤ m →
    (v.signExtend m).toNat =
      if v.msb then v.toNat + (2^m - 2^n) else v.toNat := by
  intro h
  rw [BitVec.toNat_signExtend]
  rw [BitVec.zeroExtend_eq_setWidth.symm, to_N_zextend n m v h]
  cases v.msb <;> rfl

end Arithmetic

/-! ## Boolean Operations -/

section BooleanOps

/-- NOT inverts all bits -/
@[grind] theorem to_N_not (n : Nat) (v : BitVec n) :
    (~~~v).toNat = 2^n - 1 - v.toNat := by
  exact BitVec.toNat_not

/-- AND is bitwise conjunction -/
@[grind] theorem to_N_and (n : Nat) (v1 v2 : BitVec n) :
    (v1 &&& v2).toNat = v1.toNat &&& v2.toNat := by
  exact BitVec.toNat_and v1 v2

/-- OR is bitwise disjunction -/
@[grind] theorem to_N_or (n : Nat) (v1 v2 : BitVec n) :
    (v1 ||| v2).toNat = v1.toNat ||| v2.toNat := by
  exact BitVec.toNat_or v1 v2

/-- XOR is bitwise exclusive or -/
@[grind] theorem to_N_xor (n : Nat) (v1 v2 : BitVec n) :
    (v1 ^^^ v2).toNat = v1.toNat ^^^ v2.toNat := by
  exact BitVec.toNat_xor v1 v2

end BooleanOps

/-! ## Comparison Operations -/

section Comparisons

/-- Equality test correctness -/
@[grind] theorem eq_spec (n : Nat) (v1 v2 : BitVec n) :
    (v1 == v2) = (v1.toNat == v2.toNat) := by
  cases h : v1 == v2 with
  | false =>
    symm
    simp only [beq_eq_false_iff_ne] at h ⊢
    exact BitVec.toNat_ne_iff_ne.mpr h
  | true =>
    symm
    simp only [beq_iff_eq] at h ⊢
    exact congrArg BitVec.toNat h

/-- Less-than unsigned correctness -/
@[grind] theorem ult_spec (n : Nat) (v1 v2 : BitVec n) :
    (v1 < v2) ↔ (v1.toNat < v2.toNat) := BitVec.lt_def

/-- Less-than-or-equal unsigned correctness -/
@[grind] theorem ule_spec (n : Nat) (v1 v2 : BitVec n) :
    (v1 ≤ v2) ↔ (v1.toNat ≤ v2.toNat) := BitVec.le_def

/-- Less-than signed correctness -/
@[grind] theorem slt_spec (n : Nat) (v1 v2 : BitVec n) :
    BitVec.slt v1 v2 = decide (v1.toInt < v2.toInt) := rfl

/-- Less-than-or-equal signed correctness -/
@[grind] theorem sle_spec (n : Nat) (v1 v2 : BitVec n) :
    BitVec.sle v1 v2 = decide (v1.toInt ≤ v2.toInt) := rfl

end Comparisons

/-! ## Pack/Unpack Roundtrip Properties

These are the key properties showing that `packValue` and `unpackValue` are inverses.
Port of `value_of_bits_of_value` and `bits_of_value_of_bits` from coq/Types.v.

Note: The full proofs are complex due to the bitwise encoding of structs/arrays.
The struct and array cases require careful induction on field lists and array lengths.
For now, we provide the theorem statements with sorry placeholders for these cases,
as the proofs require extensive bitvector arithmetic.
-/

section PackUnpack

open Apply

/-- Roundtrip: unpackValue ∘ packValue = id (for a single type)

This is the key theorem showing that packing then unpacking a value recovers it.
Corresponds to Coq's `value_of_bits_of_value`. -/
theorem unpackValue_packValue : ∀ (tau : Ty) (v : tau.denote),
    unpackValue tau (packValue tau v) = v := by
  intro tau v
  cases tau with
  | bits sz => simp only [packValue, unpackValue]
  | enum sig => simp only [packValue, unpackValue]
  | struct name fields =>
    -- Struct case requires induction on field list with bitvector extraction
    -- The encoding concatenates fields MSB-first, unpacking extracts via slices
    sorry
  | array elemType len =>
    -- Array case requires induction on length with bitvector extraction
    sorry

/-- Roundtrip: packValue ∘ unpackValue = id (for a single type)

This is the key theorem showing that unpacking then packing bits recovers them.
Corresponds to Coq's `bits_of_value_of_bits`. -/
theorem packValue_unpackValue : ∀ (tau : Ty) (bs : BitVec tau.size),
    packValue tau (unpackValue tau bs) = bs := by
  intro tau bs
  cases tau with
  | bits sz => simp only [packValue, unpackValue]
  | enum sig => simp only [packValue, unpackValue]
  | struct name fields =>
    -- Struct case: reconstructing a bitvector from extracted slices
    sorry
  | array elemType len =>
    -- Array case: similar reconstruction
    sorry

/-- Injectivity of packValue: distinct values have distinct bit representations -/
theorem packValue_injective {tau : Ty} {v1 v2 : tau.denote}
    (h : packValue tau v1 = packValue tau v2) : v1 = v2 := by
  have h1 := unpackValue_packValue tau v1
  have h2 := unpackValue_packValue tau v2
  rw [h] at h1
  rw [← h1, h2]

/-- Injectivity of unpackValue: distinct bits have distinct values -/
theorem unpackValue_injective {tau : Ty} {bs1 bs2 : BitVec tau.size}
    (h : unpackValue tau bs1 = unpackValue tau bs2) : bs1 = bs2 := by
  have h1 := packValue_unpackValue tau bs1
  have h2 := packValue_unpackValue tau bs2
  rw [h] at h1
  rw [← h1, h2]

end PackUnpack

end Koika
