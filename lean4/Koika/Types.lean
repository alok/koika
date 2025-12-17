/-
  Koika/Types.lean - Port of coq/Types.v
  Core type system for Kôika programs
-/

import Lean.Data.Format

namespace Koika

/-! ## Read/Write Ports -/

inductive Port where
  | p0
  | p1
  deriving DecidableEq, Repr, Inhabited, BEq

/-! ## Type Signatures -/

/-- Enum signature: named enumeration with bit patterns -/
structure EnumSig where
  name : String
  size : Nat  -- number of members
  bitsize : Nat  -- bit width for encoding
  members : Array String  -- member names (length = size)
  deriving Repr, DecidableEq

/-- BEq for EnumSig via DecidableEq (ensures LawfulBEq) -/
instance : BEq EnumSig where
  beq a b := decide (a = b)

instance : LawfulBEq EnumSig where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-! ## Kôika Types -/

/-- Core type system for Kôika -/
inductive Ty where
  | bits (sz : Nat)
  | enum (sig : EnumSig)
  | struct (name : String) (fields : List (String × Ty))
  | array (elemType : Ty) (len : Nat)

/-- Unit type is 0-bit bitvector -/
abbrev unitTy : Ty := .bits 0

/-! ## BEq and DecidableEq for Ty -/

mutual
  def Ty.beq : Ty → Ty → Bool
    | .bits sz1, .bits sz2 => sz1 == sz2
    | .enum sig1, .enum sig2 => sig1 == sig2
    | .struct n1 f1, .struct n2 f2 => n1 == n2 && fieldsBeq f1 f2
    | .array t1 l1, .array t2 l2 => Ty.beq t1 t2 && l1 == l2
    | _, _ => false

  def fieldsBeq : List (String × Ty) → List (String × Ty) → Bool
    | [], [] => true
    | (n1, t1) :: rest1, (n2, t2) :: rest2 =>
        n1 == n2 && Ty.beq t1 t2 && fieldsBeq rest1 rest2
    | _, _ => false
end

instance : BEq Ty := ⟨Ty.beq⟩

/-! ## Ty.beq soundness and completeness -/

mutual
  theorem Ty.beq_eq_true_iff : ∀ t1 t2 : Ty, t1.beq t2 = true ↔ t1 = t2
    | .bits sz1, .bits sz2 => by simp [Ty.beq, beq_iff_eq]
    | .bits _, .enum _ => by simp [Ty.beq]
    | .bits _, .struct _ _ => by simp [Ty.beq]
    | .bits _, .array _ _ => by simp [Ty.beq]
    | .enum _, .bits _ => by simp [Ty.beq]
    | .enum sig1, .enum sig2 => by
        simp only [Ty.beq, beq_iff_eq]
        exact Iff.intro (congrArg Ty.enum) (fun h => Ty.enum.inj h)
    | .enum _, .struct _ _ => by simp [Ty.beq]
    | .enum _, .array _ _ => by simp [Ty.beq]
    | .struct _ _, .bits _ => by simp [Ty.beq]
    | .struct _ _, .enum _ => by simp [Ty.beq]
    | .struct n1 f1, .struct n2 f2 => by
        simp only [Ty.beq, Bool.and_eq_true, beq_iff_eq]
        constructor
        · intro ⟨hn, hf⟩
          have hfeq := (fieldsBeq_eq_true_iff f1 f2).mp hf
          simp [hn, hfeq]
        · intro h
          injection h with hn hf
          exact ⟨hn, (fieldsBeq_eq_true_iff f1 f2).mpr hf⟩
    | .struct _ _, .array _ _ => by simp [Ty.beq]
    | .array _ _, .bits _ => by simp [Ty.beq]
    | .array _ _, .enum _ => by simp [Ty.beq]
    | .array _ _, .struct _ _ => by simp [Ty.beq]
    | .array t1 l1, .array t2 l2 => by
        simp only [Ty.beq, Bool.and_eq_true, beq_iff_eq]
        constructor
        · intro ⟨ht, hl⟩
          have hteq := (Ty.beq_eq_true_iff t1 t2).mp ht
          simp [hteq, hl]
        · intro h
          injection h with ht hl
          exact ⟨(Ty.beq_eq_true_iff t1 t2).mpr ht, hl⟩

  theorem fieldsBeq_eq_true_iff : ∀ f1 f2 : List (String × Ty), fieldsBeq f1 f2 = true ↔ f1 = f2
    | [], [] => by simp [fieldsBeq]
    | [], _ :: _ => by simp [fieldsBeq]
    | _ :: _, [] => by simp [fieldsBeq]
    | (n1, t1) :: rest1, (n2, t2) :: rest2 => by
        simp only [fieldsBeq, Bool.and_eq_true, beq_iff_eq]
        constructor
        · intro ⟨⟨hn, ht⟩, hr⟩
          have hteq := (Ty.beq_eq_true_iff t1 t2).mp ht
          have hreq := (fieldsBeq_eq_true_iff rest1 rest2).mp hr
          simp [hn, hteq, hreq]
        · intro h
          injection h with h1 h2
          have ⟨hn, ht⟩ := Prod.mk.inj h1
          exact ⟨⟨hn, (Ty.beq_eq_true_iff t1 t2).mpr ht⟩, (fieldsBeq_eq_true_iff rest1 rest2).mpr h2⟩
end

instance : DecidableEq Ty := fun t1 t2 =>
  if h : t1.beq t2 then
    isTrue ((Ty.beq_eq_true_iff t1 t2).mp h)
  else
    isFalse (fun heq => h ((Ty.beq_eq_true_iff t1 t2).mpr heq))

/-! ## Repr for Ty -/

mutual
  partial def Ty.reprPrec : Ty → Nat → Lean.Format
    | .bits sz, _ => f!"Ty.bits {sz}"
    | .enum sig, _ => f!"Ty.enum {repr sig}"
    | .struct name fields, _ => f!"Ty.struct {repr name} {fieldsRepr fields}"
    | .array elemType len, _ => f!"Ty.array ({Ty.reprPrec elemType 0}) {len}"

  partial def fieldsRepr : List (String × Ty) → Lean.Format
    | [] => "[]"
    | fields => f!"[{fields.map (fun (n, t) => f!"({repr n}, {Ty.reprPrec t 0})")}]"
end

instance : Repr Ty := ⟨Ty.reprPrec⟩

/-! ## Type Kind (for pattern matching without full details) -/

inductive TyKind where
  | bits
  | enum
  | struct
  | array
  deriving DecidableEq, Repr

def Ty.kind : Ty → TyKind
  | .bits _ => .bits
  | .enum _ => .enum
  | .struct _ _ => .struct
  | .array _ _ => .array

/-! ## Type Size Computation -/

mutual
  /-- Compute bit width of a type -/
  def Ty.size : Ty → Nat
    | .bits sz => sz
    | .enum sig => sig.bitsize
    | .struct _ fields => fieldsSize fields
    | .array elemType len => len * Ty.size elemType

  def fieldsSize : List (String × Ty) → Nat
    | [] => 0
    | (_, ty) :: rest => Ty.size ty + fieldsSize rest
end

/-! ## Type Denotation (Lean type for Kôika type) -/

mutual
  /-- Lean type corresponding to a Kôika type -/
  def Ty.denote : Ty → Type
    | .bits sz => BitVec sz
    | .enum sig => BitVec sig.bitsize
    | .struct _ fields => fieldsDenote fields
    | .array elemType len => Fin len → Ty.denote elemType

  def fieldsDenote : List (String × Ty) → Type
    | [] => Unit
    | (_, ty) :: rest => Ty.denote ty × fieldsDenote rest
end

/-! ## Default Values -/

mutual
  /-- Default (zero) value for a type -/
  def Ty.default : (ty : Ty) → ty.denote
    | .bits sz => (0 : BitVec sz)
    | .enum sig => (0 : BitVec sig.bitsize)
    | .struct _ fields => fieldsDefault fields
    | .array elemType _ => fun _ => Ty.default elemType

  def fieldsDefault : (fields : List (String × Ty)) → fieldsDenote fields
    | [] => ()
    | (_, ty) :: rest => (Ty.default ty, fieldsDefault rest)
end

instance (ty : Ty) : Inhabited ty.denote := ⟨Ty.default ty⟩

/-! ## Struct Field Access -/

/-- Get field type by name -/
def Ty.fieldType? (ty : Ty) (fieldName : String) : Option Ty :=
  match ty with
  | .struct _ fields => fields.lookup fieldName
  | _ => none

/-- Number of fields in a struct -/
def Ty.numFields : Ty → Nat
  | .struct _ fields => fields.length
  | _ => 0

/-! ## Function Signatures -/

/-- Generic function signature -/
structure FnSig where
  argTypes : List Ty
  retType : Ty
  deriving Repr

/-- External function signature (1 argument) -/
structure ExternalSig where
  argType : Ty
  retType : Ty
  deriving Repr

/-- Lowered (circuit-level) signature with sizes instead of types -/
structure CExternalSig where
  argSize : Nat
  retSize : Nat
  deriving Repr, BEq, DecidableEq

def ExternalSig.toLowered (sig : ExternalSig) : CExternalSig :=
  { argSize := sig.argType.size
    retSize := sig.retType.size }

def CExternalSig.toTyped (sig : CExternalSig) : ExternalSig :=
  { argType := .bits sig.argSize
    retType := .bits sig.retSize }

/-! ## Internal Function Signature -/

/-- Type signature for local variables -/
abbrev TSig (var_t : Type) := List (var_t × Ty)

/-- Lowered signature (just sizes) -/
abbrev LSig := List Nat

def TSig.toLSig (sig : TSig var_t) : LSig :=
  sig.map (fun (_, ty) => ty.size)

/-- Internal function definition -/
structure InternalFn (var_t fn_name_t action : Type) where
  name : fn_name_t
  argSpec : TSig var_t
  retType : Ty
  body : action

def InternalFn.mapBody (f : α → β) (fn : InternalFn var_t fn_name_t α) : InternalFn var_t fn_name_t β :=
  { fn with body := f fn.body }

/-! ## Type ID for debugging -/

def Ty.id : Ty → String
  | .bits sz => s!"bits_{sz}"
  | .enum sig => sig.name
  | .struct name _ => name
  | .array elemType len => s!"array_{len}_{elemType.id}"

/-! ## DecidableEq for denote -/

/-- Helper: check all elements of finite function for equality -/
def finFunEqDec {n : Nat} {α : Type} [DecidableEq α] (f g : Fin n → α) : Decidable (f = g) := by
  induction n with
  | zero => exact isTrue (funext (fun i => i.elim0))
  | succ n ih =>
    -- Check the last element and recurse
    let f' : Fin n → α := fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩
    let g' : Fin n → α := fun i => g ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩
    match ih f' g' with
    | isFalse hne =>
        apply isFalse
        intro heq
        apply hne
        funext i
        have := congrFun heq ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩
        exact this
    | isTrue heq =>
        let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
        if hlast : f last = g last then
          apply isTrue
          funext i
          if hi : i.val < n then
            have := congrFun heq ⟨i.val, hi⟩
            exact this
          else
            have := Nat.eq_of_lt_succ_of_not_lt i.isLt hi
            have : i = last := Fin.ext this
            rw [this]
            exact hlast
        else
          apply isFalse
          intro heq'
          apply hlast
          exact congrFun heq' last

mutual
  /-- DecidableEq for Ty.denote -/
  def Ty.decEq : (ty : Ty) → DecidableEq ty.denote
    | .bits sz => fun (a : BitVec sz) (b : BitVec sz) => decEq a b
    | .enum sig => fun (a : BitVec sig.bitsize) (b : BitVec sig.bitsize) => decEq a b
    | .struct _ fields => fieldsDecEq fields
    | .array elemType len => fun f g =>
        @finFunEqDec len elemType.denote (Ty.decEq elemType) f g

  def fieldsDecEq : (fields : List (String × Ty)) → DecidableEq (fieldsDenote fields)
    | [] => fun _ _ => isTrue rfl  -- Unit has one element
    | (_, ty) :: rest =>
        fun (a1, r1) (a2, r2) =>
          match Ty.decEq ty a1 a2, fieldsDecEq rest r1 r2 with
          | isTrue ha, isTrue hr => isTrue (by rw [ha, hr])
          | isFalse ha, _ => isFalse (fun h => ha (Prod.mk.inj h).1)
          | _, isFalse hr => isFalse (fun h => hr (Prod.mk.inj h).2)
end

instance (ty : Ty) : DecidableEq ty.denote := Ty.decEq ty

end Koika
