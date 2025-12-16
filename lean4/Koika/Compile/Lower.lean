/-
  Koika/Compile/Lower.lean - Port of coq/Lowering.v
  Compilation from typed ASTs to lowered ASTs
-/

import Koika.Types
import Koika.Primitives
import Koika.TypedSyntax
import Koika.Compile.Lowered

namespace Koika

/-! ## Value/Bits Conversion -/

/-- Convert a typed value to bits -/
def bitsOfValue {tau : Ty} : tau.denote → BitVec tau.size :=
  Apply.packValue tau

/-- Convert bits to a typed value -/
def valueOfBits {tau : Ty} : BitVec tau.size → tau.denote :=
  Apply.unpackValue tau

/-! ## Lower External Signature -/

/-- Lower an external signature to circuit level -/
def lowerExternalSig (sig : ExternalSig) : CExternalSig :=
  { argSize := sig.argType.size
    retSize := sig.retType.size }

/-! ## Lower Primitives -/

/-- Compute total size of struct fields -/
def structTotalSize (fields : List (String × Ty)) : Nat :=
  fields.foldl (fun acc (_, ty) => acc + ty.size) 0

/-- Compute offset to a field in a struct -/
def fieldOffset (fields : List (String × Ty)) (idx : Nat) : Nat :=
  fields.drop (idx + 1) |>.foldl (fun acc (_, ty) => acc + ty.size) 0

/-- Compute size of a field in a struct -/
def fieldWidth (fields : List (String × Ty)) (idx : Nat) : Nat :=
  match fields[idx]? with
  | some (_, ty) => ty.size
  | none => 0

/-- Lower a typed unary operation to a circuit-level operation -/
def lowerFn1 (fn : Typed.Fn1) : Typed.FBits1 :=
  match fn with
  | .display fn => .lowered (.displayBits fn)
  | .conv tau .pack => .slice tau.size 0 tau.size  -- Identity: extract all bits
  | .conv tau .unpack => .slice tau.size 0 tau.size  -- Identity: extract all bits
  | .conv tau .ignore => .lowered (.ignoreBits tau.size)
  | .bits1 fn => fn
  | .struct1 .getField _ fields idx =>
      -- Extract field from packed struct (fields are packed MSB-first)
      .slice (structTotalSize fields) (fieldOffset fields idx) (fieldWidth fields idx)
  | .array1 .getElement elemTy len idx =>
      -- Extract element from packed array (elements are packed MSB-first)
      let elemSize := elemTy.size
      let totalSize := len * elemSize
      let offset := (len - 1 - idx) * elemSize
      .slice totalSize offset elemSize

/-- Lower a typed binary operation to circuit-level operations -/
def lowerFn2 (fn : Typed.Fn2) : Typed.FBits2 :=
  match fn with
  | .eq tau negate => .eqBits tau.size negate
  | .bits2 fn => fn
  | .struct2 .substField _ fields idx =>
      -- Substitute field in packed struct (fields are packed MSB-first)
      .sliceSubst (structTotalSize fields) (fieldOffset fields idx) (fieldWidth fields idx)
  | .array2 .substElement elemTy len idx =>
      -- Substitute element in packed array (elements are packed MSB-first)
      let elemSize := elemTy.size
      let totalSize := len * elemSize
      let offset := (len - 1 - idx) * elemSize
      .sliceSubst totalSize offset elemSize

/-! ## Main Lowering Pass -/

section Lower

variable {reg_t ext_fn_t : Type}
variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-- Lowered register type function -/
def lowerR (r : reg_t) : Nat := (R r).size

/-- Lowered external signature function -/
def lowerSigma (f : ext_fn_t) : CExternalSig := lowerExternalSig (Sigma f)

/-! ## Size Equality Lemmas -/

/-- The argument size after lowering matches the circuit signature -/
theorem arg1_size_eq (fn : Typed.Fn1) :
    (Sig.arg1 fn).size = (Circuit.sig1 (lowerFn1 fn)).1 := by
  cases fn <;> simp [Sig.arg1, lowerFn1, Circuit.sig1] <;> try rfl
  all_goals sorry  -- These require proving structTotalSize = Ty.size for struct

/-- The return size after lowering matches the circuit signature -/
theorem ret1_size_eq (fn : Typed.Fn1) :
    (Sig.ret1 fn).size = (Circuit.sig1 (lowerFn1 fn)).2 := by
  cases fn <;> simp [Sig.ret1, lowerFn1, Circuit.sig1] <;> try rfl
  all_goals sorry

/-- The first argument size after lowering matches the circuit signature -/
theorem args2_1_size_eq (fn : Typed.Fn2) :
    (Sig.args2 fn).1.size = (Circuit.sig2 (lowerFn2 fn)).1 := by
  cases fn <;> simp [Sig.args2, lowerFn2, Circuit.sig2] <;> try rfl
  all_goals sorry

/-- The second argument size after lowering matches the circuit signature -/
theorem args2_2_size_eq (fn : Typed.Fn2) :
    (Sig.args2 fn).2.size = (Circuit.sig2 (lowerFn2 fn)).2.1 := by
  cases fn <;> simp [Sig.args2, lowerFn2, Circuit.sig2] <;> try rfl
  all_goals sorry

/-- The return size after lowering matches the circuit signature -/
theorem ret2_size_eq (fn : Typed.Fn2) :
    (Sig.ret2 fn).size = (Circuit.sig2 (lowerFn2 fn)).2.2 := by
  cases fn <;> simp [Sig.ret2, lowerFn2, Circuit.sig2] <;> try rfl
  all_goals sorry

/-- Cast an LAction to a different size (when sizes are proven equal) -/
def castLAction (h : sz = sz') :
    LAction reg_t ext_fn_t (lowerR R) (lowerSigma Sigma) sig sz →
    LAction reg_t ext_fn_t (lowerR R) (lowerSigma Sigma) sig sz' :=
  fun a => h ▸ a

/-- Lower a typed action to a lowered action -/
def lowerAction : Action reg_t ext_fn_t R Sigma sig tau →
                  LAction reg_t ext_fn_t (lowerR R) (lowerSigma Sigma) (lowerSig sig) tau.size
  | .fail tau => .fail tau.size
  | .var m => .var m.varName (lowerMember m)
  | .const v => .const (bitsOfValue v)
  | .assign m e => .assign m.varName (lowerMember m) (lowerAction e)
  | .seq a b => .seq (lowerAction a) (lowerAction b)
  | .bind v e body => .bind v (lowerAction e) (lowerAction body)
  | .if c t f => .if (lowerAction c) (lowerAction t) (lowerAction f)
  | .read p r => .read p r
  | .write p r v => .write p r (lowerAction v)
  | .unop fn a =>
      let loweredFn := lowerFn1 fn
      let loweredArg := castLAction R Sigma (arg1_size_eq fn) (lowerAction a)
      let result := LAction.unop loweredFn loweredArg
      castLAction R Sigma (ret1_size_eq fn).symm result
  | .binop fn a1 a2 =>
      let loweredFn := lowerFn2 fn
      let loweredArg1 := castLAction R Sigma (args2_1_size_eq fn) (lowerAction a1)
      let loweredArg2 := castLAction R Sigma (args2_2_size_eq fn) (lowerAction a2)
      let result := LAction.binop loweredFn loweredArg1 loweredArg2
      castLAction R Sigma (ret2_size_eq fn).symm result
  | .extCall fn a => .extCall fn (lowerAction a)

/-- Lower a typed rule to a lowered rule -/
def lowerRule (rl : Rule reg_t ext_fn_t R Sigma)
    : LRule reg_t ext_fn_t (lowerR R) (lowerSigma Sigma) :=
  lowerAction R Sigma rl

end Lower

/-! ## Lower Register State -/

/-- Lower register state from typed to bitvectors -/
def lowerRegState {reg_t : Type}
    (R : reg_t → Ty)
    (env : (r : reg_t) → (R r).denote)
    : (r : reg_t) → BitVec (R r).size :=
  fun r => bitsOfValue (env r)

end Koika
