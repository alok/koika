/-
  Koika/Desugaring.lean - Port of coq/Desugaring.v
  Desugaring of untyped actions

  This module transforms syntactic sugar constructs (USugar) into
  core untyped actions (UAction). The desugaring phase can produce
  larger terms than its inputs.

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/Desugaring.v
-/

import Koika.Types
import Koika.Syntax
import Koika.Primitives

namespace Koika

/-! ## Helper Functions -/

/-- Convert ASCII character to 8-bit bitvector -/
def bitsOfChar (c : Char) : BitVec 8 :=
  BitVec.ofNat 8 c.val.toNat

/-- Convert string to array of bytes (8-bit bitvectors) -/
def arrayOfBytes (s : String) : Fin s.length → BitVec 8 :=
  fun i => bitsOfChar (s.get ⟨i.val⟩)

/-- Lookup enum member by name, return index if found -/
def lookupEnumMember (sig : EnumSig) (memberName : String) : Option (Fin sig.size) :=
  sig.members.findIdx? (· == memberName) >>= fun idx =>
    if h : idx < sig.size then
      some ⟨idx, h⟩
    else
      none

/-- Enumerate a list with indices -/
def List.zipWithIndex {α : Type _} (xs : List α) : List (Nat × α) :=
  let rec go (n : Nat) (xs : List α) : List (Nat × α) :=
    match xs with
    | [] => []
    | x :: xs => (n, x) :: go (n + 1) xs
  go 0 xs

/-! ## Syntax Macros

These match the Coq SyntaxMacros.v functions used during desugaring.
-/

namespace SyntaxMacros

variable {pos_t var_t fn_name_t reg_t ext_fn_t : Type}

/-- Skip action (unit value): 0-bit constant -/
def uskip : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  .const unitTy (0 : BitVec 0)

/-- Sequence multiple actions using USeq -/
def uprogn : List (UAction pos_t var_t fn_name_t reg_t ext_fn_t) → UAction pos_t var_t fn_name_t reg_t ext_fn_t
  | [] => uskip
  | [a] => a
  | a :: rest => .seq a (uprogn rest)

/-- Initialize a type to its default (zero) value -/
def uinit (tau : Ty) : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  let zeroes : BitVec tau.size := 0
  .unop (.conv (.unpack tau)) (.const (.bits tau.size) zeroes)

/-- Initialize a struct with field values -/
def ustructInit (name : String) (fields : List (String × Ty))
    (inits : List (String × UAction pos_t var_t fn_name_t reg_t ext_fn_t))
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  let sig : Ty := .struct name fields
  let empty := uinit sig
  let usubst (f : String) := UAction.binop (.struct2 (.substField f))
  inits.foldl (fun acc (f, a) => usubst f acc a) empty

/-- Switch statement with multiple branches -/
def uswitch (var default : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    (branches : List (UAction pos_t var_t fn_name_t reg_t ext_fn_t × UAction pos_t var_t fn_name_t reg_t ext_fn_t))
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  branches.foldr
    (fun (label, action) acc =>
      .if (.binop (.eq false) var label) action acc)
    default

end SyntaxMacros

/-! ## Desugaring Functions -/

mutual

/-- Main desugaring function with register/external function remapping.
  This allows desugaring actions that reference one set of registers/external
  functions while producing actions that reference a different set (used by UCallModule).
-/
unsafe def desugarAction' {pos_t var_t fn_name_t reg_t ext_fn_t reg_t' ext_fn_t' : Type}
    (pos : pos_t)
    (fR : reg_t' → reg_t)
    (fSigma : ext_fn_t' → ext_fn_t)
    (a : UAction pos_t var_t fn_name_t reg_t' ext_fn_t')
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  let d := desugarAction' pos fR fSigma
  match a with
  | .error err => .error err
  | .fail tau => .fail tau
  | .var v => .var v
  | .const tau cst => .const tau cst
  | .assign v ex => .assign v (d ex)
  | .seq a1 a2 => .seq (d a1) (d a2)
  | .bind v ex body => .bind v (d ex) (d body)
  | .if cond tbranch fbranch => .if (d cond) (d tbranch) (d fbranch)
  | .read port idx => .read port (fR idx)
  | .write port idx value => .write port (fR idx) (d value)
  | .unop fn arg => .unop fn (d arg)
  | .binop fn arg1 arg2 => .binop fn (d arg1) (d arg2)
  | .extCall fn arg => .extCall (fSigma fn) (d arg)
  | .intCall fn args =>
      .intCall (fn.mapBody d) (args.map d)
  | .pos p e => .pos p (d e)
  | .sugar s => desugar pos fR fSigma s

unsafe def desugar {pos_t var_t fn_name_t reg_t ext_fn_t reg_t' ext_fn_t' : Type}
    (pos : pos_t)
    (fR : reg_t' → reg_t)
    (fSigma : ext_fn_t' → ext_fn_t)
    (s : USugar pos_t var_t fn_name_t reg_t' ext_fn_t')
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  let d := desugarAction' pos fR fSigma
  match s with
  | .errorInAst =>
      .error {
        pos := pos
        msg := .explicitErrorInAst
      }
  | .skip =>
      SyntaxMacros.uskip
  | .constBits sz bs =>
      .const (.bits sz) bs
  | .constString str =>
      -- String becomes array of 8-bit bytes
      let len := str.length
      let arr := arrayOfBytes str
      .const (.array (.bits 8) len) arr
  | .constEnum sig memberName =>
      match lookupEnumMember sig memberName with
      | some idx =>
          -- Look up the bit pattern for this enum member
          -- For now, we use the index directly as the bit pattern
          -- In a full implementation, this should look up sig.bitpatterns[idx]
          let bitPattern : BitVec sig.bitsize := BitVec.ofNat sig.bitsize idx.val
          .const (.enum sig) bitPattern
      | none =>
          .error {
            pos := pos
            msg := .unboundEnumMember memberName sig
          }
  | .progn aa =>
      SyntaxMacros.uprogn (aa.map d)
  | .let bindings body =>
      -- Desugar let to nested binds
      bindings.foldr
        (fun (var, a) acc => .bind var (d a) acc)
        (d body)
  | .when cond body =>
      -- When is if with fail in else branch
      .if (d cond) (d body) (.fail unitTy)
  | .structInit name fields inits =>
      let initsDesugared := inits.map fun (f, a) => (f, d a)
      SyntaxMacros.ustructInit name fields initsDesugared
  | .arrayInit elemType elements =>
      -- Array initialization: start with zero array, substitute each element
      let len := elements.length
      let sig : Ty := .array elemType len
      let usubst (pos : Nat) :=
        UAction.binop (.array2 (.substElement pos))
      let empty := SyntaxMacros.uinit sig
      -- Use zipWithIndex to get (index, element) pairs
      (List.zipWithIndex elements).foldl
        (fun acc (pos, a) => usubst pos acc (d a))
        empty
  | .switch var default branches =>
      let branchesDesugared := branches.map fun (cond, body) => (d cond, d body)
      SyntaxMacros.uswitch (d var) (d default) branchesDesugared

end

/-! ## Top-level Desugaring -/

/-- Desugar an action with identity register/external function mappings -/
unsafe def desugarAction {pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (pos : pos_t)
    (a : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  desugarAction' pos id id a

end Koika
