/-
  Koika/TypedSyntaxFunctions.lean - Port of coq/TypedSyntaxFunctions.v
  Functions defined on typed ASTs

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/TypedSyntaxFunctions.v
-/

import Koika.Types
import Koika.Primitives
import Koika.TypedSyntax
import Koika.Syntax

namespace Koika

/-! ## Scheduler Utilities -/

/-- Extract all rule names mentioned in a scheduler -/
def schedulerRules {rule_name_t : Type} : Scheduler Unit rule_name_t → List rule_name_t
  | .done => []
  | .cons r s => r :: schedulerRules s
  | .try_ r s1 s2 => r :: schedulerRules s1 ++ schedulerRules s2
  | .pos _ s => schedulerRules s

/-- Get all possible paths through a scheduler -/
def allSchedulerPaths {rule_name_t : Type} : Scheduler Unit rule_name_t → List (List rule_name_t)
  | .done => [[]]
  | .cons r s => (allSchedulerPaths s).map (r :: ·)
  | .try_ r s1 s2 => (allSchedulerPaths s1).map (r :: ·) ++ (allSchedulerPaths s2).map (r :: ·)
  | .pos _ s => allSchedulerPaths s

/-! ## Action Traversals -/

section ActionTraversals

variable {reg_t ext_fn_t : Type}
variable {R : reg_t → Ty}
variable {Sigma : ext_fn_t → ExternalSig}

/-- Read/Write event type -/
inductive RWEvent where
  | read
  | write
  deriving DecidableEq, Repr

/-- Footprint entry: register with event and port -/
abbrev FootprintEntry (reg_t : Type) := reg_t × RWEvent × Port

/-- Compute the register access footprint of an action -/
def actionFootprint' {sig : List (String × Ty)} {tau : Ty}
    (acc : List (FootprintEntry reg_t))
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    : List (FootprintEntry reg_t) :=
  match a with
  | .fail _ | .var _ | .const _ => acc
  | .assign _ ex => actionFootprint' acc ex
  | .seq r1 r2 => actionFootprint' (actionFootprint' acc r1) r2
  | .bind _ ex body => actionFootprint' (actionFootprint' acc ex) body
  | .if cond tbranch fbranch =>
      actionFootprint' (actionFootprint' (actionFootprint' acc cond) tbranch) fbranch
  | .read port idx => (idx, .read, port) :: acc
  | .write port idx value => (idx, .write, port) :: actionFootprint' acc value
  | .unop _ arg => actionFootprint' acc arg
  | .binop _ arg1 arg2 => actionFootprint' (actionFootprint' acc arg1) arg2
  | .extCall _ arg => actionFootprint' acc arg

/-- Compute the register access footprint of an action -/
def actionFootprint {sig : List (String × Ty)} {tau : Ty}
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    : List (FootprintEntry reg_t) :=
  actionFootprint' [] a

/-- Get unique registers accessed by an action -/
def actionRegisters [DecidableEq reg_t] {sig : List (String × Ty)} {tau : Ty}
    (a : Action reg_t ext_fn_t R Sigma sig tau)
    : List reg_t :=
  (actionFootprint a).map (·.1) |>.eraseDups

/-! ## Purity and Static Analysis -/

/-- Check if an action is pure (no side effects) -/
def isPure {sig : List (String × Ty)} {tau : Ty}
    (a : Action reg_t ext_fn_t R Sigma sig tau) : Bool :=
  match a with
  | .fail _ => false
  | .var _ => true
  | .const _ => true
  | .assign _ _ => false
  | .seq r1 r2 => isPure r1 && isPure r2
  | .bind _ ex body => isPure ex && isPure body
  | .if cond tbranch fbranch => isPure cond && isPure tbranch && isPure fbranch
  | .read _ _ => false
  | .write _ _ _ => false
  | .unop _ arg => isPure arg
  | .binop _ arg1 arg2 => isPure arg1 && isPure arg2
  | .extCall _ _ => false

/-- Check if an action returns zero -/
def returnsZero {sig : List (String × Ty)} {tau : Ty}
    (a : Action reg_t ext_fn_t R Sigma sig tau) : Bool :=
  match a with
  | .fail _ => false
  | .var _ => false
  | .const v =>
      -- Check if value is all zeros
      match tau with
      | .bits n => (Apply.packValue (.bits n) v) == 0
      | _ => false
  | .assign _ _ => false
  | .seq _ r2 => returnsZero r2
  | .bind _ _ body => returnsZero body
  | .if _ tbranch fbranch => returnsZero tbranch && returnsZero fbranch
  | .read _ _ => false
  | .write _ _ _ => false
  | .unop _ _ => false
  | .binop _ _ _ => false
  | .extCall _ _ => false

/-- Compute the size (number of AST nodes) of an action -/
def actionSize {sig : List (String × Ty)} {tau : Ty}
    (a : Action reg_t ext_fn_t R Sigma sig tau) : Nat :=
  1 + match a with
  | .fail _ | .var _ | .const _ | .read _ _ => 0
  | .assign _ ex => actionSize ex
  | .seq a1 a2 => actionSize a1 + actionSize a2
  | .bind _ ex body => actionSize ex + actionSize body
  | .if cond tbranch fbranch => actionSize cond + actionSize tbranch + actionSize fbranch
  | .write _ _ value => actionSize value
  | .unop _ arg => actionSize arg
  | .binop _ arg1 arg2 => actionSize arg1 + actionSize arg2
  | .extCall _ arg => actionSize arg

/-- Maximum log size needed for an action -/
def ruleMaxLogSize {sig : List (String × Ty)} {tau : Ty}
    (a : Action reg_t ext_fn_t R Sigma sig tau) : Nat :=
  match a with
  | .fail _ | .var _ | .const _ => 0
  | .assign _ ex => ruleMaxLogSize ex
  | .seq r1 r2 => ruleMaxLogSize r1 + ruleMaxLogSize r2
  | .bind _ ex body => ruleMaxLogSize ex + ruleMaxLogSize body
  | .if cond tbranch fbranch =>
      ruleMaxLogSize cond + max (ruleMaxLogSize tbranch) (ruleMaxLogSize fbranch)
  | .read _ _ => 1
  | .write _ _ value => 1 + ruleMaxLogSize value
  | .unop _ arg => ruleMaxLogSize arg
  | .binop _ arg1 arg2 => ruleMaxLogSize arg1 + ruleMaxLogSize arg2
  | .extCall _ arg => ruleMaxLogSize arg

/-! ## Subterm Search -/

/-- Wrapper for any action (existential over sig and tau) -/
inductive AnyAction (reg_t ext_fn_t : Type) (R : reg_t → Ty) (Sigma : ext_fn_t → ExternalSig) where
  | mk : {sig : List (String × Ty)} → {tau : Ty} →
         Action reg_t ext_fn_t R Sigma sig tau → AnyAction reg_t ext_fn_t R Sigma

/-- Check if any subterm satisfies a predicate -/
def existsSubterm (f : AnyAction reg_t ext_fn_t R Sigma → Bool)
    {sig : List (String × Ty)} {tau : Ty}
    (a : Action reg_t ext_fn_t R Sigma sig tau) : Bool :=
  f (.mk a) ||
  match a with
  | .fail _ | .var _ | .const _ | .read _ _ => false
  | .assign _ ex => existsSubterm f ex
  | .seq r1 r2 => existsSubterm f r1 || existsSubterm f r2
  | .bind _ ex body => existsSubterm f ex || existsSubterm f body
  | .if cond tbranch fbranch =>
      existsSubterm f cond || existsSubterm f tbranch || existsSubterm f fbranch
  | .write _ _ value => existsSubterm f value
  | .unop _ arg => existsSubterm f arg
  | .binop _ arg1 arg2 => existsSubterm f arg1 || existsSubterm f arg2
  | .extCall _ arg => existsSubterm f arg

/-! ## Register History Analysis (Tribool-based) -/

/-- Three-valued boolean for static analysis -/
inductive Tribool where
  | true
  | false
  | unknown
  deriving DecidableEq, Repr

namespace Tribool

def and : Tribool → Tribool → Tribool
  | .false, _ | _, .false => .false
  | .true, .true => .true
  | _, _ => .unknown

def or : Tribool → Tribool → Tribool
  | .true, _ | _, .true => .true
  | .false, .false => .false
  | _, _ => .unknown

def not : Tribool → Tribool
  | .true => .false
  | .false => .true
  | .unknown => .unknown

def join : Tribool → Tribool → Tribool
  | .true, .true => .true
  | .false, .false => .false
  | _, _ => .unknown

instance : AndOp Tribool := ⟨Tribool.and⟩
instance : OrOp Tribool := ⟨Tribool.or⟩

end Tribool

/-- Register access history -/
structure RegisterHistory where
  hr0 : Tribool := .false  -- read on port 0
  hr1 : Tribool := .false  -- read on port 1
  hw0 : Tribool := .false  -- write on port 0
  hw1 : Tribool := .false  -- write on port 1
  hcf : Tribool := .true   -- conflict-free
  deriving Repr

def RegisterHistory.empty : RegisterHistory :=
  { hr0 := .false, hr1 := .false, hw0 := .false, hw1 := .false, hcf := .true }

def RegisterHistory.unknown : RegisterHistory :=
  { hr0 := .unknown, hr1 := .unknown, hw0 := .unknown, hw1 := .unknown, hcf := .false }

def RegisterHistory.join (h1 h2 : RegisterHistory) : RegisterHistory :=
  { hr0 := Tribool.join h1.hr0 h2.hr0
    hr1 := Tribool.join h1.hr1 h2.hr1
    hw0 := Tribool.join h1.hw0 h2.hw0
    hw1 := Tribool.join h1.hw1 h2.hw1
    hcf := Tribool.join h1.hcf h2.hcf }

/-- Register classification based on access pattern -/
inductive RegisterKind where
  | value     -- Never accessed with conflicts
  | wire      -- Only read0, write0
  | register  -- No port-1 access
  | ehr       -- Needs EHR semantics
  deriving DecidableEq, Repr

/-- Classify a register based on its history -/
def computeRegisterKind (history : RegisterHistory) : RegisterKind :=
  match history with
  | { hcf := .true, .. } => .value
  | { hr1 := .false, hw1 := .false, .. } => .register
  | { hr0 := .false, hw1 := .false, .. } => .wire
  | _ => .ehr

end ActionTraversals

end Koika
