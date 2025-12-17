/-
  Koika/Common.lean - Port of coq/Common.v
  Shared utilities

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/Common.v
-/

namespace Koika

/-! ## Option utilities -/

/-- Bind for Option monad -/
def optBind {A B : Type} (o : Option A) (f : A → Option B) : Option B :=
  o.bind f

/-- Convert Option to Result with default error -/
def optResult {S F : Type} (o : Option S) (f : F) : Except F S :=
  match o with
  | some x => .ok x
  | none => .error f

/-! ## Result type -/

/-- Map over the error type of a result -/
def Except.mapError {S F1 F2 : Type} (fn : F1 → F2) (r : Except F1 S) : Except F2 S :=
  match r with
  | .ok s => .ok s
  | .error f => .error (fn f)

/-- Check if result is success -/
def Except.isSuccess {S F : Type} (r : Except F S) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => false

/-- Map over a list with a fallible function -/
def Except.listMap {A B F : Type} (f : A → Except F B) : List A → Except F (List B)
  | [] => .ok []
  | a :: la =>
      match f a with
      | .error e => .error e
      | .ok b =>
          match Except.listMap f la with
          | .error e => .error e
          | .ok lb => .ok (b :: lb)

/-! ## List utilities -/

/-- Find first element matching predicate and return transformed result -/
def List.findOpt {A B : Type} (f : A → Option B) : List A → Option B
  | [] => none
  | x :: l =>
      match f x with
      | some y => some y
      | none => findOpt f l

/-- Sum of a list of natural numbers -/
def List.sum' (n : Nat) (l : List Nat) : Nat :=
  l.foldl (· + ·) n

def List.sum (l : List Nat) : Nat :=
  List.sum' 0 l

/-- Remove duplicates from list -/
def List.dedup {A : Type} [DecidableEq A] (acc : List A) : List A → List A
  | [] => acc
  | a :: l =>
      let acc' := if acc.contains a then acc else a :: acc
      dedup acc' l

/-- Iterate a function n times -/
def iterate (n : Nat) {A : Type} (f : A → A) (init : A) : A :=
  match n with
  | 0 => init
  | n + 1 => f (iterate n f init)

/-- Tail-recursive iterate -/
def iterateTR (n : Nat) {A : Type} (f : A → A) (init : A) : A :=
  match n with
  | 0 => init
  | n + 1 => iterateTR n f (f init)

/-- Generate list [n, n-1, ..., 1, 0] -/
def upto (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: upto n

/-! ## Logarithm -/

/-- Ceiling of log base 2 -/
def log2 (n : Nat) : Nat := Nat.log2 n + 1

/-! ## Projections -/

def andFst {A B : Prop} (h : A ∧ B) : A := h.1
def andSnd {A B : Prop} (h : A ∧ B) : B := h.2

end Koika
