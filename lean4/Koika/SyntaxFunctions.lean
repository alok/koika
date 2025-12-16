/-
  Koika/SyntaxFunctions.lean - Port of coq/SyntaxFunctions.v
  Functions on untyped ASTs, including error localization

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/SyntaxFunctions.v
-/

import Koika.Types
import Koika.Syntax

namespace Koika

/-! ## Path-based Error Localization -/

/-- Path into an AST for error localization -/
inductive Path where
  | this : Path
  | that : Path → Nat → Path
  deriving DecidableEq, Repr, Inhabited

namespace Path

/-- Reverse a path (for matching during traversal) -/
def rev (acc : Path) : Path → Path
  | .this => acc
  | .that p n => rev (.that acc n) p

/-- Check if we're on track to a target path -/
def onTrack (revTarget currentPath : Path) : Option Path :=
  match revTarget, currentPath with
  | .this, _ => some .this
  | p, .this => some p
  | .that p n, .that _ n' =>
      if n == n' then some p else none

end Path

/-! ## Untyped Action Utilities -/

mutual
/-- Compute the size of an untyped action AST -/
partial def uactionSize {pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (ua : UAction pos_t var_t fn_name_t reg_t ext_fn_t) : Nat :=
  1 + match ua with
  | .error _ | .fail _ | .var _ | .const _ _ | .read _ _ => 0
  | .assign _ ex => uactionSize ex
  | .seq a1 a2 => uactionSize a1 + uactionSize a2
  | .bind _ ex body => uactionSize ex + uactionSize body
  | .if cond tbranch fbranch =>
      uactionSize cond + uactionSize tbranch + uactionSize fbranch
  | .write _ _ value => uactionSize value
  | .unop _ arg => uactionSize arg
  | .binop _ arg1 arg2 => uactionSize arg1 + uactionSize arg2
  | .extCall _ arg => uactionSize arg
  | .intCall fn args =>
      uactionSize fn.body + args.foldl (fun acc a => acc + uactionSize a) 0
  | .pos _ e => uactionSize e
  | .sugar s => usugarSize s

/-- Compute the size of a sugar AST -/
partial def usugarSize {pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (us : USugar pos_t var_t fn_name_t reg_t ext_fn_t) : Nat :=
  1 + match us with
  | .errorInAst | .skip | .constBits _ _ | .constString _ | .constEnum _ _ => 0
  | .progn aa => aa.foldl (fun acc a => acc + uactionSize a) 0
  | .let bindings body =>
      bindings.foldl (fun acc (_, v) => acc + uactionSize v) 0 + uactionSize body
  | .when cond body => uactionSize cond + uactionSize body
  | .switch _ default branches =>
      branches.foldl (fun acc (_, b) => acc + uactionSize b) 0 + uactionSize default
  | .structInit _ _ inits =>
      inits.foldl (fun acc (_, v) => acc + uactionSize v) 0
  | .arrayInit _ elements =>
      elements.foldl (fun acc e => acc + uactionSize e) 0
end

/-! ## AST Traversal Utilities -/

/-- Map a function over all subactions in sugar (shallow) -/
def mapUSugar {pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (f : UAction pos_t var_t fn_name_t reg_t ext_fn_t → UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    : USugar pos_t var_t fn_name_t reg_t ext_fn_t → USugar pos_t var_t fn_name_t reg_t ext_fn_t
  | .errorInAst => .errorInAst
  | .skip => .skip
  | .constBits sz bs => .constBits sz bs
  | .constString s => .constString s
  | .constEnum sig v => .constEnum sig v
  | .progn aa => .progn (aa.map f)
  | .let bindings body => .let (bindings.map fun (v, e) => (v, f e)) (f body)
  | .when c b => .when (f c) (f b)
  | .switch v d branches => .switch (f v) (f d) (branches.map fun (c, b) => (f c, f b))
  | .structInit name fields inits => .structInit name fields (inits.map fun (n, v) => (n, f v))
  | .arrayInit ty elems => .arrayInit ty (elems.map f)

/-- Map a function over all subactions (shallow) -/
def mapUAction {pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (f : UAction pos_t var_t fn_name_t reg_t ext_fn_t → UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t → UAction pos_t var_t fn_name_t reg_t ext_fn_t
  | .error e => .error e
  | .fail ty => .fail ty
  | .var v => .var v
  | .const ty c => .const ty c
  | .assign v ex => .assign v (f ex)
  | .seq a1 a2 => .seq (f a1) (f a2)
  | .bind v ex body => .bind v (f ex) (f body)
  | .if c t e => .if (f c) (f t) (f e)
  | .read p r => .read p r
  | .write p r v => .write p r (f v)
  | .unop op arg => .unop op (f arg)
  | .binop op a1 a2 => .binop op (f a1) (f a2)
  | .extCall fn arg => .extCall fn (f arg)
  | .intCall fn args => .intCall (fn.mapBody f) (args.map f)
  | .pos p e => .pos p (f e)
  | .sugar s => .sugar (mapUSugar f s)

/-- Fold over all subactions in sugar -/
def foldUSugar {α pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (f : α → UAction pos_t var_t fn_name_t reg_t ext_fn_t → α)
    (init : α) : USugar pos_t var_t fn_name_t reg_t ext_fn_t → α
  | .errorInAst | .skip | .constBits _ _ | .constString _ | .constEnum _ _ => init
  | .progn aa => aa.foldl f init
  | .let bindings body => f (bindings.foldl (fun acc (_, e) => f acc e) init) body
  | .when c b => f (f init c) b
  | .switch v d branches =>
      let acc := f (f init v) d
      branches.foldl (fun acc (c, b) => f (f acc c) b) acc
  | .structInit _ _ inits => inits.foldl (fun acc (_, v) => f acc v) init
  | .arrayInit _ elems => elems.foldl f init

/-- Fold over all subactions -/
def foldUAction {α pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (f : α → UAction pos_t var_t fn_name_t reg_t ext_fn_t → α)
    (init : α) : UAction pos_t var_t fn_name_t reg_t ext_fn_t → α
  | .error _ | .fail _ | .var _ | .const _ _ | .read _ _ => init
  | .assign _ ex => f init ex
  | .seq a1 a2 => f (f init a1) a2
  | .bind _ ex body => f (f init ex) body
  | .if c t e => f (f (f init c) t) e
  | .write _ _ v => f init v
  | .unop _ arg => f init arg
  | .binop _ a1 a2 => f (f init a1) a2
  | .extCall _ arg => f init arg
  | .intCall fn args => args.foldl f (f init fn.body)
  | .pos _ e => f init e
  | .sugar s => foldUSugar f init s

/-- Check if an action contains any subterm satisfying a predicate -/
partial def existsUAction {pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (p : UAction pos_t var_t fn_name_t reg_t ext_fn_t → Bool)
    (a : UAction pos_t var_t fn_name_t reg_t ext_fn_t) : Bool :=
  p a || foldUAction (fun acc sub => acc || existsUAction p sub) false a

/-- Collect all registers mentioned in an action -/
partial def collectRegisters {pos_t var_t fn_name_t reg_t ext_fn_t : Type} [DecidableEq reg_t]
    (a : UAction pos_t var_t fn_name_t reg_t ext_fn_t) : List reg_t :=
  go [] a
where
  go (acc : List reg_t) : UAction pos_t var_t fn_name_t reg_t ext_fn_t → List reg_t
    | .read _ r => if acc.contains r then acc else r :: acc
    | .write _ r v => go (if acc.contains r then acc else r :: acc) v
    | .assign _ ex => go acc ex
    | .seq a1 a2 => go (go acc a1) a2
    | .bind _ ex body => go (go acc ex) body
    | .if c t e => go (go (go acc c) t) e
    | .unop _ arg => go acc arg
    | .binop _ a1 a2 => go (go acc a1) a2
    | .extCall _ arg => go acc arg
    | .intCall fn args => args.foldl go (go acc fn.body)
    | .pos _ e => go acc e
    | .sugar s => goSugar acc s
    | .error _ | .fail _ | .var _ | .const _ _ => acc
  goSugar (acc : List reg_t) : USugar pos_t var_t fn_name_t reg_t ext_fn_t → List reg_t
    | .progn aa => aa.foldl go acc
    | .let bindings body => go (bindings.foldl (fun a (_, e) => go a e) acc) body
    | .when c b => go (go acc c) b
    | .switch v d branches =>
        branches.foldl (fun a (c, b) => go (go a c) b) (go (go acc v) d)
    | .structInit _ _ inits => inits.foldl (fun a (_, v) => go a v) acc
    | .arrayInit _ elems => elems.foldl go acc
    | .errorInAst | .skip | .constBits _ _ | .constString _ | .constEnum _ _ => acc

/-! ## Scheduler Utilities -/

/-- Get all rule names from a scheduler -/
def schedulerRuleNames {rule_name_t : Type} : Scheduler Unit rule_name_t → List rule_name_t
  | .done => []
  | .cons r s => r :: schedulerRuleNames s
  | .try_ r s1 s2 => r :: schedulerRuleNames s1 ++ schedulerRuleNames s2
  | .pos _ s => schedulerRuleNames s

/-- Count the number of rules in a scheduler -/
def schedulerSize {rule_name_t : Type} : Scheduler Unit rule_name_t → Nat
  | .done => 0
  | .cons _ s => 1 + schedulerSize s
  | .try_ _ s1 s2 => 1 + schedulerSize s1 + schedulerSize s2
  | .pos _ s => schedulerSize s

end Koika
