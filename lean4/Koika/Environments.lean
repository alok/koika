/-
  Koika/Environments.lean - Port of coq/Environments.v
  Utilities: Environments used to track variable bindings
-/

import Koika.Types
import Koika.FiniteType

namespace Koika

/-! ## Member - Dependent type tracking membership into a list -/

/-- Proof that element k is part of list sig -/
inductive EnvMember {K : Type} : K → List K → Type where
  | hd : (k : K) → (sig : List K) → EnvMember k (k :: sig)
  | tl : (k : K) → (k' : K) → (sig : List K) → EnvMember k sig → EnvMember k (k' :: sig)

namespace EnvMember

/-- Get the index of a member -/
def idx {K : Type} {sig : List K} {k : K} : EnvMember k sig → Nat
  | hd _ _ => 0
  | tl _ _ _ m => idx m + 1

/-- Map a function over member keys -/
def map {K K' : Type} (f : K → K') {k : K} {ls : List K} :
    EnvMember k ls → EnvMember (f k) (ls.map f)
  | hd k sig => hd (f k) (sig.map f)
  | tl k k' sig m => tl (f k) (f k') (sig.map f) (map f m)

/-- Extend member to list with prefix -/
def «prefix» {K : Type} (pre : List K) {sig : List K} {k : K} :
    EnvMember k sig → EnvMember k (pre ++ sig)
  | m => match pre with
    | [] => m
    | k' :: pre' => tl k k' (pre' ++ sig) («prefix» pre' m)

end EnvMember

/-! ## Context - Dependent typed environment as a list -/

section Contexts

variable {K : Type}
variable {V : K → Type}

/-- Context indexed by a signature -/
inductive Context : (sig : List K) → Type where
  | empty : Context []
  | cons : (k : K) → V k → Context sig → Context (k :: sig)

namespace Context

/-- Head of a non-empty context -/
def hd {k : K} {sig : List K} : Context (V := V) (k :: sig) → V k
  | cons _ v _ => v

/-- Tail of a non-empty context -/
def tl {k : K} {sig : List K} : Context (V := V) (k :: sig) → Context (V := V) sig
  | cons _ _ ctx => ctx

/-- Look up value at a member position -/
def assoc {sig : List K} {k : K} : EnvMember k sig → Context (V := V) sig → V k
  | EnvMember.hd _ _, ctx => hd ctx
  | EnvMember.tl _ _ _ m, ctx => assoc m (Context.tl ctx)

/-- Create a context by providing a value for each member -/
def create : (sig : List K) → (f : ∀ k, EnvMember k sig → V k) → Context (V := V) sig
  | [], _ => empty
  | h :: t, f =>
      cons h (f h (EnvMember.hd h t))
             (create t (fun k m => f k (EnvMember.tl k h t m)))

/-- Replace value at a member position -/
def replace {sig : List K} {k : K} :
    EnvMember k sig → V k → Context (V := V) sig → Context (V := V) sig
  | EnvMember.hd _ _, v, ctx => cons _ v (Context.tl ctx)
  | EnvMember.tl _ k' _ m, v, ctx => cons k' (Context.hd ctx) (replace m v (Context.tl ctx))

/-- Append two contexts -/
def app {sig sig' : List K} : Context (V := V) sig → Context (V := V) sig' → Context (V := V) (sig ++ sig')
  | empty, ctx' => ctx'
  | cons k v ctx, ctx' => cons k v (app ctx ctx')

/-- Map a function over context values (preserving keys) -/
def mapv {V' : K → Type} (f : ∀ k, V k → V' k) :
    {sig : List K} → Context (V := V) sig → Context (V := V') sig
  | [], empty => empty
  | _ :: _, cons k v ctx => cons k (f k v) (mapv f ctx)

/-- Map functions over both keys and values -/
def map {K' : Type} {V' : K' → Type}
    (fK : K → K') (fV : ∀ k, V k → V' (fK k)) :
    {sig : List K} → Context (V := V) sig → Context (V := V') (sig.map fK)
  | [], empty => empty
  | _ :: _, cons k v ctx => cons (fK k) (fV k v) (map fK fV ctx)

/-- Left fold over context -/
def foldl {T : Type} (f : ∀ (k : K) (_v : V k) (_acc : T), T) :
    {sig : List K} → Context (V := V) sig → T → T
  | [], empty, init => init
  | _ :: _, cons k v ctx, init => foldl f ctx (f k v init)

/-- Right fold over context -/
def foldr {T : List K → Type}
    (f : ∀ (sg : List K) (k : K) (_v : V k), T sg → T (k :: sg)) :
    {sig : List K} → Context (V := V) sig → T [] → T sig
  | [], empty, init => init
  | _ :: _, cons k v ctx, init => f _ k v (foldr f ctx init)

end Context

end Contexts

/-! ## Env Typeclass - Finite map interface -/

/-- Signature for value types indexed by keys -/
abbrev ESig (K : Type) := K → Type

/-- Environment typeclass providing finite map operations -/
class Env (K : Type) where
  /-- Type of environment for value signature V -/
  env_t : (V : ESig K) → Type

  /-- Get value for key k -/
  getenv : {V : ESig K} → env_t V → (k : K) → V k

  /-- Update value for key k -/
  putenv : {V : ESig K} → env_t V → (k : K) → V k → env_t V

  /-- Create environment from function -/
  create : {V : ESig K} → (fn : ∀ (k : K), V k) → env_t V

  /-- Finite keys constraint -/
  finite_keys : FiniteType K

  /-- create (getenv ev) = ev -/
  create_getenv_id : ∀ {V : ESig K} (ev : env_t V),
    create (getenv ev) = ev

  /-- Extensionality for create -/
  create_funext : ∀ {V : ESig K} (fn1 fn2 : ∀ k, V k),
    (∀ k, fn1 k = fn2 k) → create fn1 = create fn2

  /-- getenv after create -/
  getenv_create : ∀ {V : ESig K} (fn : ∀ k, V k) (k : K),
    getenv (create fn) k = fn k

  /-- Get after put (same key) -/
  get_put_eq : ∀ {V : ESig K} (ev : env_t V) (k : K) (v : V k),
    getenv (putenv ev k v) k = v

  /-- Get after put (different key) -/
  get_put_neq : ∀ {V : ESig K} (ev : env_t V) (k k' : K) (v : V k),
    k ≠ k' → getenv (putenv ev k v) k' = getenv ev k'

namespace Env

variable {K : Type} [E : Env K]

/-- Equivalence of environments (pointwise equality) -/
def equiv {V : ESig K} (ev1 ev2 : E.env_t V) : Prop :=
  ∀ k : K, E.getenv ev1 k = E.getenv ev2 k

/-- Update environment by applying function to current value -/
def update {V : ESig K} (ev : E.env_t V) (k : K) (fn : V k → V k) : E.env_t V :=
  E.putenv ev k (fn (E.getenv ev k))

/-- Map over environment values -/
def map {V1 V2 : ESig K} (fn : ∀ k, V1 k → V2 k) (ev1 : E.env_t V1) : E.env_t V2 :=
  E.create (fun k => fn k (E.getenv ev1 k))

/-- Zip two environments -/
def zip {V1 V2 : ESig K} (ev1 : E.env_t V1) (ev2 : E.env_t V2) :
    E.env_t (fun k => V1 k × V2 k) :=
  E.create (fun k => (E.getenv ev1 k, E.getenv ev2 k))

/-- Unzip a paired environment -/
def unzip {V1 V2 : ESig K} (ev : E.env_t (fun k => V1 k × V2 k)) :
    E.env_t V1 × E.env_t V2 :=
  (E.create (fun k => (E.getenv ev k).1),
   E.create (fun k => (E.getenv ev k).2))

/-- Map binary function over two environments -/
def map2 {V1 V2 V3 : ESig K} (fn : ∀ k, V1 k → V2 k → V3 k)
    (ev1 : E.env_t V1) (ev2 : E.env_t V2) : E.env_t V3 :=
  E.create (fun k => fn k (E.getenv ev1 k) (E.getenv ev2 k))

/-- Fold over all keys in environment -/
def fold_right {V : ESig K} {T : Type} (f : ∀ k : K, V k → T → T)
    (ev : E.env_t V) (t0 : T) : T :=
  List.foldr (fun k t => f k (E.getenv ev k) t) t0 E.finite_keys.finite_elements

/-- Convert environment to dependent list -/
def to_list {V : ESig K} (ev : E.env_t V) : List (Σ k : K, V k) :=
  fold_right (fun k v t => (⟨k, v⟩ : Σ k : K, V k) :: t) ev []

/-- Convert environment with uniform values to association list -/
def to_alist {V : Type} (ev : E.env_t (fun _ => V)) : List (K × V) :=
  fold_right (fun k v t => (k, v) :: t) ev []

end Env

/-! ## Context-based Env implementation -/

/-- Helper to construct member from index and proof that element is at that index -/
def envMemberFromIndex {K : Type} (k : K) : (l : List K) → (idx : Nat) →
    (h : l[idx]? = some k) → EnvMember k l
  | [], _, h => by simp at h
  | k' :: l', 0, h => by
      simp at h
      exact h ▸ EnvMember.hd k' l'
  | k' :: l', idx + 1, h => by
      have h' : l'[idx]? = some k := by simp at h; exact h
      exact EnvMember.tl k k' l' (envMemberFromIndex k l' idx h')

/-- Index of envMemberFromIndex equals the original index -/
theorem envMemberFromIndex_idx {K : Type} (k : K) (l : List K) (idx : Nat)
    (h : l[idx]? = some k) : (envMemberFromIndex k l idx h).idx = idx := by
  induction l generalizing idx with
  | nil => simp at h
  | cons k' l' ih =>
    cases idx with
    | zero =>
      simp only [envMemberFromIndex]
      simp only [List.getElem?_cons_zero] at h
      -- h : some k' = some k, so k' = k
      cases h
      rfl
    | succ idx' =>
      simp only [envMemberFromIndex, EnvMember.idx]
      have h' : l'[idx']? = some k := by simp at h; exact h
      rw [ih idx' h']

/-- Helper to construct member from index in finite list -/
def finiteEnvMember {T : Type} [FT : FiniteType T] (t : T) :
    EnvMember t FT.finite_elements :=
  envMemberFromIndex t FT.finite_elements (FT.finite_index t) (FT.finite_surjective t)

/-- Index of finiteEnvMember equals finite_index -/
theorem finiteEnvMember_idx {T : Type} [FT : FiniteType T] (t : T) :
    (finiteEnvMember t).idx = FT.finite_index t :=
  envMemberFromIndex_idx t FT.finite_elements (FT.finite_index t) (FT.finite_surjective t)

/-- Different elements have different finiteEnvMember indices -/
@[grind] theorem finiteEnvMember_idx_ne {T : Type} [FT : FiniteType T] (t1 t2 : T) :
    t1 ≠ t2 → (finiteEnvMember t1).idx ≠ (finiteEnvMember t2).idx := by
  intro hne
  simp only [finiteEnvMember_idx]
  intro heq
  apply hne
  exact finite_index_injective t1 t2 heq

/-- Context.create with equal functions produces equal contexts -/
theorem Context.create_funext' {K : Type} {V : K → Type} {sig : List K}
    (f1 f2 : ∀ k, EnvMember k sig → V k) (h : ∀ k m, f1 k m = f2 k m) :
    Context.create sig f1 = Context.create sig f2 := by
  induction sig with
  | nil => rfl
  | cons k sig' ih =>
    simp only [Context.create]
    have h1 := h k (EnvMember.hd k sig')
    have h2 := ih (fun k' m' => f1 k' (EnvMember.tl k' k sig' m'))
                  (fun k' m' => f2 k' (EnvMember.tl k' k sig' m'))
                  (fun k' m' => h k' (EnvMember.tl k' k sig' m'))
    simp only [h1, h2]

/-- Creating a context from assoc lookups of an existing context gives back the same context -/
theorem Context.create_assoc_id {K : Type} {V : K → Type} {sig : List K}
    (ctx : Context (V := V) sig) :
    Context.create sig (fun _k m => Context.assoc m ctx) = ctx := by
  induction ctx with
  | empty => rfl
  | @cons k sig' v ctx' ih =>
    simp only [Context.create, Context.assoc, Context.hd, Context.tl]
    rw [ih]

/-- Two membership witnesses with the same index give the same assoc result -/
theorem Context.assoc_eq_of_idx_eq {K : Type} {V : K → Type} {sig : List K}
    {k : K} (m1 m2 : EnvMember k sig) (ctx : Context (V := V) sig)
    (heq : m1.idx = m2.idx) : Context.assoc m1 ctx = Context.assoc m2 ctx := by
  induction m1 with
  | hd sig' =>
    cases m2 with
    | hd => rfl
    | tl _ _ m2' =>
      simp only [EnvMember.idx] at heq
      omega
  | tl k' sig' m1' ih =>
    cases m2 with
    | hd =>
      simp only [EnvMember.idx] at heq
      omega
    | tl _ _ m2' =>
      simp only [EnvMember.idx] at heq
      cases ctx with
      | cons _ _ ctx' =>
        simp only [Context.assoc, Context.tl]
        apply ih m2' ctx'
        omega

/-- EnvMember at position i implies the list has k at that position -/
theorem EnvMember.list_getElem {K : Type} {sig : List K} {k : K}
    (m : EnvMember k sig) : sig[m.idx]? = some k := by
  induction m with
  | hd => rfl
  | tl _ _ m' ih => exact ih

/-- Nodup list: equal elements at different indices means equal indices -/
theorem nodup_getElem_eq_imp_idx_eq {α : Type} (l : List α) (hnodup : l.Nodup)
    (i j : Nat) (hi : i < l.length) (hj : j < l.length)
    (heq : l[i] = l[j]) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a as ih =>
    rw [List.nodup_cons] at hnodup
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        simp only [List.length_cons] at hj
        have hjlt : j' < as.length := by omega
        have : a ∈ as := heq ▸ List.getElem_mem hjlt
        exact absurd this hnodup.1
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        simp only [List.length_cons] at hi
        have hilt : i' < as.length := by omega
        have : a ∈ as := heq.symm ▸ List.getElem_mem hilt
        exact absurd this hnodup.1
      | succ j' =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi hj
        simp only [List.getElem_cons_succ] at heq
        have := ih hnodup.2 i' j' hi hj heq
        omega

/-- Lookup in created context equals the function value -/
@[grind] theorem assoc_create' {K : Type} {V : K → Type} {sig : List K}
    (f : ∀ k, EnvMember k sig → V k) {k : K} (m : EnvMember k sig) :
    Context.assoc m (Context.create sig f) = f k m := by
  induction m
  case hd => rfl
  case tl k' sig' m' ih =>
    simp only [Context.create, Context.assoc, Context.tl]
    exact ih _

/-- Replace then lookup at same position returns new value -/
@[grind] theorem assoc_replace_eq' {K : Type} {V : K → Type} {sig : List K}
    (ctx : Context (V := V) sig) {k : K} (m : EnvMember k sig) (v : V k) :
    Context.assoc m (Context.replace m v ctx) = v := by
  induction m
  case hd =>
    cases ctx with
    | cons _ _ _ => rfl
  case tl k' sig' m' ih =>
    cases ctx with
    | cons _ _ ctx' =>
      simp only [Context.replace, Context.assoc, Context.tl]
      exact ih ctx'

/-- Replace then lookup at different position returns old value -/
@[grind] theorem assoc_replace_neq' {K : Type} {V : K → Type} {sig : List K}
    (ctx : Context (V := V) sig) {k k' : K}
    (m : EnvMember k sig) (m' : EnvMember k' sig) (v : V k) :
    m.idx ≠ m'.idx →
    Context.assoc m' (Context.replace m v ctx) = Context.assoc m' ctx := by
  intro hneq
  induction m generalizing k'
  case hd sig' =>
    cases m' with
    | hd => simp only [EnvMember.idx] at hneq; omega
    | tl _ _ m'' =>
      cases ctx with
      | cons _ _ ctx' =>
        simp only [Context.replace, Context.assoc, Context.tl]
  case tl k'' sig'' m'' ih =>
    cases m' with
    | hd =>
      cases ctx with
      | cons _ _ ctx' =>
        simp only [Context.replace, Context.assoc, Context.hd]
    | tl _ _ m''' =>
      cases ctx with
      | cons _ v' ctx' =>
        simp only [Context.replace, Context.assoc, Context.tl]
        apply ih
        simp only [EnvMember.idx] at hneq ⊢
        omega

/-- Context-based implementation of Env -/
def contextEnv {K : Type} [FT : FiniteType K] [DecidableEq K] : Env K where
  env_t V := Context (V := V) FT.finite_elements
  getenv ctx k := Context.assoc (finiteEnvMember k) ctx
  putenv ctx k v := Context.replace (finiteEnvMember k) v ctx
  create fn := Context.create FT.finite_elements (fun k _ => fn k)
  finite_keys := FT
  create_getenv_id := by
    intro V ev
    -- Use funext with the identity lemma
    have h := Context.create_assoc_id ev
    apply Eq.trans _ h
    apply Context.create_funext'
    intro k m
    -- Need: Context.assoc (finiteEnvMember k) ev = Context.assoc m ev
    -- By assoc_eq_of_idx_eq, this follows if (finiteEnvMember k).idx = m.idx
    apply Context.assoc_eq_of_idx_eq
    -- finiteEnvMember k has idx = FT.finite_index k
    rw [finiteEnvMember_idx]
    -- Need: FT.finite_index k = m.idx
    -- We have: FT.finite_elements[FT.finite_index k]? = some k (surjective)
    --          FT.finite_elements[m.idx]? = some k (from EnvMember)
    have hsurj := FT.finite_surjective k
    have hm := EnvMember.list_getElem m
    have hlt1 : FT.finite_index k < FT.finite_elements.length := finite_index_lt k
    have hlt2 : m.idx < FT.finite_elements.length := by
      simp only [List.getElem?_eq_some_iff] at hm
      exact hm.1
    simp only [List.getElem?_eq_some_iff] at hsurj hm
    have heq_val : FT.finite_elements[FT.finite_index k] = FT.finite_elements[m.idx] := by
      rw [hsurj.2, hm.2]
    -- By Nodup and equal elements, indices must be equal
    have hnodup := finite_nodup (T := K)
    exact nodup_getElem_eq_imp_idx_eq FT.finite_elements hnodup _ _ hlt1 hlt2 heq_val
  create_funext := by
    intro V fn1 fn2 h
    apply Context.create_funext'
    intro k m
    exact h k
  getenv_create := by
    intro V fn k
    -- Need Context.assoc (finiteEnvMember k) (Context.create ...) = fn k
    exact assoc_create' _ _
  get_put_eq := by
    intro V ev k v
    exact assoc_replace_eq' ev (finiteEnvMember k) v
  get_put_neq := by
    intro V ev k k' v hne
    exact assoc_replace_neq' ev (finiteEnvMember k) (finiteEnvMember k') v
           (finiteEnvMember_idx_ne k k' hne)

/-! ## Lemmas -/

section Lemmas

variable {K : Type}
variable {V : K → Type}

/-- Lookup in created context equals the function value -/
@[grind] theorem assoc_create {sig : List K} (f : ∀ k, EnvMember k sig → V k) {k : K}
    (m : EnvMember k sig) :
    Context.assoc m (Context.create sig f) = f k m := by
  induction m
  case hd => rfl
  case tl k' sig' m' ih =>
    simp only [Context.create, Context.assoc, Context.tl]
    exact ih _

/-- Replace then lookup at same position returns new value -/
@[grind] theorem assoc_replace_eq {sig : List K} (ctx : Context sig) {k : K}
    (m : EnvMember k sig) (v : V k) :
    Context.assoc m (Context.replace m v ctx) = v := by
  induction m
  case hd =>
    cases ctx with
    | cons _ _ _ => rfl
  case tl k' sig' m' ih =>
    cases ctx with
    | cons _ _ ctx' =>
      simp only [Context.replace, Context.assoc, Context.tl]
      exact ih ctx'

/-- Replace then lookup at different position returns old value -/
@[grind] theorem assoc_replace_neq {sig : List K} (ctx : Context sig) {k k' : K}
    (m : EnvMember k sig) (m' : EnvMember k' sig) (v : V k) :
    m.idx ≠ m'.idx →
    Context.assoc m' (Context.replace m v ctx) = Context.assoc m' ctx := by
  intro hneq
  induction m generalizing k'
  case hd sig' =>
    cases m' with
    | hd => simp only [EnvMember.idx] at hneq; omega
    | tl _ _ m'' =>
      cases ctx with
      | cons _ _ ctx' =>
        simp only [Context.replace, Context.assoc, Context.tl]
  case tl k'' sig'' m'' ih =>
    cases m' with
    | hd =>
      cases ctx with
      | cons _ _ ctx' =>
        simp only [Context.replace, Context.assoc, Context.hd]
    | tl _ _ m''' =>
      cases ctx with
      | cons _ v' ctx' =>
        simp only [Context.replace, Context.assoc, Context.tl]
        apply ih
        simp only [EnvMember.idx] at hneq ⊢
        omega

/-- Map commutes with assoc -/
@[grind] theorem map_assoc {K K' : Type} {V : K → Type} {V' : K' → Type}
    (fK : K → K') (fV : ∀ k, V k → V' (fK k))
    {sig : List K} (ctx : Context sig) {k : K} (m : EnvMember k sig) :
    Context.assoc (m.map fK) (Context.map fK fV ctx) = fV k (Context.assoc m ctx) := by
  induction m
  case hd sig' =>
    cases ctx with
    | cons _ v _ => rfl
  case tl k' sig' m' ih =>
    cases ctx with
    | cons _ _ ctx' =>
      simp only [EnvMember.map, Context.map, Context.assoc, Context.tl]
      exact ih ctx'

/-- getenv after map equals mapped value -/
@[grind] theorem getenv_map {K : Type} [E : Env K] {V1 V2 : ESig K}
    (fn : ∀ k, V1 k → V2 k) (ev : E.env_t V1) (k : K) :
    E.getenv (Env.map fn ev) k = fn k (E.getenv ev k) := by
  simp only [Env.map, E.getenv_create]

/-- getenv after zip gives pair -/
@[grind] theorem getenv_zip {K : Type} [E : Env K] {V1 V2 : ESig K}
    (ev1 : E.env_t V1) (ev2 : E.env_t V2) (k : K) :
    E.getenv (Env.zip ev1 ev2) k = (E.getenv ev1 k, E.getenv ev2 k) := by
  simp only [Env.zip, E.getenv_create]

/-- getenv after map2 gives binary application -/
@[grind] theorem getenv_map2 {K : Type} [E : Env K] {V1 V2 V3 : ESig K}
    (fn : ∀ k, V1 k → V2 k → V3 k) (ev1 : E.env_t V1) (ev2 : E.env_t V2) (k : K) :
    E.getenv (Env.map2 fn ev1 ev2) k = fn k (E.getenv ev1 k) (E.getenv ev2 k) := by
  simp only [Env.map2, E.getenv_create]

/-- equiv is reflexive -/
theorem equiv_refl {K : Type} [E : Env K] {V : ESig K} (ev : E.env_t V) :
    Env.equiv ev ev := by
  intro k
  rfl

/-- Equivalent environments are equal -/
theorem equiv_eq {K : Type} [E : Env K] {V : ESig K} (ev1 ev2 : E.env_t V) :
    Env.equiv ev1 ev2 → ev1 = ev2 := by
  intro h
  have h1 : E.create (E.getenv ev1) = ev1 := E.create_getenv_id ev1
  have h2 : E.create (E.getenv ev2) = ev2 := E.create_getenv_id ev2
  rw [←h1, ←h2]
  apply E.create_funext
  exact h

end Lemmas

end Koika
