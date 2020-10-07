(*! Tools | Functions defined on typed ASTs !*)
Require Export Koika.Member Koika.TypedSyntax Koika.TypedSyntax.
Require Import Koika.Primitives Koika.TypedSemantics.
Import PrimTyped.

Require Import Magic.

Section TypedSyntaxMacros.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Notation action := (action pos_t var_t fn_name_t).
  Notation InternalFunction R Sigma sig tau := (InternalFunction pos_t var_t fn_name_t R Sigma sig tau).

  Section Simple.
    Notation action := (action R Sigma).

    Definition struct_sig_of_action {sig tau} (a: action sig tau)
      : option struct_sig :=
      match tau with
      | struct_t sig => Some sig
      | _ => None
      end.

    Definition init sig (tau: type) : action sig tau :=
      let zeroes := Const (tau := bits_t _) (Bits.zeroes (type_sz tau)) in
      Unop (Conv tau Unpack) zeroes.

    Fixpoint struct_init
             {sig}
             (ssig: struct_sig)
             (initializers: context (fun k_tau => action sig (snd k_tau))
                                    ssig.(struct_fields))
      : action sig (struct_t ssig) :=
      let empty := init sig (struct_t ssig) in
      let mk_subst f := Binop (Struct2 SubstField ssig f) in
      cfoldli (V := fun k_tau => action sig (snd k_tau))
              (fun k_tau m a (acc: action sig (struct_t ssig)) =>
                 (mk_subst (existT _ k_tau m)) acc a)
              initializers empty.

    Fixpoint switch {vk vtau} {sig tau} (m: member (vk, vtau) sig)
             (default: action sig tau)
             (branches: list (action sig vtau * action sig tau)) : action sig tau :=
      match branches with
      | nil => default
      | (label, action) :: branches =>
        If (Binop (Eq _ false) (Var m) label)
           action (switch m default branches)
      end.

    Definition switch_pure {vk vtau} {sig tau} (m: member (vk, vtau) sig)
               (default: action sig tau)
               (branches: list (vtau * action sig tau)) : action sig tau :=
      switch m default (List.map (fun p => (Const (tau := vtau) (fst p), snd p)) branches).
  End Simple.

  Section Lift.
    Context {reg_t' ext_fn_t': Type}.

    Context {R': reg_t' -> type}.
    Context {Sigma': ext_fn_t' -> ExternalSignature}.

    (* FIXME not called a lift *)

    Class Intfun_lift_OK {A A' B} (fA: A -> B) (fA': A' -> B) (l: A' -> A) :=
      { lift_comm: fA' = (fun a => fA (l a));
        lift_inj: forall a'0 a'1, l a'0 = l a'1 -> a'0 = a'1 }.

    Class Intfun_lift {A A' B} (fA: A -> B) (fA': A' -> B) :=
      { lift_fn: A' -> A;
        lift_ok: Intfun_lift_OK fA fA' lift_fn }.

    Global Arguments lift_comm {A A' B} {fA fA' l} ok : rename.
    Global Arguments lift_inj {A A' B} {fA fA' l} ok : rename.

    Global Arguments lift_fn {A A' B} {fA fA'} l : rename.
    Global Arguments lift_ok {A A' B} {fA fA'} l : rename.

    Context (lR: Intfun_lift R R')
            (lSigma: Intfun_lift Sigma Sigma').

    Section lift_intfun.
      Context {tau: type}.
      Context {argspec : tsig var_t}.
      Context (lift: forall (a: action R' Sigma' (List.rev argspec) tau),
                  action R Sigma (List.rev argspec) tau).

      Definition lift_intfun'
                 (fn : InternalFunction R' Sigma' (List.rev argspec) tau) :
        InternalFunction R Sigma (List.rev argspec) tau :=
        {| int_name := fn.(int_name);
           int_body := lift fn.(int_body) |}.
    End lift_intfun.

    Fixpoint lift
             {sig tau}
             (a: action R' Sigma' sig tau)
      : action R Sigma sig tau :=
      match a with
      | Fail tau => Fail tau
      | Var vr => Var vr
      | Const cst => Const cst
      | Assign vr ex => Assign vr (lift ex)
      | Seq a1 a2 => Seq (lift a1) (lift a2)
      | Bind var ex body => Bind var (lift ex) (lift body)
      | If cond tbranch fbranch => If (lift cond) (lift tbranch) (lift fbranch)
      | Read port idx =>
        rew <- [fun R' => action R Sigma _ (R' idx)] lR.(lift_ok).(lift_comm) in
            (Read port (lift_fn lR idx))
      | Write port idx value =>
        Write port (lR.(lift_fn) idx)
              (rew [fun R' => action R Sigma _ (R' idx)] lR.(lift_ok).(lift_comm) in
                  (lift value))
      | Unop fn arg1 => Unop fn (lift arg1)
      | Binop fn arg1 arg2 => Binop fn (lift arg1) (lift arg2)
      | ExternalCall fn arg =>
        rew <- [fun Sigma' => action R Sigma _ (retSig (Sigma' fn))] lSigma.(lift_ok).(lift_comm) in
            (ExternalCall
               (lSigma.(lift_fn) fn)
               (rew [fun Sigma' => action R Sigma _ (arg1Sig (Sigma' fn))]
                        lSigma.(lift_ok).(lift_comm) in
                   (lift arg)))
      | InternalCall fn args =>
        InternalCall (lift_intfun' lift fn) (cmapv (fun _ => lift) args)
      | APos pos a => APos pos (lift a)
      end.

    Context {REnv: Env reg_t}.
    Context {REnv': Env reg_t'}.

    Definition unlift_REnv
               (f: type -> Type)
               (env: REnv.(env_t) (fun x => f (R x)))
    : REnv'.(env_t) (fun x => f (R' x)) :=
      rew <- [fun R' => REnv'.(env_t) (fun r => f (R' r))] lR.(lift_ok).(lift_comm) in
        REnv'.(create) (fun reg: reg_t' => REnv.(getenv) env (lR.(lift_fn) reg)).

    Definition unlift_sigma
               (sigma: forall f, Sig_denote (Sigma f))
      : forall f, Sig_denote (Sigma' f) :=
      rew <- [fun Sigma' => forall f, Sig_denote (Sigma' f)] lSigma.(lift_ok).(lift_comm) in
        (fun f => sigma (lSigma.(lift_fn) f)).

    Definition lift_REnv
               (f: type -> Type)
               (env: REnv.(env_t) (fun x => f (R x)))
               (env': REnv'.(env_t) (fun x => f (R' x)))
      : REnv.(env_t) (fun x => f (R x)) :=
      Environments.fold_right
        REnv'
        (fun k v acc =>
           (REnv.(putenv))
             acc (lR.(lift_fn) k)
             (rew [fun R' => f (R' k)] lR.(lift_ok).(lift_comm) in v))
        env' env.

    Context (r: REnv.(env_t) R).
    Context (sigma: forall f, Sig_denote (Sigma f)).

    Lemma lift_unlift_REnv (f: type -> Type):
      forall l, lift_REnv f l (unlift_REnv f l) = l.
    Proof.
      unfold lift_REnv, unlift_REnv, Environments.fold_right.
      induction finite_elements; cbn.
      - reflexivity.
      - intros.
        rewrite IHl. apply put_get_eq.
        unfold eq_rect_r.
        rewrite getenv_rew'.
        rewrite getenv_create.
        rewrite rew_compose.
        apply __magic__.
    Qed.

    Lemma unlift_lift_REnv (f: type -> Type):
      forall ev ev0, unlift_REnv f (lift_REnv f ev0 ev) = ev.
    Proof.
      unfold lift_REnv, unlift_REnv, Environments.fold_right.
      intros.
      apply equiv_eq; intros k.
      unfold eq_rect_r; rewrite getenv_rew', getenv_create.
      (* LR k is in the list, so must be hit, and by injectivity it's not replaced *)
        apply __magic__.
    Qed.

    Lemma getenv_unlift_REnv (f: type -> Type) :
      forall ev k,
        REnv'.(getenv) (unlift_REnv f ev) k =
        rew <- [fun R' => f (R' k)] lR.(lift_ok).(lift_comm) in
          REnv.(getenv) ev (lift_fn lR k).
    Proof.
      unfold unlift_REnv; intros.
      unfold eq_rect_r.
      rewrite getenv_rew'.
      rewrite getenv_create; reflexivity.
    Qed.

    Lemma getenv_lift_REnv_lifted (f: type -> Type) :
      forall ev ev0 k',
        REnv.(getenv) (lift_REnv f ev0 ev) (lift_fn lR k') =
        rew [fun R' => f (R' k')] lR.(lift_ok).(lift_comm) in
          REnv'.(getenv) ev k'.
    Proof.
      apply __magic__.
    Qed.

    Lemma getenv_lift_REnv_unlifted (f: type -> Type) :
      forall ev ev0 k,
        (forall k', lift_fn lR k' <> k) ->
        REnv.(getenv) (lift_REnv f ev0 ev) k =
        REnv.(getenv) ev0 k.
    Proof.
      apply __magic__.
    Qed.
  End Lift.
End TypedSyntaxMacros.

Notation lift_intfun lR lSigma fn :=
  (lift_intfun' (lift lR lSigma) fn).

Require Import CompactLogs.

Arguments unlift_sigma {ext_fn_t} {Sigma} {ext_fn_t'} {Sigma'} {lSigma} sigma f _: assert.

Notation unlift_Log := (unlift_REnv _ LogEntry).
Notation unlift_r := (unlift_REnv _ type_denote).

Notation lift_Log := (lift_REnv _ LogEntry).
Notation lift_r := (lift_REnv _ type_denote).
