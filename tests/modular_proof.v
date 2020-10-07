(*! Simple modular proof !*)
Require Import Koika.TypedSyntaxMacros.
Require Import Koika.Frontend.
Import Koika.CompactLogs Koika.CompactSemantics.

Notation action := (action pos_t var_t fn_name_t).
Notation rule := (rule pos_t var_t fn_name_t).
Notation scheduler := (scheduler pos_t _).
Notation InternalFunction R Sigma sig tau :=
  (InternalFunction pos_t var_t fn_name_t R Sigma sig tau).

Module Rf.
  Section Rf.
    Context {data_t: type} {sz: nat}.
    Context {init: data_t}.

    Inductive reg_t := rData (n: Vect.index sz).

    Definition R (idx: reg_t) :=
      data_t.

    Definition r (idx: reg_t) : R idx :=
      init.

    Definition read : InternalFunction R empty_Sigma _ _ :=
      <{ fun read (idx : bits_t (log2 sz)) : data_t =>
           ` (switch_pure
               (_: VarRef _ "idx" _)
               (<{ fail }>)
               (List.map
                  (fun idx: Vect.index sz =>
                     (Bits.of_index _ idx: bits_t _,
                      <{ read0(rData idx) }>: action R empty_Sigma _ data_t))
                  (vect_to_list (all_indices sz)))) ` }>.

    Definition write : InternalFunction R empty_Sigma _ _ :=
      <{ fun write (idx : bits_t (log2 sz)) (val: data_t) : unit_t =>
           ` (switch_pure
               (_: VarRef _ "idx" _)
               (<{ fail }>)
               (List.map
                  (fun idx: Vect.index sz =>
                     (Bits.of_index _ idx: bits_t _,
                      <{ write0(rData idx, val) }>))
                  (vect_to_list (all_indices sz)))) ` }>.

    Lemma switch_pure_eqn REnv r sigma:
      forall {vk vtau} {sig tau}
        (m: member (vk, vtau) sig)
        (default: action R empty_Sigma sig tau)
        (branches: list (vtau * action R empty_Sigma sig tau))
        Gamma (L l: Log R REnv),
        let idx := cassoc m Gamma in
        interp_action
          r sigma Gamma L l
          (switch_pure m default branches) =
        match (List.find (fun p => beq_dec idx (fst p)) branches) with
        | Some (_, a) => interp_action r sigma Gamma L l a
        | None => interp_action r sigma Gamma L l default
        end.
    Proof.
      induction branches as [ | (cst & a) branches IH]; cbn; intros.
      - reflexivity.
      - destruct (beq_dec _ _); simpl.
        + reflexivity.
        + rewrite IH; reflexivity.
    Qed.

    Lemma find_map {A B} (p: B -> bool) (f: A -> B):
      forall l, List.find p (List.map f l) =
           option_map f (List.find (fun a => p (f a)) l).
    Proof.
      unfold option_map; induction l as [ | a l IH]; cbn.
      - reflexivity.
      - destruct (p (f a)); try rewrite IH; reflexivity.
    Qed.

    Section read_eqn.
      Context (REnv : Env reg_t).
      Context (r : env_t REnv (fun x : reg_t => R x)).
      Context (sigma : forall f : empty_ext_fn_t, Sig_denote (empty_Sigma f)).

      Context (Gamma: tcontext (rev [("idx", bits_t (log2 sz))])).
      Context (L: Log R REnv).
      Context (l: Log R REnv).
      Context (idx: Vect.index sz).

      Context (Hidx: cassoc (MemberHd _ _) Gamma = Bits.of_index (log2 sz) idx).
      Context (Hr0: may_read0 L (rData idx) = true).

      Lemma read_eqn:
        interp_action r sigma Gamma L l (read.(int_body)) =
        Some
            (putenv REnv l (rData idx)
                    {|
                      lread0 := true;
                      lread1 := lread1 (getenv REnv l (rData idx));
                      lwrite0 := lwrite0 (getenv REnv l (rData idx));
                      lwrite1 := lwrite1 (getenv REnv l (rData idx)) |}, getenv REnv r (rData idx),
             #{ ("idx", bits_t (log2 sz)) => Bits.of_index (log2 sz) idx }#).
      Proof.
        destruct (cdestruct Gamma) as [(idx_bits & empty) ->]; simpl in *; subst;
          rewrite (cdestruct empty); clear empty.
        rewrite switch_pure_eqn; simpl.
        rewrite <- vect_to_list_map.
        rewrite <- vect_to_list_find.
        rewrite vect_find_map.
        rewrite vect_find_inj, vect_mem_find.
        - rewrite (proj1 (reflect_iff _ _ (vect_mem_In _ _))).
          + simpl; rewrite Hr0; reflexivity.
          + eauto using vect_nth_In, all_indices_eqn.
        - intros; eapply Bits.of_index_inj; eauto using le_pow2_log2.
      Qed.

      Lemma read_eqn_cps {A} k:
        interp_action_cps r sigma L (read.(int_body)) A k Gamma l =
        k (Some
             (putenv REnv l (rData idx)
                     {|
                       lread0 := true;
                       lread1 := lread1 (getenv REnv l (rData idx));
                       lwrite0 := lwrite0 (getenv REnv l (rData idx));
                       lwrite1 := lwrite1 (getenv REnv l (rData idx)) |}, getenv REnv r (rData idx),
              #{ ("idx", bits_t (log2 sz)) => Bits.of_index (log2 sz) idx }#)).
      Proof.
        rewrite interp_action_cps_correct. f_equal; apply read_eqn.
      Qed.
    End read_eqn.
  End Rf.
End Rf.

Definition sz := 64.
Definition data_t := bits_t 32.

Inductive reg_t :=
| in_buf
| out_buf
| rf (r: Rf.reg_t (sz := sz)).

Instance FiniteType_rf : FiniteType (Rf.reg_t (sz := sz)) := _.
Instance FiniteType_reg_t : FiniteType reg_t := _.

Definition R reg : type :=
  match reg with
  | in_buf => bits_t (log2 sz)
  | out_buf => data_t
  | rf r => Rf.R (data_t := data_t) r
  end.

Inductive rule_name_t := rl0.

Program Instance Intfun_lift_refl
        (ext_fn_t: Type) {Sigma: ext_fn_t -> ExternalSignature}
  : Intfun_lift Sigma Sigma :=
  {| lift_fn f := f;
     lift_ok := {| lift_comm := eq_refl;
                  lift_inj := _ |} |}.

Program Instance Intfun_lift_OK_rf
  : Intfun_lift_OK R (Rf.R (data_t := data_t)) rf.

Program Definition rules rl : rule R empty_Sigma :=
  match rl with
  | rl0 => <{ write0(out_buf, rf.(Rf.read)(read0(in_buf))) }>
  end.

Definition sched : scheduler :=
  rl0 |> done.

Require Import Koika.CPS.

Section Proofs.
  (* Notation "'WP' 'context:' Gamma 'L:' L 'l:' l a 'then:' res '⇒' k" := *)
  (*   (block (@interp_action_cps _ _ _ _ _ _ _ _ _ _) _ _ L a Prop (fun res => k) Gamma l) *)
  (*     (at level 0, *)
  (*      no associativity, *)
  (*      a at level 0, *)
  (*      format "'[v  ' 'WP' '//' '[hv  ' 'context:'  Gamma ']' '//' '[hv  ' 'L:'  L ']' '//' '[hv  ' 'l:'  l ']' '//' a ']' '//' '[hv  ' 'then:'  res  ⇒  k ']'"). *)

  Notation "'WP' 'context:' Gamma 'L:' L 'l:' l a 'then:' '…'" :=
    (block (@interp_action_cps _ _ _ _ _ _ _ _ _ _) _ _ L a Prop _ Gamma l)
      (at level 0,
       no associativity,
       a at level 0,
       format "'[v  ' 'WP' '//' '[hv  ' 'context:'  Gamma ']' '//' '[hv  ' 'L:'  L ']' '//' '[hv  ' 'l:'  l ']' '//' a ']' '//' '[hv  ' 'then:'  '…' ']'").

  Arguments ContextEnv : simpl never.

  Lemma apply_eq {a a': Prop} (pr: a = a'): a -> a'.
  Proof.
    rewrite pr; intros; assumption.
  Qed.

  (* Notation blocked_interp sig tau L a Gamma l := *)
  (*   (block (@interp_action_cps _ _ _ _ _ _ _ _ _ _) sig tau L a Prop _ Gamma l). *)
  Arguments block : simpl never.

  Ltac prepare_interp :=
    change (@interp_action_cps ?pos_t ?var_t ?fn_name_t ?reg_t ?ext_fn_t ?R ?Sigma ?Env ?r ?sigma)
    with (block (@interp_action_cps pos_t var_t fn_name_t reg_t ext_fn_t R Sigma Env r sigma)).

  Ltac interp_init r :=
    apply (wp_cycle_correct r);
    unfold wp_cycle, interp_cycle_cps, interp_scheduler_cps;
    cbn -[interp_action_cps];
    unfold interp_rule_cps;
    prepare_interp.

  Ltac interp_simpl :=
    unfold block at 1; simpl.
  Ltac interp_rewrite :=
    unfold block at 1;
    rewrite <- interp_action_cps_eqn;
    unfold interp_action_cps1.
  Ltac interp_apply :=
    unfold block at 1;
    simple apply (apply_eq (interp_action_cps_eqn _ _ _ _ _ _ _ _ _ _));
    unfold interp_action_cps1.

  Import CompactLogs.
  Arguments Bits.to_index : simpl never.

  Definition blocked_let
             {A} {K: A -> Type} (a: A)
             (k: forall a, K a) : K a :=
    let aa := a in k aa.
  Arguments blocked_let: simpl never.

  Notation "'let/b' x .. y := v 'in' f" :=
    (blocked_let v (fun x => .. (fun y => f) .. ))
      (at level 200, x binder, y binder, f at level 200,
       format "'let/b'  x .. y  :=  v  'in' '//' f").

  Goal forall (r: ContextEnv.(env_t) R),
      match CompactSemantics.interp_action
              (R := R) r empty_sigma CtxEmpty
              log_empty log_empty
              (rules rl0) with
      | Some (l, _, _) =>
        l.[in_buf].(lwrite0) = None /\
        l.[in_buf].(lwrite1) = None /\
        exists v,
          l.[out_buf].(lwrite0) = Some v /\
          l.[out_buf].(lwrite1) = None
      | None => True
      end.
  Proof.
    intros.
    apply wp_action_correct.
    unfold wp_action.
    prepare_interp.

    unfold rules.
    repeat interp_apply.
    unfold interp_args'_cps.
    unfold eq_rect, rules_obligation_1.
    repeat interp_apply.

    simpl may_read0; cbv iota.

    unfold int_body, lift_intfun.
    unfold block.
    rewrite (lift_interp_cps (rule_name_t := rule_name_t) (REnv' := ContextEnv));
      prepare_interp.
    unfold unlift_REnv.

    unfold block.
    change (interp_action_cps ?r ?sigma ?Log ?a Prop ?post)
      with (wp_action r sigma Log a post).
    apply wp_action_abstract; intros [((l, v), Gamma) | ].
    - unfold may_write0, update.
      rewrite !get_put_eq.
      rewrite !get_put_neq by congruence.
      rewrite !(getenv_lift_REnv_unlifted _ LogEntry) by (intros ? ?; discriminate).
      unfold log_empty; rewrite !getenv_create.
      rewrite !get_put_eq.
      rewrite !get_put_neq by congruence.
      rewrite !getenv_create.
      simpl; eauto.
    - eauto.
  Qed.


  Goal forall (r: ContextEnv.(env_t) R),
      exists l,
        CompactSemantics.interp_action
          (R := R) r empty_sigma CtxEmpty
          log_empty log_empty
          (rules rl0) = Some (l, Ob, CtxEmpty) /\
        l.[in_buf] = {| lread0 := true; lread1 := false;
                        lwrite0 := None; lwrite1 := None |} /\
        l.[out_buf] = {| lread0 := false; lread1 := false;
                         lwrite0 := Some r.[rf (Rf.rData (Bits.to_index_safe r.[in_buf]))];
                         lwrite1 := None |}.
  Proof.
    intros.
    apply wp_action_correct.
    unfold wp_action.
    prepare_interp.

    unfold rules.
    repeat interp_apply.
    unfold interp_args'_cps.
    unfold eq_rect, rules_obligation_1.
    repeat interp_apply.

    change (may_read0 _ _) with true; cbv iota.

    unfold int_body, lift_intfun, block;
      rewrite (lift_interp_cps (rule_name_t := rule_name_t) (REnv' := ContextEnv)).

    rewrite Rf.read_eqn_cps with (idx := Bits.to_index_safe r.[in_buf]).

    change (may_write0 _ _ _) with true; cbv iota.
    - eexists; split; [ reflexivity | ].

      unfold update.
      rewrite !get_put_eq.
      rewrite !get_put_neq by congruence.
      rewrite !(getenv_lift_REnv_unlifted _ LogEntry) by (intros ? ?; discriminate).
      unfold log_empty; rewrite !getenv_create.
      rewrite !get_put_eq.
      rewrite !get_put_neq by congruence.
      rewrite !getenv_create.
      rewrite (getenv_unlift_REnv _ type_denote).

      split; reflexivity.
    - rewrite Bits.of_index_to_index_safe; reflexivity.
    - unfold may_read0.
      rewrite (getenv_unlift_REnv _ LogEntry).
      unfold log_empty; rewrite getenv_create.
      reflexivity.
  Qed.
End Proofs.

Definition r reg : R reg :=
  match reg with
  | in_buf => Bits.zero
  | out_buf => Bits.zero
  | rf r => Bits.zero
  end.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := fun _ => false;
                   koika_scheduler := sched;
                   koika_module_name := "simple_proof" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "simple_proof.ml" prog.
