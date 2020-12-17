(*! Computing terms of the Collatz sequence (Coq version) !*)
Require Koika.Frontend.
Require Import NumberParsing.

Module Test.
  Import Frontend.

  Notation "sz ''b' num" :=
    (Const (tau := bits_t sz) (tc_compute ((must_bits (decode_bitstring_from_bits sz num%bitstrings)): bits_t sz)))
      (in custom tkoika at level 1, sz constr at level 0, num constr at level 0, no associativity, only parsing).

  Definition t : action (fun _: unit => bits_t 0) empty_Sigma [] (bits_t 1) :=
    <{ let a := 1'b0 in let b := 1'b1 in a && b }>.
End Test.

Open Scope string_scope.
Import Vect.
Import VectNotations.
Require Import Lists.List.
Import ListNotations.
Eval simpl in ltac:(let t := eval unfold Test.t in Test.t in exact t).


Module Collatz.
  Inductive reg_t := r0.
  Inductive rule_name_t := divide | multiply.

  Definition logsz := 4.
  Notation sz := (pow2 logsz).

  Definition R r :=
    match r with
    | r0 => bits_t sz
    end.

  Definition r idx : R idx :=
    match idx with
    | r0 => Bits.of_nat sz 18
    end.

  Notation "sz ''b' num" :=
    (Const (tau := bits_t sz) (tc_compute ((must_bits (decode_bitstring_from_bits sz num%bitstrings)): bits_t sz)))
      (in custom tkoika at level 1, sz constr at level 0, num constr at level 0, no associativity, only parsing).

  Check <{ let a := 4'b0 in let b := 4'b1 in a + b }>.

  Definition times_three : InternalFunction R empty_Sigma _ _ :=
    <{ fun times_three (bs: bits_t 16) : bits_t 16 =>
         (bs << Ob~1) + bs }>.

  Program Definition _divide : rule R empty_Sigma :=
    <{ let v := read0(r0) in
       let odd := v[Ob~0~0~0~0] in
       if !odd then
         write0(r0,v >> Ob~1)
       else
         fail }>.

  Program Definition _multiply : rule R empty_Sigma :=
    <{ let v := read1(r0) in
       let odd := v[4'b0] in
       if odd then
         write1(r0, times_three(v) + 16'b1)
       else
         fail }>.

  Definition collatz : scheduler :=
    divide |> multiply |> done.

  Definition cr := ContextEnv.(create) r.

  Definition rules :=
    fun r => match r with
          | divide => _divide
          | multiply => _multiply
          end.

  Definition cycle_log :=
    tc_compute (interp_scheduler cr empty_sigma rules collatz).

  Definition divide_result :=
    tc_compute (interp_action cr empty_sigma CtxEmpty log_empty log_empty
                              (rules divide)).

  Definition multiply_result :=
    tc_compute (interp_action cr empty_sigma CtxEmpty log_empty log_empty (rules multiply)).

  Definition result :=
    tc_compute (commit_update cr cycle_log).

  Definition external (r: rule_name_t) := false.

  Definition circuits :=
    compile_scheduler rules external collatz.

  Definition circuits_result :=
    tc_compute (interp_circuits empty_sigma circuits (lower_r (ContextEnv.(create) r))).

  Example test: circuits_result = Lowering.lower_r result :=
    eq_refl.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := empty_Sigma;
                     koika_rules := rules;
                     koika_rule_external := external;
                     koika_scheduler := collatz;
                     koika_module_name := "collatz" |};

       ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.
End Collatz.

Definition prog := Interop.Backends.register Collatz.package.
