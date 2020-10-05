(*! Frontend | Parser for the typed Kôika EDSL !*)
Require Import
        Koika.Common
        Koika.TypedSyntax
        Koika.IdentParsing.

Export Koika.Types.SigNotations.
Export Koika.Primitives.PrimTyped.
Export Coq.Strings.String.
Export Coq.Lists.List.ListNotations.

Declare Custom Entry tkoika.
Declare Custom Entry tkoika_args.
Declare Custom Entry tkoika_var.
Declare Custom Entry tkoika_types.
Declare Custom Entry tkoika_branches.
Declare Custom Entry tkoika_consts.

Notation "'<{' e '}>'" :=
  (e)
    (e custom tkoika at level 200,
     format "'<{' '[v' '/' e '/' ']' '}>'").

(* Koika_consts *)
Notation "'1'" :=
  (Ob~1)
    (in custom tkoika_consts at level 0).
Notation "'0'" :=
  (Ob~0)
    (in custom tkoika_consts at level 0).

Notation "bs '~' '0'" :=
  (Bits.cons false bs)
    (in custom tkoika_consts at level 7,
        left associativity,
        format "bs '~' '0'").
Notation "bs '~' '1'" :=
  (Bits.cons true bs)
    (in custom tkoika_consts at level 7,
        left associativity,
        format "bs '~' '1'").
Notation "'Ob' '~' number" :=
  (Const (tau := bits_t _) number)
    (in custom tkoika at level 7,
        number custom tkoika_consts at level 99,
        format "'Ob' '~' number").

Notation "'|' a '`d' b '|'" :=
  (Const (tau := bits_t a) (Bits.of_N a b%N))
    (in custom tkoika,
        a constr at level 0,
        b constr at level 0,
        format "'|' a '`d' b '|'").

(* Koika_args *)
Declare Custom Entry tkoika_middle_args.

Notation "x" :=
  (CtxCons _ x CtxEmpty)
    (in custom tkoika_middle_args at level 0,
        x custom tkoika at level 99).

Notation "x ',' y" :=
  (CtxCons _ x y)
    (in custom tkoika_middle_args at level 1,
        x custom tkoika_middle_args,
        y custom tkoika_middle_args,
        right associativity).

Notation "'()'" :=
  CtxEmpty (in custom tkoika_args).

Notation "'(' x ')'" :=
  x (in custom tkoika_args, x custom tkoika_middle_args).
(* Koika_var *)

(* Class NameRef := nr_name: string. *)
(* Hint Extern 1 NameRef => serialize_ident_in_context : typeclass_instances. *)

(* Notation ident_to_string' a := (match __Ltac2_Mark return NameRef with *)
(*                                | a => _ *)
(*                                end) (only parsing). *)

Notation "a" :=
  (ident_to_string a)
    (in custom tkoika_var at level 0, a constr at level 0, format "'[' a ']'", only parsing).
Notation "a" :=
  (a)
    (in custom tkoika_var at level 0, a constr at level 0, format "'[' a ']'", only printing).

(* Koika_types *)
Notation " '(' x ':' y ')'" :=
  (cons (x%string, y) nil)
    (in custom tkoika_types at level 60,
        x custom tkoika_var at level 0,
        y constr at level 12).
Notation "a  b" :=
  (app a b)
    (in custom tkoika_types at level 95,
        a custom tkoika_types,
        b custom tkoika_types,
        right associativity).

(* Koika_branches *)
Notation "x '=>' a " :=
  (cons (x, a) nil)
    (in custom tkoika_branches at level 60,
        x custom tkoika at level 99,
        a custom tkoika at level 89).
Notation "arg1 '|' arg2" :=
  (app arg1 arg2)
    (in custom tkoika_branches at level 13,
        arg1 custom tkoika_branches,
        arg2 custom tkoika_branches,
        format "'[v' arg1 ']' '/' '|'  '[v' arg2 ']'").

(* Koika *)

Notation "'fail'" :=
  (Fail _)
    (in custom tkoika, format "'fail'").
Notation "'fail' '(' t ')'" :=
  (Fail (bits_t t))
    (in custom tkoika,
        t constr at level 0,
        format "'fail' '(' t ')'").
Notation "'fail' '@(' t ')'" :=
  (Fail t)
    (in custom tkoika,
        t constr at level 0,
        format "'fail' '@(' t ')'").

Require Import Magic.

Notation "'pass'" :=
  (Const (tau := bits_t 0) Ob)
    (in custom tkoika).
Notation "'magic'" :=
  (Const __magic__)
    (in custom tkoika).

Notation "'let' a ':=' b 'in' c" :=
  (Bind a b c)
    (in custom tkoika at level 91,
        a custom tkoika_var at level 1,
        right associativity,
        format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").
Notation "a ';' b" :=
  (Seq a b)
    (in custom tkoika at level 90,
        format "'[v' a ';' '/' b ']'" ).
Notation "'set' a ':=' b" :=
  (Assign (k := a) _ b)
    (in custom tkoika at level 89,
        a custom tkoika_var at level 1,
        format "'set'  a  ':='  b").
Notation "'(' a ')'" :=
  (a)
    (in custom tkoika at level 1,
        a custom tkoika,
        format "'[v' '(' a ')' ']'").

(* Notation "instance  '.(' method ')' args" := *)
(*   (USugar (UCallModule instance _ method args)) *)
(*     (in custom tkoika at level 1, *)
(*         instance constr at level 0, *)
(*         method constr, *)
(*         args custom tkoika_args at level 99). *)
(* Notation "'{' method '}' args" := *)
(*   (USugar (UCallModule id _ method args)) *)
(*     (in custom tkoika at level 1, *)
(*         method constr at level 200, *)
(*         args custom tkoika_args at level 99, *)
(*         only parsing). *)
(* Notation "method args" := *)
(*   (USugar (UCallModule id _ method args)) *)
(*     (in custom tkoika at level 1, *)
(*         method constr at level 0, *)
(*         args custom tkoika_args at level 99, *)
(*         only parsing). *)

Notation "a" :=
  (Var (k := a) _)
  (* (match a with *)
  (*  | k => Var (k := k) *)
  (*            ltac:( *)
  (*          lazymatch goal with *)
  (*          | |- VarRef ?sig ?k _ => exact (projT2 (must (assoc k sig))) *)
  (*          end) *)
  (* end) *)
    (in custom tkoika at level 1, a custom tkoika_var at level 0, only parsing).
Notation "a" :=
  (Var (k := a) _)
    (in custom tkoika at level 1, a custom tkoika_var at level 0, only printing).

Notation "'read0' '(' reg ')' " :=
  (Read P0 reg)
    (in custom tkoika,
        reg constr,
        format "'read0' '(' reg ')'").
Notation "'read1' '(' reg ')' " :=
  (Read P1 reg)
    (in custom tkoika,
        reg constr,
        format "'read1' '(' reg ')'").
Notation "'write0' '(' reg ',' value ')'" :=
  (Write P0 reg value)
    (in custom tkoika,
        reg constr at level 13,
        format "'write0' '(' reg ',' value ')'").
Notation "'write1' '(' reg ',' value ')'" :=
  (Write P1 reg value)
    (in custom tkoika,
        reg constr at level 13,
        format "'write1' '(' reg ',' value ')'").

(* FIXME: need better way to infer the argument in Const *)

Notation "'if' a 'then' t 'else' f" :=
  (If a t f)
    (in custom tkoika at level 86,
        right associativity,
        format "'[v' 'if'  a '/' 'then'  t '/' 'else'  f ']'").
Notation "'guard' '(' a ')' " :=
  (If (Unop (Bits1 (Not 1)) a) (Fail (bits_t 0)) (Const (tau := bits_t 0) Ob))
    (in custom tkoika at level 86,
        right associativity,
        format "'guard' '(' a ')'").
Notation "'when' a 'do' t " :=
  (If a t (Const (tau := bits_t 0) Ob))
    (in custom tkoika at level 91,
        right associativity,
        format "'[v' 'when'  a '/' 'do'  t '/' ']'").

Notation "a '&&' b" :=
  (Binop (Bits2 (And _)) a b)
    (in custom tkoika at level 80,
        right associativity,
        format "a  '&&'  b").
Notation "'!' a" :=
  (Unop (Bits1 (Not _)) a)
    (in custom tkoika at level 75,
        format "'!' a").
Notation "a '||' b" :=
  (Binop (Bits2 (Or _)) a b)
    (in custom tkoika at level 85,
        format "a  '||'  b").
Notation "'zeroExtend(' a ',' b ')'" :=
  (Unop (Bits1 (ZExtL _ b)) a)
    (in custom tkoika,
        b constr at level 0,
        format "'zeroExtend(' a ',' b ')'").
Notation "'sext(' a ',' b ')'" :=
  (Unop (Bits1 (SExt _ b)) a)
    (in custom tkoika,
        b constr at level 0,
        format "'sext(' a ',' b ')'").
Notation "'ignore(' a ')'" :=
  (Unop (Conv _ Ignore) a)
    (in custom tkoika,
        a custom tkoika).
Notation "'pack(' a ')'" :=
  (Unop (Conv _ Pack) a)
    (in custom tkoika,
        a custom tkoika).
Notation "'unpack(' t ',' v ')'" :=
  (Unop (Conv t Unpack) v)
    (in custom tkoika,
        t constr at level 11,
        v custom tkoika).
Notation "a  '^'  b" :=
  (Binop (Bits2 (Xor _)) a b)
    (in custom tkoika at level 85).
Notation "a  '+'  b" :=
  (Binop (Bits2 (Plus _)) a b)
    (in custom tkoika at level 85).
Notation "a  '-'  b" :=
  (Binop (Bits2 (Minus _)) a b)
    (in custom tkoika at level 85).
Notation "a  '*'  b" :=
  (Binop (Bits2 (Mul _ _)) a b)
    (in custom tkoika at level 84).
Notation "a  '!='  b" :=
  (Binop (Eq _ true) a b)
    (in custom tkoika at level 79).
Notation "a  '=='  b" :=
  (Binop (Eq _ false) a b)
    (in custom tkoika at level 79).
Notation "a  '>>'  b" :=
  (Binop (Bits2 (Lsr _ _)) a b)
    (in custom tkoika at level 79).
Notation "a  '>>>'  b" :=
  (Binop (Bits2 (Asr _ _)) a b)
    (in custom tkoika at level 79).
Notation "a  '<<'  b" :=
  (Binop (Bits2 (Lsl _ _)) a b)
    (in custom tkoika at level 79).
Notation "a  '<'  b" :=
  (Binop (Bits2 (Compare false cLt _)) a b)
    (in custom tkoika at level 79).
Notation "a  '<s'  b" :=
  (Binop (Bits2 (Compare true cLt _)) a b)
    (in custom tkoika at level 79).
Notation "a  '<='  b" :=
  (Binop (Bits2 (Compare false cLe _)) a b)
    (in custom tkoika at level 79).
Notation "a  '<s='  b" :=
  (Binop (Bits2 (Compare true cLe _)) a b)
    (in custom tkoika at level 79).
Notation "a  '>'  b" :=
  (Binop (Bits2 (Compare false cGt _)) a b)
    (in custom tkoika at level 79).
Notation "a  '>s'  b" :=
  (Binop (Bits2 (Compare true cGt _)) a b)
    (in custom tkoika at level 79).
Notation "a  '>='  b" :=
  (Binop (Bits2 (Compare false cGe _)) a b)
    (in custom tkoika at level 79).
Notation "a  '>s='  b" :=
  (Binop (Bits2 (Compare true cGe _)) a b)
    (in custom tkoika at level 79).
Notation "a '++' b" :=
  (Binop (Bits2 (Concat _ _)) a b)
    (in custom tkoika at level 80,
        right associativity,
        format "a  '++'  b").
Notation "a '[' b ']'" :=
  (Binop (Bits2 (Sel _)) a b)
    (in custom tkoika at level 75,
        format "'[' a [ b ] ']'").
(* Notation "a '[' b ':' c ']'" := *)
(*    (Binop (Bits2 (IndexedSlice _ c)) a b) *)
(*    (in custom tkoika at level 75, *)
(*        c constr at level 0, *)
(*        format "'[' a [ b ':' c ] ']'"). *)
Notation "a '[' b ':+' c ']'" :=
  (Binop (Bits2 (IndexedSlice _ c)) a b)
    (in custom tkoika at level 75,
        c constr at level 0,
        format "'[' a [ b ':+' c ] ']'").
Notation "'`' a '`'" :=
  (a)
    (in custom tkoika at level 99,
        a constr at level 99).

(* FIXME Hint Mode for VarRef *)
Notation "'fun' nm args ':' ret '=>' body" :=
  (@Build_InternalFunction'
     string (action _ _ string _ _ (List.rev args) ret)
     nm%string body)
    (in custom tkoika at level 99,
        nm custom tkoika_var at level 0,
        args custom tkoika_types,
        ret constr at level 0,
        body custom tkoika at level 99,
        format "'[v' 'fun'  nm  args  ':'  ret  '=>' '/' body ']'").

Notation "'fun' nm '()' ':' ret '=>' body" :=
  (@Build_InternalFunction'
     string (action _ _ string _ _ (List.rev nil) ret)
     nm%string body)
    (in custom tkoika at level 99,
        nm custom tkoika_var at level 0,
        ret constr at level 0,
        body custom tkoika at level 99,
        format "'[v' 'fun'  nm  '()'   ':'  ret  '=>' '/' body ']'").

(* Deprecated *)
(* Notation "'call' instance method args" := *)
(*   (USugar (UCallModule instance _ method args)) *)
(*     (in custom tkoika at level 99, *)
(*         instance constr at level 0, *)
(*         method constr at level 0, *)
(*         args custom tkoika_args). *)

Notation "'funcall' method args" :=
  (InternalCall method args)
    (in custom tkoika at level 98,
        method constr at level 0,
        args custom tkoika_args).

Notation "'extcall' method '(' arg ')'" :=
  (ExternalCall method arg)
    (in custom tkoika at level 98,
        method constr at level 0,
        arg custom tkoika).

(* Notation "'call0' instance method " := *)
(*   (USugar (UCallModule instance _ method nil)) *)
(*     (in custom tkoika at level 98, *)
(*         instance constr at level 0, *)
(*         method constr). *)

Notation "'funcall0' method " :=
  (InternalCall _ method nil)
    (in custom tkoika at level 98,
        method constr at level 0).

(* Definition str tau := *)
(*   (must (match tau )) *)

Section TypedMacros.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv : Env reg_t}.

  Notation action := (action pos_t var_t fn_name_t R Sigma).

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
End TypedMacros.

Notation must_field sig f :=
  (must (PrimTypeInference.find_field_opt sig f)).

Notation must_field_of_action a f :=
  (must_field (must (struct_sig_of_action a)) f).

(* Class StructField (sig: struct_sig) (f: string) := *)
(*   sf_idx : struct_index sig. *)

(* Hint Extern 1 (StructField ?sig ?f) => exact (must_field sig f) : typeclass_instances. *)
(* Hint Mode StructField + + : typeclass_instances. *)

(* Notation "'get' '(' v ',' f ')'" := *)
(*   (Unop (Struct1 GetField _ (_: StructField _ f)) v) *)
(*     (in custom tkoika, *)
(*         v custom tkoika at level 13, *)
(*         f custom tkoika_var at level 0, *)
(*         format "'get' '(' v ','  f ')'"). *)

Notation "'getbits' '(' sig ',' v ',' f ')'" :=
  (Unop (Bits1 (GetFieldBits sig (must_field sig f))) v)
    (in custom tkoika,
        sig constr at level 11,
        v custom tkoika at level 13,
        f custom tkoika_var at level 0,
        format "'getbits' '(' sig ','  v ','  f ')'").

(* Notation "'subst' '(' v ',' f ',' a ')'" := *)
(*   (Binop (Struct2 SubstField _ (_: StructField _ f)) v a) *)
(*     (in custom tkoika, *)
(*         v custom tkoika at level 13, *)
(*         a custom tkoika at level 13, *)
(*         f custom tkoika_var at level 0, *)
(*         format "'subst' '(' v ','  f ',' a ')'"). *)

Notation "'substbits' '(' sig ',' v ',' f ',' a ')'" :=
  (Binop (Bits2 (SubstFieldBits sig (must_field sig f))) v a)
    (in custom tkoika,
        sig constr at level 11,
        v custom tkoika at level 13,
        a custom tkoika at level 13,
        f custom tkoika_var at level 0,
        format "'substbits' '(' sig ','  v ','  f ',' a ')'").

Declare Custom Entry tkoika_structs_init.

Notation "f ':=' expr ';'  rest" :=
  (CtxCons (f, _) expr rest)
    (in custom tkoika_structs_init at level 20,
        f custom tkoika_var at level 0,
        expr custom tkoika at level 88,
        rest custom tkoika_structs_init).

Notation "f ':=' expr" :=
  (CtxCons (f, _) expr CtxEmpty)
    (in custom tkoika_structs_init at level 20,
        f custom tkoika_var at level 0,
        expr custom tkoika at level 88).

Notation "'struct' sig '{' fields '}'" :=
  (struct_init sig fields)
    (in custom tkoika,
        sig constr at level 0,
        fields custom tkoika_structs_init at level 92).

Notation "'enum' sig '{' name '}'" :=
  (Const (tau := enum_t sig)
         (vect_nth (sig.(enum_bitpatterns))
                   (must (vect_index name sig.(enum_members)))))
    (in custom tkoika at level 1,
        sig constr at level 1,
        name custom tkoika_var at level 1).

Notation "'match' term 'with' '|' branches 'return' 'default' ':' default 'end'" :=
  (Bind "__reserved__matchPattern" term
        (switch (MemberHd ("__reserved__matchPattern", _) _)
                default branches))
    (in custom tkoika at level 30,
        term custom tkoika,
        branches custom tkoika_branches,
        default custom tkoika,
        format "'match'  term  'with' '/' '[v'  '|'  branches '/' 'return'  'default' ':' default ']' 'end'").

Notation "'#' s" :=
  (Const (tau := bits_t _) s)
    (in custom tkoika at level 98,
        s constr at level 0,
        only parsing).

Module Type Tests.
  Parameter pos_t : Type.
  Definition fn_name_t := string.

  Inductive reg_t := data0 | data1.
  Parameter ext_fn_t : Type.

  Axiom data1_sz : nat.
  Definition R (reg: reg_t): type :=
    match reg with
    | data0 => bits_t 32
    | data1 => bits_t data1_sz
    end.
  Parameter Sigma: ext_fn_t -> ExternalSignature.

  Notation action R Sigma := (action pos_t string fn_name_t R Sigma).

  (* With that instead of the typeclass we'll need to propagate top-down everywhere. *)
  (* Arguments Seq {pos_t var_t fn_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {sig tau} &. *)

  Definition test_2 : action R Sigma [("u", unit_t); ("v", unit_t)] _ :=
    <{ u; v }>.
  Definition test_3 : action R Sigma [("v", unit_t)] _ :=
    <{ set v := magic }>.

  Definition test_1 : action R Sigma [] (bits_t 3) :=
    <{ let v := fail(2) in magic }>.
  Definition test_1' : action R Sigma [] _ :=
    <{ let v := fail(2) in v }>.
  Definition test_2' : action R Sigma [] unit_t :=
    <{ magic; magic }>.
  Definition test_3' : action R Sigma [("v", unit_t)] unit_t :=
    <{ set v := magic; magic }>.
  Definition test_4 : action R Sigma [("v", unit_t)] _ :=
    <{ magic; set v := magic }>.
  Definition test_5 : action R Sigma [("v", unit_t)] unit_t :=
    <{ let v := set v := magic in magic }>.
  Definition test_6 : action R Sigma [("v", unit_t)] unit_t :=
    <{ let v := set v := magic; pass in magic; magic }>.
  Definition test_7 : action R Sigma [("v", unit_t)] unit_t :=
    <{ (let v := (set v := magic); pass in magic; magic) }>.
  Definition test_8 : action R Sigma [("v", unit_t)] unit_t :=
    <{ (let v := set v := magic; pass in magic); magic }>.
  Inductive test : Set := rData (n: nat).
  Definition R_test (reg: test) := match reg with rData n => bits_t n end.
  Definition test_9 : action R Sigma [] _ :=
    <{ read0(data0) }>.
  Definition test_10 : forall (idx: nat), action R_test Sigma [] (bits_t idx) :=
    (fun idx => <{ read0(rData idx) }>).
  Definition test_11 : action R Sigma [("v", unit_t)] unit_t :=
    <{ (let v := read0(data0) in write0(data0, magic)); fail }>.
  Definition test_12 : action R Sigma [] unit_t :=
    <{ (let v := if fail then read0(data0) else fail in
        write0(data0, magic)); fail }>.

  (* We're using Program Definition to work around quirks of Coq's type system. The alternative would be to use bidirectionality hints, but it's not robust: it breaks e.g. when specifying the return type of a concatenation, because without the argument we can't check that the concatenation has the right size.  *)
  (* Arguments Binop {pos_t}%type_scope {var_t fn_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {sig} fn &. *)
  (* Arguments Unop {pos_t var_t fn_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {sig} fn &. *)
  (* FIXME bidirectionality hints some examples fail. Using a typeclasses for ident parsing and Var resolution helps but doesn't solve the problem. *)

  Definition test_14 : action R Sigma [("v", bits_t 1)] (bits_t 1) :=
    <{ !v && v }>.
  Definition test_14' : action R Sigma [("v", bits_t 1)] _ :=
    <{ !(v && v) }>.
  Goal test_14 <> test_14'. Proof. compute; congruence. Qed.

  (* Arguments Write {pos_t var_t fn_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {sig} port idx &. *)

  Definition test_15 : action R Sigma [("v", _ (* inferred *))] _ :=
    <{ write0(data0, v); unpack(_ (* inferred *), v) && read0(data0) }>.
  Definition test_16 : action R Sigma [] _ :=
    <{ !read0(data0) && !read0(data0) }>. (* works without knowing the size of data1 *)
  Definition test_16' : action R Sigma [] _ :=
    <{ read0(data0) && read0(data0) }>.
  Definition test_17 : action R Sigma [] _ :=
    <{ !read0(data1) && magic}>.

  Program Definition test_18 : action R Sigma [("v", bits_t 32)] _ :=
    <{ !read0(data0) && v }>.

  Definition test_19 : action R Sigma [("v", bits_t 32); ("w", bits_t 5); ("x", bits_t 5)] _ :=
    <{ v [#(Bits.of_nat _ 2)] && Ob~1 }>.
  Program Definition test_20 : action R Sigma _ _ :=
    <{ let v := |32`d0| in v[Ob~0~0~0~0~0] }> : action R Sigma [] _.

  (* Using Program Definition makes finding type errors much nicer: *)
  Program Definition broken : action R Sigma [("v", bits_t 32)] _ :=
    <{ !read0(data0) && v && v[Ob~0] }>.
  Next Obligation.
    exact 32.
  Defined.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  Program Definition test_20' : action R Sigma [("v", bits_t 32)] _ :=
    <{ (v[magic :+ 3] ++ v) && (v[magic :+ 35]) }>.
  Program Definition test_20'' : action R Sigma [("v", bits_t 32); ("w", bits_t 16)] (bits_t 51) :=
    <{ (v ++ w ++ v[magic :+ 3]) }>.

  Notation InternalFunction sig tau := (InternalFunction pos_t string fn_name_t R Sigma sig tau).

  Definition test_23 : InternalFunction _ _ :=
    <{ fun test (arg1 : (bits_t 3)) (arg2 : bits_t 2) : bits_t 4 => magic }>.

  Definition test_24 : forall sz: nat, InternalFunction _ _ :=
    (fun sz => <{ fun test (arg1 : bits_t sz) (arg1 : bits_t sz) : bits_t sz  => magic}>).
  Definition test_25 : forall sz: nat, InternalFunction _ _ :=
    (fun sz => <{fun test (arg1 : bits_t sz ) : bits_t sz => let oo := pass >> pass in magic}>).
  Definition test_26 : forall sz: nat, InternalFunction _ _ :=
    (fun sz => <{ fun test () : bits_t sz  => magic }>).
  Program Definition test_27 : action R Sigma [("w", bits_t 1)] _ :=
    <{
        (if !(read0(data0)[Ob~0~0~0~0~0]) then
           write0(data0, |32`d0|);
           let u := if (w == Ob~1) then w else w || w
           in write0(data0, |32`d0|)
         else
           (ignore(read0(data0)); pass));
        fail(4)
    }>.
  Definition test_28 : action R Sigma [("var", bits_t 5)] unit_t :=
    <{
      match var with
      | magic => magic
      return default: magic
      end
    }>.

  Definition test_sig :=
    {| struct_name := "test_sig";
       struct_fields := [("foo", bits_t 2); ("bar", bits_t 32)] |}.

  Program Definition test_30'' : action R Sigma [("v", bits_t 5)] _ :=
    <{
      struct test_sig { foo := v[#(Bits.of_nat 3 0) :+ 2];
                        bar := |32`d98| }
    }>.

  Definition test_31'' : action R Sigma [("a", struct_t test_sig)] _ :=
    <{
        pack(a)
    }>.

  Program Definition test_31' : action R Sigma [("v", bits_t 5)] _ :=
    <{
      let a := struct test_sig { foo := v[#(Bits.of_nat 3 0) :+ 2];
                                bar := |32`d98| } in
      unpack(struct_t test_sig, pack(a))
    }>.

  (* Definition test_32 : action R Sigma [("v", struct_t test_sig)] _ := *)
  (*   <{ subst(v, foo, <{ Ob~1~1 }>) *)
  (*   }>. *)
End Tests.
