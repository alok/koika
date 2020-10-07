(*! Frontend | Parser for the typed Kôika EDSL !*)
Require Import
        Koika.Common
        Koika.TypedSyntaxMacros
        Koika.IdentParsing.
Require Import
        Koika.Magic.

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
     format "'<{'  '[hv  ' e ']'  '}>'"). (* FIXME parsing.v format *)

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

Notation "'Ob'" :=               (* FIXME copy to Parsing.v? *)
  (Const (tau := bits_t 0) Ob)
    (in custom tkoika at level 7,
        format "'Ob'").

Check <{ Ob~0~0~1 }>.
Check <{ Ob }>.

Notation "'|' a '`d' b '|'" :=
  (Const (tau := bits_t a) (Bits.of_N a b%N))
    (in custom tkoika,
        a constr at level 0,
        b constr at level 0,
        format "'|' a '`d' b '|'").

Check <{ |3`d0| }>.

Notation "'$' n" :=
  (Const (tau := bits_t _) (Bits.of_N _ n%N))
    (in custom tkoika at level 0,
        n constr at level 0,
        format "'$' n").

Check <{ $3 }>.

Notation "'#' s" :=
  (Const (tau := bits_t _) s)
    (in custom tkoika at level 98,
        s constr at level 0,
        only parsing).

Check <{ #(Bits.of_nat _ 3) }>. (* FIXME not reparseable *)

Notation "'(' a ')'" :=
  (a)
    (in custom tkoika at level 1,
        a custom tkoika at level 200,
        format "'[v' '(' a ')' ']'").
Check <{ (($3)) }>.

(* Koika_var *)
(* Class NameRef := nr_name: string. *)
(* Hint Extern 1 NameRef => serialize_ident_in_context : typeclass_instances. *)
(* Notation ident_to_string' a := (match __Ltac2_Mark return NameRef with *)
(*                                | a => _ *)
(*                                end) (only parsing). *)


Notation "a" :=
  (ident_to_string a)
    (in custom tkoika_var at level 0,
        a constr at level 0,
        only parsing).
Notation "a" :=
  (a)
    (in custom tkoika_var at level 0,
        a constr at level 0,
        only printing).

(* This typeclass trick doesn't work.  I added it in hopes of making struct_sig
   inference possible, but it's not enough.  Take a bit of code like get(v,
   foo), where v is a struct in context.  There are two typeclasses to infer:

   - ?vr: VarRef [("v", struct_t test_sig)] "v" (arg1Sig (Struct1 ?sg ?idx)))
   - ?idx: StructField ?sg foo

   The problem is that the variable type in the VarRef (spuriously) depends
   on ?idx, and so TC resolution tries to find the ?idx first, which it can't
   since ?sg isn't resolved yet.

   Making the type explicit removed the dependency and fixed it, so the hope
   would be that using an untyped VarRef would help, but it didn't:

    Definition xx : action R Sigma [("v", struct_t test_sig)] _ :=
      <{ get(`Var (_: VarRef [("v", struct_t test_sig)] "v" (struct_t test_sig))`, foo) }>. *)

(* Class UntypedVarRef {var_t} (sig: tsig var_t) (k: var_t) := *)
(*   { uvr_tau : type; *)
(*     uvr_m : member (k, uvr_tau) sig }. *)
(* Definition VarRef_of_UntypedVarRef *)
(*            {var_t} {sig: tsig var_t} {k: var_t} *)
(*            (uvr: UntypedVarRef sig k): VarRef sig k uvr_tau := *)
(*   uvr_m. *)
(* Hint Extern 1 (UntypedVarRef ?sig ?k) => *)
(*   exact {| uvr_m := projT2 (must (assoc k sig)) |} : typeclass_instances. *)

Class VarRef {var_t} (sig: tsig var_t) (k: var_t) (tau: type) :=
  vr_m : member (k, tau) sig.

(* Specify that TC resolution shouldn't guess sig or k, but may guess tau. *)
Hint Mode VarRef + ! ! - : typeclass_instances.

(* Teach Coq how to find a variable in context *)
Hint Extern 1 (VarRef ?sig ?k _) =>
  exact (projT2 (must (assoc k sig))) : typeclass_instances.

(* This notation uses ident_to_string and "a constr" instead of "a custom
   tkoika_var" to avoid a conflict with the notation for function calls *)

Notation "a" :=
  (Var (_: VarRef _ (ident_to_string a) _))
  (* (match a with *)
  (*  | k => Var (k := k) *)
  (*            ltac:( *)
  (*          lazymatch goal with *)
  (*          | |- VarRef ?sig ?k _ => exact (projT2 (must (assoc k sig))) *)
  (*          end) *)
  (* end) *)
    (in custom tkoika at level 1,
        a constr at level 0,
        only parsing).
Notation "'&' a" :=              (* FIXME Parsing.v *)
  (Var (k := a) _)
    (in custom tkoika at level 1,
        a constr at level 0,
        format "'&' a").

Check <{ x }>.

(* Koika *)

(* FIXME Parsing.v only parsing *)
Notation "'fail'" :=
  (Fail _)
    (in custom tkoika at level 0,
        format "'fail'",
        only parsing).
Notation "'fail' '(' t ')'" :=
  (Fail (bits_t t))
    (in custom tkoika,
        t constr at level 0,
        format "'fail' '(' t ')'",
        only parsing).
Notation "'fail@' t" :=
  (Fail t)
    (in custom tkoika at level 0,
        t constr at level 0,
        format "'fail@' t").

Check <{ fail }>.
Check <{ fail(1) }>.
Check <{ fail@unit_t }>.
Check <{ fail@(bits_t 1) }>.

Notation "'pass'" :=
  (Const (tau := bits_t 0) Ob)
    (in custom tkoika).
Check <{ pass }>.

Notation "'__'" :=
  (Const __magic__)
    (in custom tkoika).
Check <{ __ }>.

Notation "'let' a ':=' b 'in' c" :=
  (Bind a b c)
    (in custom tkoika at level 91,
        a custom tkoika_var at level 1,
        b custom tkoika at level 91, (* FIXME required by the printer? *)
        c custom tkoika at level 91, (* FIXME required by the printer? *)
        format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").

Check <{ let a := pass in pass }>.
Check <{ let a := let b := pass in pass in pass }>.
Check <{ let a := pass in let b := pass in pass }>.

Notation "a ';' b" :=
  (Seq a b)
    (in custom tkoika at level 90,
        a custom tkoika,
        b custom tkoika at level 90,       (* FIXME needed by printer? *)
        format "'[hv' a ';'  '/' b ']'" ). (* FIXME parsing.v hv *)
(* Check <{ a; b }>. *)
(* Check <{ (a; b); c }>. (* FIXME printer ambiguous *) *)
(* Check <{ a; (b; c) }>. (* FIXME printer ambiguous *) *)

Notation "'set' a ':=' b" :=
  (Assign (_: VarRef _ a _) b)
    (in custom tkoika at level 89,
        a custom tkoika_var at level 1,
        b custom tkoika at level 89, (* FIXME parsing.v, review *)
        format "'[hv  ' 'set'  a  ':='  '/' b ']'").
Check <{ (set a := b); c }>.
(* Check <{ set a := (b; c) }>.     (* FIXME *) *)

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
        value custom tkoika at level 0, (* FIXME without this this isn't reparseable *)
        format "'write0' '(' reg ','  value ')'").
Notation "'write1' '(' reg ',' value ')'" :=
  (Write P1 reg value)
    (in custom tkoika,
        reg constr at level 13,
        value custom tkoika at level 0, (* FIXME without this this isn't reparseable *)
        format "'write1' '(' reg ','  value ')'").

Check <{ write0(_, read0(_)) }>.
Check <{ write1(_, read1(_)) }>.
Check <{ write0(_, $0) }>.
Check <{ write1(_, let x := $1 in x) }>. (* FIXME not printable *)

Notation "'if' a 'then' t 'else' f" :=
  (If a t f)
    (in custom tkoika at level 86,
        a custom tkoika at level 86,
        t custom tkoika at level 86,
        f custom tkoika at level 86,
        right associativity,
        format "'[v' 'if'  a '/' 'then'  t '/' 'else'  f ']'").
Check <{ if __ then __ else __ }>.
Check <{ if __ then __ else __ }>.

Notation "'guard' '(' a ')' " :=
  (If (Unop (Bits1 (Not 1)) a) (Fail (bits_t 0)) (Const (tau := bits_t 0) Ob))
    (in custom tkoika at level 86,
        right associativity,
        a custom tkoika at level 86,
        format "'guard' '(' a ')'").
Check <{ guard(__) }>.

Notation "'when' a 'do' t " :=
  (If a t (Const (tau := bits_t 0) Ob))
    (in custom tkoika at level 91,
        a custom tkoika at level 86,
        t custom tkoika at level 91,
        right associativity,
        format "'[v' 'when'  a '/' 'do'  t ']'"). (* FIXME parsing.v removed final '/' *)
(* Check <{ when a do t }>. *)

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

(* Koika_types *)
Notation "'(' x ':' y ')'" :=
  (cons (x%string, y) nil)
    (in custom tkoika_types at level 60,
        x custom tkoika_var at level 0,
        y constr at level 12).
Notation "'(' x ':' y ')'  b" :=
  (cons (x%string, y) b)
    (in custom tkoika_types at level 60,
        x custom tkoika_var at level 0,
        y constr at level 12).

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

(* Koika_args *)
Declare Custom Entry tkoika_arglist.

Notation "x" :=
  (CtxCons _ x CtxEmpty)
    (in custom tkoika_arglist at level 0,
        x custom tkoika at level 99).
Notation "x ',' y" :=
  (CtxCons _ x y)
    (in custom tkoika_arglist at level 0,
        x custom tkoika at level 99,
        y custom tkoika_arglist,
        right associativity).

Notation "'()'" :=
  CtxEmpty (in custom tkoika_args).
Notation "'(' x ')'" :=
  x (in custom tkoika_args at level 0,
        x custom tkoika_arglist at level 0).

Notation "instance  '.(' method ')' args" :=
  (InternalCall
     (lift_intfun {| lift_fn := instance |} _ method)
     args)
    (in custom tkoika at level 1,
        instance constr at level 0,
        method constr,
        args custom tkoika_args at level 99).
Notation "'{' method '}' args" :=
  (InternalCall method args)
    (in custom tkoika at level 1,
        method constr at level 200,
        args custom tkoika_args at level 99,
        only parsing).
Notation "method args" :=
  (InternalCall method args)
    (in custom tkoika at level 1,
        method constr at level 0,
        args custom tkoika_args at level 99,
        only parsing).

(* Check <{ (?[f]: InternalFunction ) (a, b) }>. *)
(* Check <{ v .( w ) () }>. *)

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

Notation "'call0' instance method " :=
  (InternalCall
     (lift_intfun {| lift_fn := instance |} _ method)
     CtxEmpty)
    (in custom tkoika at level 98,
        instance constr at level 0,
        method constr).

Notation "'funcall0' method " :=
  (InternalCall _ method nil)
    (in custom tkoika at level 98,
        method constr at level 0).

Notation must_field sig f :=
  (must (PrimTypeInference.find_field_opt sig f)).

Class StructField (sig: struct_sig) (f: string) :=
  sf_idx : struct_index sig.

Hint Extern 1 (StructField ?sig ?f) => exact (must_field sig f) : typeclass_instances.
Hint Mode StructField + + : typeclass_instances.

Notation "'get@' sig '(' v ',' f ')'" :=
  (Unop (Struct1 GetField sig (_: StructField sig f)) v)
    (in custom tkoika,
        sig constr at level 0,
        v custom tkoika at level 13,
        f custom tkoika_var at level 0,
        format "'get@' sig '(' v ','  f ')'").

Notation "'getbits@' sig '(' v ',' f ')'" :=
  (Unop (Bits1 (GetFieldBits sig (must_field sig f))) v)
    (in custom tkoika,
        sig constr at level 0,  (* FIXME parsing.v level *)
        v custom tkoika at level 13,
        f custom tkoika_var at level 0,
        format "'getbits@' sig '(' v ','  f ')'").

Notation "'subst@' sig '(' v ',' f ',' a ')'" :=
  (Binop (Struct2 SubstField sig (_: StructField sig f)) v a)
    (in custom tkoika,
        sig constr at level 0,
        v custom tkoika at level 13,
        a custom tkoika at level 13,
        f custom tkoika_var at level 0,
        format "'subst@' sig '(' v ','  f ',' a ')'").

Notation "'substbits@' sig '(' v ',' f ',' a ')'" :=
  (Binop (Bits2 (SubstFieldBits sig (must_field sig f))) v a)
    (in custom tkoika,
        sig constr at level 0,
        v custom tkoika at level 13,
        a custom tkoika at level 13,
        f custom tkoika_var at level 0,
        format "'substbits@' sig '(' v ','  f ','  a ')'"). (* FIXME parsing.v spacing *)

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

Notation "'match' term 'with' '|' branches 'return' 'default' ':' default 'end'" :=
  (Bind "__reserved__matchPattern" term
        (switch (MemberHd ("__reserved__matchPattern", _) _)
                default branches))
    (in custom tkoika at level 30,
        term custom tkoika,
        branches custom tkoika_branches,
        default custom tkoika,
        format "'match'  term  'with' '/' '[v'  '|'  branches '/' 'return'  'default' ':' default ']' 'end'").

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

  Program Definition test_2 : action R Sigma [("u", unit_t); ("v", unit_t)] _ :=
    <{ u; v }>.
  Definition test_3 : action R Sigma [("v", unit_t)] _ :=
    <{ set v := __ }>.

  Definition test_1 : action R Sigma [] (bits_t 3) :=
    <{ let v := fail(2) in __ }>.
  Definition test_1' : action R Sigma [] _ :=
    <{ let v := fail(2) in v }>.
  Definition test_2' : action R Sigma [] unit_t :=
    <{ __; __ }>.
  Definition test_3' : action R Sigma [("v", unit_t)] unit_t :=
    <{ set v := __; __ }>.
  Definition test_4 : action R Sigma [("v", unit_t)] _ :=
    <{ __; set v := __ }>.
  Definition test_5 : action R Sigma [("v", unit_t)] unit_t :=
    <{ let v := set v := __ in __ }>.
  Definition test_6 : action R Sigma [("v", unit_t)] unit_t :=
    <{ let v := set v := __; pass in __; __ }>.
  Definition test_7 : action R Sigma [("v", unit_t)] unit_t :=
    <{ (let v := (set v := __); pass in __; __) }>.
  Definition test_8 : action R Sigma [("v", unit_t)] unit_t :=
    <{ (let v := set v := __; pass in __); __ }>.
  Inductive test : Set := rData (n: nat).
  Definition R_test (reg: test) := match reg with rData n => bits_t n end.
  Definition test_9 : action R Sigma [] _ :=
    <{ read0(data0) }>.
  Definition test_10 : forall (idx: nat), action R_test Sigma [] (bits_t idx) :=
    (fun idx => <{ read0(rData idx) }>).
  Definition test_11 : action R Sigma [("v", unit_t)] unit_t :=
    <{ (let v := read0(data0) in write0(data0, __)); fail }>.
  Definition test_12 : action R Sigma [] unit_t :=
    <{ (let v := if fail then read0(data0) else fail in
        write0(data0, __)); fail }>.

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
    <{ !read0(data1) && __}>.

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
    <{ (v[__ :+ 3] ++ v) && (v[__ :+ 35]) }>.
  Program Definition test_20'' : action R Sigma [("v", bits_t 32); ("w", bits_t 16)] (bits_t 51) :=
    <{ (v ++ w ++ v[__ :+ 3]) }>.

  Notation InternalFunction sig tau := (InternalFunction pos_t string fn_name_t R Sigma sig tau).

  Definition test_23 : InternalFunction _ _ :=
    <{ fun test (arg1 : (bits_t 3)) (arg2 : bits_t 2) : bits_t 4 => __ }>.

  Definition test_24 : forall sz: nat, InternalFunction _ _ :=
    (fun sz => <{ fun test (arg1 : bits_t sz) (arg1 : bits_t sz) : bits_t sz  => __}>).
  Definition test_25 : forall sz: nat, InternalFunction _ _ :=
    (fun sz => <{fun test (arg1 : bits_t sz ) : bits_t sz => let oo := pass >> pass in __}>).
  Definition test_26 : forall sz: nat, InternalFunction _ _ :=
    (fun sz => <{ fun test () : bits_t sz  => __ }>).
  Program Definition test_27 : InternalFunction [("w", bits_t 1)] _ :=
    <{ fun test (w: bits_t 1) : bits_t 4 =>
        (if !((read0(data0) && |32`d0|)[Ob~0~0~0~0~0]) then
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
      | __ => __
      return default: __
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

  Set Typeclasses Dependency Order.
  Set Typeclasses Filtered Unification.

  Definition xx : action R Sigma [("v", struct_t test_sig)] _ :=
    <{ get@test_sig(v, foo) }>.

  Program Definition test_32 : action R Sigma [("v", struct_t test_sig)] _ :=
    <{ subst@test_sig(v, foo, Ob~1~1) }>.
End Tests.
