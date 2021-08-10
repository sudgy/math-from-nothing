Require Import init.

Require Export set_base.
Require Export set_type.

(** Most of this file is hidden from the docs because you really don't need to
know all the random theorems that go into making this work.  What you need to
know is this:
- To define an equivalence class, make a value of type [equivalence U] (which
  we'll call [E]).  Then the new type is [equiv_type E].
- To define an operation on an equivalence class, you need to prove it's well
  defined and then use one of the definitions below (like [binary_self_op])
  with your proof.
- To pick a value from the equivalence class, use the tactic
  [equiv_get_value] on each equivalence class.
- If you have operations you defined on equivalence classes and you need to
  prove something about them, use [equiv_get_value] to pick values from all
  relevant equivalence classes then use the [equiv_simpl] tactic.  It will
  use all of your proofs that things are well-defined automatically to
  simplify down to proving things just for the particular values from your
  equivalence classes.
*)

#[universes(template)]
Record equivalence U := make_equiv {
    eq_equal : U → U → Prop;
    eq_reflexive : Reflexive eq_equal;
    eq_symmetric : Symmetric eq_equal;
    eq_transitive : Transitive eq_equal;
}.
Arguments make_equiv {U}.
Arguments eq_equal {U}.
Arguments eq_reflexive {U}.
Arguments eq_symmetric {U}.
Arguments eq_transitive {U}.

(* begin hide *)
Definition equiv_class {U} (E : equivalence U) (a : U) := λ x, eq_equal E a x.
Definition equiv_set {U} (E : equivalence U) := λ S, ∃ x, S = equiv_class E x.
(* end hide *)
(* begin show *)
Notation "'equiv_type' E" := (set_type (equiv_set E)) (at level 10).
Definition to_equiv_type {U} (E : equivalence U) (x : U) : equiv_type E.
    remember (equiv_class E x) as X.
    assert (equiv_set E X) as X_in.
    {
        exists x.
        exact HeqX.
    }
    exact (make_set_type_val X X_in).
Defined.
(* end show *)

(* begin hide *)
Definition unary_self_op_base {U : Type}
    (E : equivalence U) (f : U → U)
    (a : equiv_type E) :=
    λ y, ∃ x, [a|] x ∧ eq_equal E (f x) y.
Definition binary_self_op_base {U : Type}
    (E : equivalence U) (f : U → U → U)
    (a b : equiv_type E) :=
    λ y, ∃ x1 x2, [a|] x1 ∧ [b|] x2 ∧ eq_equal E (f x1 x2) y.
Definition binary_rself_op_base {U U2 : Type}
    (E : equivalence U) (f : U2 → U → U)
    (a : U2) (b : equiv_type E) :=
    λ y, ∃ x, [b|] x ∧ eq_equal E (f a x) y.

Section Equivalence.

Context {U U2 : Type} {E : equivalence U}.
Local Notation "a ~ b" := (eq_equal E a b).

Theorem equiv_eq_class : ∀ a b, equiv_class E a = equiv_class E b → a ~ b.
    intros a b eq.
    assert (equiv_class E b b) as bb by apply E.
    rewrite <- eq in bb.
    exact bb.
Qed.

Theorem equiv_eq : ∀ a b, (to_equiv_type E a = to_equiv_type E b) = (a ~ b).
    pose proof (eq_reflexive E).
    pose proof (eq_symmetric E).
    pose proof (eq_transitive E).
    intros a b.
    apply propositional_ext.
    split; intros eq.
    -   unfold to_equiv_type in eq.
        inversion eq as [eq']; clear eq.
        apply equiv_eq_class.
        exact eq'.
    -   apply set_type_eq; cbn.
        unfold equiv_class.
        apply antisym.
        +   intros x ax.
            apply sym in eq.
            exact (trans eq ax).
        +   intros x bx.
            exact (trans eq bx).
Qed.

Theorem equiv_type_eq : ∀ (A : set_type (equiv_set E)) a,
        [A|] = equiv_class E a → A = to_equiv_type E a.
    intros A a eq.
    apply set_type_eq.
    exact eq.
Qed.

Theorem unary_self_op_wd : ∀ (f : U → U), (∀ a b : U, a ~ b → f a ~ f b) →
        ∀ a, equiv_set E (unary_self_op_base E f a).
    pose proof (eq_reflexive E).
    pose proof (eq_symmetric E).
    pose proof (eq_transitive E).
    intros f wd [A [x Ax]].
    subst A.
    exists (f x).
    apply predicate_ext.
    intro y.
    split.
    -   intros [x' [x'_in x'_eq]]; cbn in *.
        specialize (wd _ _ x'_in).
        exact (trans wd x'_eq).
    -   intro eq.
        exists x.
        split.
        +   cbn.
            apply refl.
        +   exact eq.
Qed.
Theorem binary_self_op_wd : ∀ (f : U → U → U),
        (∀ a b c d : U, a ~ b → c ~ d → f a c ~ f b d) →
        ∀ a b, equiv_set E (binary_self_op_base E f a b).
    pose proof (eq_reflexive E).
    pose proof (eq_symmetric E).
    pose proof (eq_transitive E).
    intros f wd [A [a Aa]] [B [b Bb]].
    subst A B.
    exists (f a b).
    apply predicate_ext.
    intro y.
    unfold equiv_class.
    split.
    -   intros [x1' [x2' [x1'_in [x2'_in eq]]]]; cbn in *.
        specialize (wd _ _ _ _ x1'_in x2'_in).
        exact (trans wd eq).
    -   intro eq.
        exists a, b.
        cbn.
        repeat split; try apply refl.
        exact eq.
Qed.
Theorem binary_rself_op_wd : ∀ (f : U2 → U → U),
        (∀ a b c, a ~ b → f c a ~ f c b) →
        ∀ a b, equiv_set E (binary_rself_op_base E f a b).
    pose proof (eq_reflexive E).
    pose proof (eq_symmetric E).
    pose proof (eq_transitive E).
    intros f wd a [B [b Bb]].
    subst B.
    exists (f a b).
    apply predicate_ext.
    intro y.
    unfold equiv_class.
    split.
    -   intros [x [xb eq]]; cbn in *.
        specialize (wd _ _ a xb).
        exact (trans wd eq).
    -   intro eq.
        exists b.
        cbn.
        split; try apply refl.
        exact eq.
Qed.

End Equivalence.
(* end hide *)
Definition unary_op {U U2 : Type}
    {E : equivalence U} {f : U → U2}
    (wd : ∀ a b : U, eq_equal E a b → f a = f b)
    (a : equiv_type E) :=
    f (ex_val [|a]).
Definition binary_op {U U2 : Type}
    {E : equivalence U} {f : U → U → U2}
    (wd : ∀ a b c d : U, eq_equal E a b → eq_equal E c d → f a c = f b d)
    (a b : equiv_type E) :=
    f (ex_val [|a]) (ex_val [|b]).
Definition unary_self_op {U : Type}
    {E : equivalence U} {f : U → U}
    (wd : ∀ a b : U, eq_equal E a b → eq_equal E (f a) (f b))
    (a : equiv_type E) :=
    [unary_self_op_base E f a | unary_self_op_wd f wd a].
Definition binary_self_op {U : Type}
    {E : equivalence U} {f : U → U → U}
    (wd : ∀ a b c d : U, eq_equal E a b → eq_equal E c d →
        eq_equal E (f a c) (f b d))
    (a b : equiv_type E) :=
    [binary_self_op_base E f a b | binary_self_op_wd f wd a b].
Definition binary_rself_op {U U2 : Type}
    {E : equivalence U} {f : U2 → U → U}
    (wd : ∀ a b c, eq_equal E a b → eq_equal E (f c a) (f c b))
    (a : U2)  (b : equiv_type E) :=
    [binary_rself_op_base E f a b | binary_rself_op_wd f wd a b].

(* begin hide *)
Section Equivalence.

Context {U V : Type} {E : equivalence U}.
Local Notation "a ~ b" := (eq_equal E a b).
Context {un : U → V} {un_wd : ∀ a b, a ~ b → un a = un b}.
Context {bin : U → U → V}
        {bin_wd : ∀ a b c d, a ~ b → c ~ d → bin a c = bin b d}.
Context {sun : U → U} {sun_wd : ∀ a b, a ~ b → sun a ~ sun b}.
Context {sbin : U → U → U}
        {sbin_wd : ∀ a b c d, a ~ b → c ~ d → sbin a c ~ sbin b d}.
Context {rsbin : V → U → U} {rsbin_wd : ∀ a b c, a ~ b → rsbin c a ~ rsbin c b}.
Local Notation "'sUn'" := (unary_self_op sun_wd).
Local Notation "'sBin'" := (binary_self_op sbin_wd).
Local Notation "'rsBin'" := (binary_rself_op rsbin_wd).
Local Notation "'Un'" := (unary_op un_wd).
Local Notation "'Bin'" := (binary_op bin_wd).

Theorem equiv_unary_op : ∀ a, Un (to_equiv_type E a) = un a.
    pose proof (eq_reflexive E).
    pose proof (eq_symmetric E).
    pose proof (eq_transitive E).
    intros a.
    unfold unary_op.
    apply un_wd.
    rewrite_ex_val b b_eq.
    cbn in b_eq.
    apply sym.
    apply equiv_eq_class.
    exact b_eq.
Qed.
Theorem equiv_binary_op : ∀ a b,
        Bin (to_equiv_type E a) (to_equiv_type E b) = bin a b.
    pose proof (eq_reflexive E).
    pose proof (eq_symmetric E).
    pose proof (eq_transitive E).
    intros a b.
    unfold binary_op.
    apply bin_wd.
    -   rewrite_ex_val c c_eq.
        apply sym.
        apply equiv_eq_class.
        exact c_eq.
    -   rewrite_ex_val c c_eq.
        apply sym.
        apply equiv_eq_class.
        exact c_eq.
Qed.
Theorem equiv_unary_self_op : ∀ a,
        sUn (to_equiv_type E a) = to_equiv_type E (sun a).
    pose proof (eq_reflexive E).
    pose proof (eq_symmetric E).
    pose proof (eq_transitive E).
    intros a.
    apply set_type_eq.
    apply predicate_ext.
    intros x.
    cbn; unfold unary_self_op_base, to_equiv_type, equiv_class; cbn.
    split.
    -   intros [b [b_in eq]].
        specialize (sun_wd _ _ b_in).
        exact (trans sun_wd eq).
    -   intros eq.
        exists a.
        split.
        +   apply refl.
        +   exact eq.
Qed.
Theorem equiv_binary_self_op : ∀ a b,
        sBin (to_equiv_type E a) (to_equiv_type E b) =
        to_equiv_type E (sbin a b).
    pose proof (eq_reflexive E).
    pose proof (eq_symmetric E).
    pose proof (eq_transitive E).
    intros a b.
    apply set_type_eq.
    apply predicate_ext.
    intros x.
    cbn; unfold binary_self_op_base, to_equiv_type, equiv_class; cbn.
    split.
    -   intros [x1 [x2 [x1_in [x2_in eq]]]].
        specialize (sbin_wd _ _ _ _ x1_in x2_in).
        exact (trans sbin_wd eq).
    -   intros eq.
        exists a, b.
        repeat split; try apply refl.
        exact eq.
Qed.
Theorem equiv_binary_rself_op : ∀ (a : V) (b : U),
        rsBin a (to_equiv_type E b) =
        to_equiv_type E (rsbin a b).
    pose proof (eq_reflexive E).
    pose proof (eq_symmetric E).
    pose proof (eq_transitive E).
    intros a b.
    apply set_type_eq.
    apply predicate_ext.
    intros x.
    cbn; unfold binary_rself_op_base, to_equiv_type, equiv_class; cbn.
    split.
    -   intros [y [y_in eq]].
        specialize (rsbin_wd _ _ a y_in).
        exact (trans rsbin_wd eq).
    -   intros eq.
        exists b.
        split; try apply refl.
        exact eq.
Qed.

End Equivalence.
(* end hide *)
Ltac equiv_get_value_single a := let a' := fresh in let a'_eq := fresh in
    destruct (ex_to_type [|a]) as [a' a'_eq];
    apply equiv_type_eq in a'_eq;
    subst a;
    rename a' into a.
Tactic Notation "equiv_get_value" constr(a) :=
    equiv_get_value_single a.
Tactic Notation "equiv_get_value" constr(a) constr(b) :=
    equiv_get_value a;
    equiv_get_value b.
Tactic Notation "equiv_get_value" constr(a) constr(b) constr(c) :=
    equiv_get_value a b;
    equiv_get_value c.
Tactic Notation "equiv_get_value" constr(a) constr(b) constr(c) constr(d) :=
    equiv_get_value a b c;
    equiv_get_value d.
Tactic Notation "equiv_get_value" constr(a) constr(b) constr(c) constr(d) constr(e) :=
    equiv_get_value a b c d;
    equiv_get_value e.
Tactic Notation "equiv_get_value" constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) :=
    equiv_get_value a b c d e;
    equiv_get_value f.
Ltac equiv_simpl :=
    simpl;
    repeat (rewrite equiv_binary_self_op + rewrite equiv_unary_self_op +
            rewrite equiv_binary_op + rewrite equiv_unary_op +
            rewrite equiv_binary_rself_op);
    repeat rewrite equiv_eq;
    simpl.
Tactic Notation "equiv_simpl" "in" ident(H) :=
    simpl in H;
    repeat (rewrite equiv_binary_self_op in H +
            rewrite equiv_unary_self_op in H +
            rewrite equiv_binary_op in H +
            rewrite equiv_unary_op in H +
            rewrite equiv_binary_rself_op in H);
    repeat rewrite equiv_eq in H;
    simpl in H.
