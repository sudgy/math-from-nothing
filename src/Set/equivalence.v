Require Import init.

Require Export set_base.
Require Export set_type.

(** To use a quotient, what you need to know is this:
- To define a quotient, make a value of type [equivalence U] (which we'll call
  [E]).  Then the quotient is [equiv_type E].
- To define an operation on a quotient, you need to prove it's well defined and
  then use either [unary_op] or [binary_op].  More complicated functions can be
  built from these as well.  For example, to convert a function [A → B → C] to
  [A → equiv_type B → C], you can use the old "fix an [a : A] and consider it a
  function [B → C]" trick.
- To pick a value from an equivalence class, use the tactic
  [equiv_get_value] on each equivalence class.  (To do it manually, use
  [from_equiv].)
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
Ltac unpack_equiv E :=
    pose proof (eq_reflexive E);
    pose proof (eq_symmetric E);
    pose proof (eq_transitive E).

Section Equivalence.

(** There are a few issues that must be understood before messing with the
details of this implementation of quotients:
- There can be loads of universe consistency issues if you don't define these
  things just right.  This is why [equiv_type] is actually a notation, not a
  definition.
- It is important that the definitions of [unary_op] and [binary_op] are
  completely opaque: If you try to give them their actual definitions, various
  theorems will accidentally look inside the definitions when you don't want to.
  For a concrete example, consider a term of the type [unary_op f_wd (unary_op
  f_wd (to_equiv E a))].  When simplifying, we would want to use unary_op_eq
  twice, once to convert it to [unary_op f_wd (f a)], and the second to convert
  it to [f (f a)].  However, if the unary operation was defined using [to_equiv]
  (as many of them are), then Rocq would see that the term is [unary_op f_wd
  (to_equiv ...)] and would then use the first [unary_op_eq] rewrite to rewrite
  the first instance of [unary_op] rather than the second.  Because of this, the
  definitions of [unary_op] and [binary_op] are opaque.
*)

Context {U} (E : equivalence U).
Local Infix "~" := (eq_equal E).

Definition equiv_class (a : U) := λ x, a ~ x.
Definition equiv_set := λ S, ∃ x, equiv_class x = S.
Local Notation "'equiv_type'" := (set_type equiv_set).

Theorem equiv_ex : ∃ (ι : U → equiv_type),
    (∀ a b, ι a = ι b ↔ a ~ b) ∧
    (∀ A, ∃ a, ι a = A) ∧
    (∀ V (f : U → V),
    (∀ a b, a ~ b → f a = f b) → ∃ f' : equiv_type → V, ∀ x, f' (ι x) = f x).
Proof.
    unpack_equiv E.
    exists (λ x, [equiv_class x | ex_intro _ _ Logic.eq_refl]).
    assert (∀ a b, equiv_class a = equiv_class b → a ~ b) as lem.
    {
        intros a b eq.
        unfold equiv_class in eq.
        pose proof (func_eq _ _ eq) as eq2; cbn in eq2.
        rewrite (eq2 b).
        apply refl.
    }
    split; [>|split].
    -   intros a b.
        rewrite set_type_eq2.
        split; [>apply lem|].
        intros ab.
        apply predicate_ext.
        intros x.
        unfold equiv_class.
        split; intros eq.
        +   apply sym in ab.
            exact (trans ab eq).
        +   exact (trans ab eq).
    -   intros [A [x A_eq]].
        exists x.
        rewrite set_type_eq2.
        exact A_eq.
    -   intros V f f_wd.
        exists (λ (X : set_type equiv_set), f (ex_val [|X])).
        intros x.
        cbn.
        rewrite_ex_val y eq.
        apply f_wd.
        apply lem.
        exact eq.
Qed.

Definition to_equiv := ex_val equiv_ex : U → equiv_type.

Theorem equiv_eq : ∀ a b, (to_equiv a = to_equiv b) ↔ (a ~ b).
Proof.
    apply (ex_proof equiv_ex).
Qed.

Theorem to_equiv_ex : ∀ A, ∃ a, to_equiv a = A.
Proof.
    apply (ex_proof equiv_ex).
Qed.

Theorem unary_op_ex : ∀ V (f : U → V),
    (∀ a b, a ~ b → f a = f b) →
    ∃ f' : equiv_type → V, ∀ x, f' (to_equiv x) = f x.
Proof.
    apply (ex_proof equiv_ex).
Qed.

Definition unary_op {V} {f : U → V} (wd : ∀ a b, a ~ b → f a = f b)
    : equiv_type → V
    := ex_val (unary_op_ex V f wd).

Theorem unary_op_eq : ∀ {V} {f : U → V} {wd : ∀ a b, a ~ b → f a = f b},
    ∀ a, unary_op wd (to_equiv a) = f a.
Proof.
    intros V f wd.
    exact (ex_proof (unary_op_ex V f wd)).
Qed.

Definition from_equiv (A : equiv_type) := ex_val (to_equiv_ex A).

Theorem from_equiv_eq : ∀ A, to_equiv (from_equiv A) = A.
Proof.
    intros A.
    exact (ex_proof (to_equiv_ex A)).
Qed.

Theorem binary_op_ex : ∀ {V} {f : U → U → V}
    (wd : ∀ a b c d, a ~ b → c ~ d → f a c = f b d),
    ∃ f' : equiv_type → equiv_type → V,
    ∀ a b, f' (to_equiv a) (to_equiv b) = f a b.
Proof.
    intros V f f_wd.
    assert (∀ a b c, b ~ c → f a b = f a c) as wd1.
    {
        intros a b c.
        apply f_wd.
        apply eq_reflexive.
    }
    pose (f1 a := unary_op (wd1 a)).
    assert (∀ a b, a ~ b → f1 a = f1 b) as wd2.
    {
        intros a b ab.
        unfold f1.
        apply functional_ext.
        intros C.
        destruct (to_equiv_ex C) as [c C_eq]; subst C.
        do 2 rewrite unary_op_eq.
        apply f_wd.
        -   exact ab.
        -   apply eq_reflexive.
    }
    exists (unary_op wd2).
    intros a b.
    rewrite unary_op_eq.
    unfold f1.
    apply unary_op_eq.
Qed.

Definition binary_op {V} {f : U → U → V}
    (wd : ∀ a b c d, a ~ b → c ~ d → f a c = f b d)
    : equiv_type → equiv_type → V
    := ex_val (binary_op_ex wd).

Theorem binary_op_eq : ∀ {V} {f : U → U → V}
    {wd : ∀ a b c d, a ~ b → c ~ d → f a c = f b d},
    ∀ a b, binary_op wd (to_equiv a) (to_equiv b) = f a b.
Proof.
    intros V f wd.
    exact (ex_proof (binary_op_ex wd)).
Qed.

Theorem unary_self_wd : ∀ {f : U → U},
    (∀ a b, a ~ b → f a ~ f b) →
    ∀ a b, a ~ b → to_equiv (f a) = to_equiv (f b).
Proof.
    intros f f_wd a b ab.
    rewrite equiv_eq.
    apply f_wd; assumption.
Qed.

Theorem binary_self_wd : ∀ {f : U → U → U},
    (∀ a b c d, a ~ b → c ~ d → f a c ~ f b d) →
    ∀ a b c d, a ~ b → c ~ d → to_equiv (f a c) = to_equiv (f b d).
Proof.
    intros f f_wd a b c d ab cd.
    rewrite equiv_eq.
    apply f_wd; assumption.
Qed.

End Equivalence.

Notation "'equiv_type' E" := (set_type (equiv_set E)) (at level 10).
Arguments unary_op {U E V f}.
Arguments to_equiv_ex {U E}.
Arguments from_equiv {U E}.
Arguments equiv_eq {U E}.
Arguments binary_op {U E V f}.
Arguments unary_op_eq {U E V f wd}.
Arguments binary_op_eq {U E V f wd}.
Arguments unary_self_wd {U E f}.
Arguments binary_self_wd {U E f}.

Ltac equiv_get_value_single a := let a' := fresh in let a'_eq := fresh in
    destruct (ex_to_type (to_equiv_ex a)) as [a' a'_eq];
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
    cbn;
    repeat (rewrite binary_op_eq + rewrite unary_op_eq);
    repeat rewrite equiv_eq;
    cbn.
Tactic Notation "equiv_simpl" "in" ident(H) :=
    cbn in H;
    repeat (rewrite binary_op_eq in H + rewrite unary_op_eq in H);
    repeat rewrite equiv_eq in H;
    cbn in H.
