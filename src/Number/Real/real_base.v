Require Import init.

Require Import rat.
Require Import set.

Declare Scope real_scope.
Delimit Scope real_scope with real.

Definition dedekind_cut (a : rat → Prop) :=
    a ≠ all ∧
    a ≠ empty ∧
    (∀ l u, a u → l < u → a l) ∧
    (∀ l, a l → ∃ u, a u ∧ l < u).

Theorem dedekind_le : ∀ a, dedekind_cut a → ∀ l u, a u → l <= u → a l.
    intros a a_cut l u au lu.
    classic_case (l = u).
    -   subst.
        exact au.
    -   apply (land (rand (rand a_cut)) _ _ au).
        split; assumption.
Qed.

Theorem dedekind_lt : ∀ a, dedekind_cut a → ∀ l u, a l → ¬a u → l < u.
    intros a a_cut l u al nau.
    classic_case (l = u) as [eq|neq]; try (subst; contradiction).
    classic_contradiction leq.
    rewrite nlt_le in leq.
    rewrite neq_sym in neq.
    apply nau.
    apply (land (rand (rand a_cut)) u l); try split; assumption.
Qed.

Notation "'real'" := (set_type dedekind_cut).

Definition rat_to_real_base (a b : rat) := b < a.
Lemma rat_to_real_cut : ∀ a, dedekind_cut (rat_to_real_base a).
    intros a.
    unfold rat_to_real_base.
    split.
    2: split.
    3: split.
    -   intros eq.
        assert (all a) as contr by exact true.
        rewrite <- eq in contr.
        destruct contr; contradiction.
    -   apply ex_not_empty.
        exists (a + -(1)).
        rewrite <- (plus_rid a) at 2.
        apply lt_lplus.
        apply pos_neg2.
        exact one_pos.
    -   intros l u ltq1 ltq2.
        exact (trans ltq2 ltq1).
    -   intros l ltq.
        exists ((l + a) * div 2).
        split.
        +   apply lt_mult_rcancel_pos with 2; try exact two_pos.
            rewrite mult_rlinv by apply two_pos.
            rewrite ldist.
            rewrite mult_rid.
            apply lt_rplus.
            exact ltq.
        +   apply lt_mult_rcancel_pos with 2; try exact two_pos.
            rewrite mult_rlinv by apply two_pos.
            rewrite ldist.
            rewrite mult_rid.
            apply lt_lplus.
            exact ltq.
Qed.

Definition rat_to_real a := [_|rat_to_real_cut a].
Definition int_to_real a := rat_to_real (int_to_rat a).
Definition nat0_to_real a := rat_to_real (nat0_to_rat a).

Theorem rat_to_real_eq : ∀ a b, rat_to_real a = rat_to_real b → a = b.
    intros a b eq.
    inversion eq as [eq2].
    unfold rat_to_real_base in eq2.
    pose proof (func_eq _ _ eq2) as eq3; cbn in eq3.
    destruct (trichotomy a b) as [[ab|ab]|ab]; try exact ab.
    -   rewrite <- eq3 in ab.
        destruct ab; contradiction.
    -   rewrite eq3 in ab.
        destruct ab; contradiction.
Qed.

Theorem int_to_real_eq : ∀ a b, int_to_real a = int_to_real b → a = b.
    intros a b eq.
    apply int_to_rat_eq.
    apply rat_to_real_eq.
    exact eq.
Qed.

Theorem nat0_to_real_eq : ∀ a b, nat0_to_real a = nat0_to_real b → a = b.
    intros a b eq.
    apply nat0_to_rat_eq.
    apply rat_to_real_eq.
    exact eq.
Qed.
