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
Proof.
    intros a a_cut l u au lu.
    classic_case (l = u).
    -   subst.
        exact au.
    -   apply (land (rand (rand a_cut)) _ _ au).
        split; assumption.
Qed.

Theorem dedekind_lt : ∀ a, dedekind_cut a → ∀ l u, a l → ¬a u → l < u.
Proof.
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
Proof.
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
