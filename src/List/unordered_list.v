Require Import init.

Require Export unordered_list_base.
Require Export unordered_list_nat.
Require Export unordered_list_in.
Require Export unordered_list_set.
Require Export unordered_list_fold.

Require Import set.

Theorem ulist_finite : ∀ {U : Type}, simple_finite U →
    ∃ l : ulist U, ulist_unique l ∧ ∀ x, in_ulist l x.
Proof.
    intros U U_fin.
    apply simple_finite_bij in U_fin as [n [f f_bij]].
    revert U f f_bij.
    nat_induction n; intros.
    {
        exists ⟦⟧.
        split.
        -   apply ulist_unique_end.
        -   intros x.
            contradiction (nat_lt_0_false (f x)).
    }
    assert (initial_segment (nat_suc n) n) as n_lt by (apply nat_lt_suc).
    pose proof (sur f [n|n_lt]) as [x x_eq].
    pose (U' := set_type (λ a, a ≠ x)).
    assert (∀ a : U', initial_segment n [f [a|]|]) as a_in.
    {
        intros a.
        unfold initial_segment.
        split.
        -   rewrite <- nat_lt_suc_le.
            apply [|f _].
        -   intros contr.
            apply set_type_eq in x_eq; cbn in x_eq.
            rewrite <- contr in x_eq.
            rewrite set_type_eq in x_eq.
            apply inj in x_eq.
            symmetry in x_eq.
            contradiction ([|a] x_eq).
    }
    specialize (IHn U' (λ a, [_|a_in a])).
    prove_parts IHn.
    {
        split; split.
        -   intros a b eq.
            apply set_type_eq in eq; cbn in eq.
            rewrite set_type_eq in eq.
            apply inj in eq.
            rewrite set_type_eq in eq.
            exact eq.
        -   intros [y y_lt].
            unfold initial_segment in y_lt.
            assert (initial_segment (nat_suc n) y) as y_lt'
                by (exact (trans y_lt (nat_lt_suc n))).
            pose proof (sur f [_|y_lt']) as [a a_eq].
            assert (a ≠ x) as neq.
            {
                intros contr; subst a.
                rewrite a_eq in x_eq.
                apply set_type_eq in x_eq; cbn in x_eq.
                subst; contradiction (irrefl _ y_lt).
            }
            exists [a|neq].
            cbn.
            apply set_type_eq; cbn.
            rewrite a_eq; reflexivity.
    }
    destruct IHn as [l [l_uni l_eq]].
    exists (x ː ulist_image set_value l).
    split.
    -   rewrite ulist_unique_add.
        split.
        +   intros x_in.
            apply image_in_ulist in x_in as [x' [x'_eq x'_in]].
            pose proof [|x'] as neq.
            cbn in neq.
            contradiction.
        +   apply ulist_image_unique_inj.
            *   apply set_type_inj.
            *   exact l_uni.
    -   intros y.
        classic_case (x = y) as [eq|neq].
        +   subst.
            apply in_ulist_add.
        +   rewrite in_ulist_add_eq.
            right.
            rewrite neq_sym in neq.
            specialize (l_eq [y|neq]).
            apply (in_ulist_image set_value) in l_eq.
            exact l_eq.
Qed.
