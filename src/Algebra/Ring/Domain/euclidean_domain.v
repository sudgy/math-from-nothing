Require Import init.

Require Import principle_ideal.

Require Import unordered_list.
Require Import nat.
Require Import set.

#[universes(template)]
Class EuclideanDomain U `{Plus U} `{Zero U} `{Mult U} := {
    euclidean_f : U → nat;
    euclidean_division :
        ∀ a b, 0 ≠ b → ∃ q r, a = b*q + r ∧
            (0 = r ∨ euclidean_f r < euclidean_f b)
}.

Section Euclidean.

Context {U : IntegralDomain} `{@EuclideanDomain U _ _ _}.

Program Instance euclidean_principle_ideal : @PrincipleIdealDomain U. 
Next Obligation.
    classic_case (∀ x, cideal_set I x → 0 = x) as [I_z|I_nz].
    {
        exists 0.
        apply cideal_eq.
        intros x.
        split.
        -   intros Ix.
            apply I_z in Ix.
            rewrite <- Ix.
            apply (cideal_zero (principle_ideal_by 0)).
        -   intros [l x_eq].
            assert (0 = x) as x_z.
            {
                rewrite x_eq.
                clear x_eq.
                induction l using ulist_induction.
                -   rewrite ulist_image_end, ulist_sum_end.
                    reflexivity.
                -   rewrite ulist_image_add, ulist_sum_add.
                    rewrite <- IHl.
                    rewrite plus_rid.
                    destruct a as [a1 [a2 a2_eq]].
                    unfold list_to_set in a2_eq.
                    rewrite <- a2_eq; cbn.
                    rewrite mult_lanni.
                    reflexivity.
            }
            rewrite <- x_z.
            apply (cideal_zero I).
    }
    pose (S n := ∃ a, 0 ≠ a ∧ cideal_set I a ∧ euclidean_f a = n).
    assert (∃ n, S n) as S_ex.
    {
        rewrite not_all in I_nz.
        destruct I_nz as [a a_nz].
        rewrite not_impl in a_nz.
        exists (euclidean_f a).
        exists a.
        repeat split; apply a_nz.
    }
    pose proof (well_ordered S S_ex) as [n [[b [b_nz [Ib n_eq]]] n_min]].
    exists b.
    apply cideal_eq.
    intros a.
    split.
    -   intros Ia.
        cbn.
        unfold cideal_generated_by_set.
        pose proof (euclidean_division a b b_nz) as [q [r [eq ltq]]].
        classic_case (0 = r) as [r_z | r_nz].
        +   rewrite <- r_z in eq.
            rewrite plus_rid in eq.
            exists ((q, [b|Logic.eq_refl]) ː ulist_end).
            rewrite ulist_image_add, ulist_sum_add; cbn.
            rewrite ulist_image_end, ulist_sum_end.
            rewrite plus_rid.
            exact eq.
        +   destruct ltq as [|ltq]; [>contradiction|].
            assert (S (euclidean_f r)) as Sr.
            {
                exists r.
                repeat split.
                -   exact r_nz.
                -   apply plus_rlmove in eq.
                    rewrite <- eq.
                    apply (cideal_plus I).
                    +   apply (cideal_neg I).
                        apply (cideal_mult I).
                        exact Ib.
                    +   exact Ia.
            }
            specialize (n_min _ Sr).
            rewrite n_eq in ltq.
            destruct (le_lt_trans n_min ltq); contradiction.
    -   intros [l a_eq].
        rewrite a_eq; clear a_eq.
        induction l as [|c l] using ulist_induction.
        +   rewrite ulist_image_end, ulist_sum_end.
            apply (cideal_zero I).
        +   rewrite ulist_image_add, ulist_sum_add.
            apply (cideal_plus I); [>clear IHl|exact IHl].
            destruct c as [c1 [c2 c2_eq]]; cbn.
            rewrite singleton_eq in c2_eq.
            rewrite <- c2_eq.
            apply (cideal_mult I).
            exact Ib.
Qed.

End Euclidean.
