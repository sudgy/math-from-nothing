Require Import init.

Require Import principle_ideal.

Require Import unordered_list.
Require Import nat.
Require Import set.

Class EuclideanDomain (U : IntegralDomain) := {
    euclidean_f : U → nat;
    euclidean_division :
        ∀ a b, 0 ≠ b → ∃ q r, a = b*q + r ∧
            (0 = r ∨ euclidean_f r < euclidean_f b)
}.

Section Euclidean.

Context {U : IntegralDomain} `{EuclideanDomain U}.

Global Instance euclidean_principle_ideal : PrincipleIdealDomain U.
Proof.
    split.
    intros I.
    classic_case (∀ x, cideal_set I x → 0 = x) as [I_z|I_nz].
    {
        exists 0.
        apply cideal_eq.
        intros x.
        split.
        -   intros Ix.
            apply I_z in Ix.
            rewrite <- Ix.
            apply cideal_generated_by_in.
            reflexivity.
        -   intros x_in.
            apply cideal_generated_by_single in x_in as [c x_eq]; subst x.
            rewrite mult_ranni.
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
        split; [>|split].
        1, 2: apply a_nz.
        reflexivity.
    }
    pose proof (well_ordered S S_ex) as [n [[b [b_nz [Ib n_eq]]] n_min]].
    exists b.
    apply cideal_eq.
    intros a.
    rewrite (cideal_generated_by_single b).
    split.
    -   intros Ia.
        pose proof (euclidean_division a b b_nz) as [q [r [eq ltq]]].
        classic_case (0 = r) as [r_z | r_nz].
        +   rewrite <- r_z in eq.
            rewrite plus_rid in eq.
            exists q.
            rewrite mult_comm.
            symmetry; exact eq.
        +   destruct ltq as [|ltq]; [>contradiction|].
            assert (S (euclidean_f r)) as Sr.
            {
                exists r.
                split; [>exact r_nz|].
                split; [>|reflexivity].
                apply plus_rlmove in eq.
                rewrite <- eq.
                apply (cideal_plus I).
                -   apply (cideal_neg I).
                    apply (cideal_mult I).
                    exact Ib.
                -   exact Ia.
            }
            specialize (n_min _ Sr).
            rewrite n_eq in ltq.
            contradiction (irrefl _ (le_lt_trans n_min ltq)).
    -   intros [c eq]; subst a.
        rewrite mult_comm.
        apply (cideal_mult I).
        exact Ib.
Qed.

End Euclidean.
