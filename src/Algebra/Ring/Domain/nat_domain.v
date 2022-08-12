Require Import init.

Require Import nat.

Require Import mult_div.
Require Export euclidean_domain.

(* begin hide *)
Lemma nat_euclidean : ∀ a b, 0 ≠ b → ∃ q r, a = b*q + r ∧ (0 = r ∨ r < b).
Proof.
    intros a b b_nz.
    pose (S n := a < b * n).
    assert (∃ n, S n) as S_ex.
    {
        exists (nat_suc a).
        unfold S.
        rewrite nat_mult_rsuc.
        assert (a <= b * a) as eq.
        {
            rewrite <- (mult_lid a) at 1.
            apply nat_le_rmult.
            nat_destruct b; try contradiction.
            unfold one; cbn; rewrite nat_sucs_le.
            apply nat_le_zero.
        }
        assert (0 < b) as b_pos by (split; try assumption; apply nat_le_zero).
        apply le_lplus with b in eq.
        apply lt_rplus with a in b_pos.
        rewrite plus_lid in b_pos.
        exact (lt_le_trans b_pos eq).
    }
    pose proof (nat_wo _ S_ex) as [q [Sq q_min]].
    nat_destruct q.
    {
        unfold S in Sq.
        rewrite mult_ranni in Sq.
        contradiction (nat_lt_zero _ Sq).
    }
    assert (b * q <= a) as leq.
    {
        classic_contradiction contr.
        rewrite nle_lt in contr.
        specialize (q_min _ contr).
        rewrite <- nlt_le in q_min.
        contradiction (q_min (nat_lt_suc q)).
    }
    apply nat_le_ex in leq as [r r_eq].
    exists q, r.
    symmetry in r_eq.
    split.
    -   exact r_eq.
    -   right.
        unfold S in Sq.
        rewrite nat_mult_rsuc in Sq.
        rewrite r_eq in Sq.
        rewrite plus_comm in Sq.
        apply lt_plus_rcancel in Sq.
        exact Sq.
Qed.
(* end hide *)
Global Instance nat_euclidean_class : EuclideanDomain nat := {
    euclidean_f := λ x, x;
    euclidean_division := nat_euclidean
}.

Theorem nat_plus_changes_divides : ∀ p a b,
                                    p ∣ a → ¬(p ∣ b) → ¬(p ∣ (a + b)).
Proof.
    intros p a b [c c_eq] not [d d_eq].
    rewrite <- c_eq in d_eq.
    destruct (trichotomy d c) as [[ltq|eq]|ltq].
    -   apply nat_lt_ex in ltq.
        destruct ltq as [x [x_nz x_eq]].
        rewrite <- x_eq in d_eq.
        rewrite rdist, <- plus_assoc in d_eq.
        rewrite <- (plus_rid (d * p)) in d_eq at 1.
        apply plus_lcancel in d_eq.
        apply nat_plus_zero in d_eq as [eq1 eq2].
        apply mult_zero in eq1 as [x_z|p_z]; try contradiction.
        subst.
        apply not.
        apply refl.
    -   subst.
        rewrite <- (plus_rid (c * p)) in d_eq at 1.
        apply plus_lcancel in d_eq.
        subst.
        apply not.
        apply divides_zero.
    -   apply nat_lt_ex in ltq.
        destruct ltq as [x [x_nz x_eq]].
        rewrite <- x_eq in d_eq.
        rewrite rdist in d_eq.
        apply plus_lcancel in d_eq.
        subst.
        apply not.
        exists x.
        reflexivity.
Qed.

Theorem nat_even_neq_odd : ∀ m n, m * 2 ≠ n * 2 + 1.
Proof.
    intros m n eq.
    assert (even (m * 2)) as m_even by (exists m; reflexivity).
    assert (even (n * 2)) as n_even by (exists n; reflexivity).
    assert (¬2 ∣ (one (U := nat))) as ndiv.
    {
        intros [c c_eq].
        nat_destruct c.
        -   rewrite mult_lanni in c_eq.
            inversion c_eq.
        -   rewrite nat_mult_lsuc in c_eq.
            assert ((one (U := nat)) < 2) as leq.
            {
                split.
                -   unfold one; cbn.
                    unfold plus; cbn.
                    unfold le; cbn.
                    exact true.
                -   intro contr; inversion contr.
            }
            pose proof (nat_le_zero (c * 2)) as leq2.
            apply le_lplus with 2 in leq2.
            rewrite plus_rid in leq2.
            pose proof (lt_le_trans leq leq2) as [C0 C1].
            symmetry in c_eq; contradiction.
    }
    pose proof (nat_plus_changes_divides 2 (n * 2) 1 n_even ndiv).
    rewrite <- eq in H.
    contradiction.
Qed.

Theorem nat_odd_plus_one : ∀ a, odd a → ∃ b, a = 2 * b + 1.
Proof.
    intros a a_odd.
    assert (0 ≠ 2) as two_nz by (intro contr; inversion contr).
    pose proof (euclidean_division a 2 two_nz) as [q [r [eq ltq]]].
    cbn in ltq.
    exists q.
    assert (0 ≠ r) as r_nz.
    {
        intro contr.
        subst.
        rewrite plus_rid in a_odd.
        unfold odd, divides in a_odd.
        rewrite not_ex in a_odd.
        apply (a_odd q).
        apply mult_comm.
    }
    rewrite eq.
    apply lplus.
    apply antisym.
    -   change 2 with (nat_suc 1) in ltq.
        rewrite nat_lt_suc_le in ltq.
        destruct ltq as [r_z|ltq].
        +   contradiction.
        +   exact ltq.
    -   classic_contradiction contr.
        rewrite nle_lt in contr.
        unfold one in contr; cbn in contr.
        rewrite nat_lt_suc_le in contr.
        apply nat_le_zero_eq in contr.
        contradiction.
Qed.

Theorem nat_div_le : ∀ a b, 0 ≠ b → a ∣ b → a <= b.
Proof.
    intros a b b_nz [c c_eq].
    rewrite <- c_eq.
    nat_destruct a.
    -   rewrite mult_ranni.
        apply refl.
    -   rewrite <- (mult_lid (nat_suc a)) at 1.
        apply nat_le_rmult.
        classic_contradiction contr.
        rewrite nle_lt in contr.
        change 1 with (nat_suc 0) in contr.
        rewrite nat_lt_suc_le in contr.
        apply nat_le_zero_eq in contr.
        subst c.
        rewrite mult_lanni in c_eq.
        contradiction.
Qed.
