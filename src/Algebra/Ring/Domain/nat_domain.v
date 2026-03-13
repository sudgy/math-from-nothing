Require Import init.

Require Export nat.

Require Export mult_div.

Theorem nat_euclidean :
    ∀ a b : nat, 0 ≠ b → ∃ q r, a = b*q + r ∧ r < b.
Proof.
    intros a b b_nz.
    pose (S n := a < b * nat_suc n).
    assert (∃ n, S n) as S_ex.
    {
        exists a.
        unfold S.
        rewrite nat_mult_rsuc.
        pose proof (nat_le_self_lmult a b b_nz) as eq.
        assert (0 < b) as b_pos by (split; try assumption; apply nat_pos).
        pose proof (le_lt_lrplus eq b_pos) as ltq.
        rewrite plus_rid in ltq.
        rewrite plus_comm.
        exact ltq.
    }
    pose proof (well_ordered _ S_ex) as [q [Sq q_min]].
    assert (b * q ≤ a) as leq.
    {
        classic_contradiction contr.
        rewrite nle_lt in contr.
        nat_destruct q.
        -   rewrite mult_ranni in contr.
            contradiction (not_neg contr).
        -   specialize (q_min _ contr).
            rewrite <- nlt_le in q_min.
            contradiction (q_min (nat_lt_suc q)).
    }
    apply nat_le_ex in leq as [r r_eq].
    exists q, r.
    symmetry in r_eq.
    split; [>exact r_eq|].
    unfold S in Sq.
    rewrite nat_mult_rsuc in Sq.
    rewrite r_eq in Sq.
    rewrite plus_comm in Sq.
    apply lt_plus_rcancel in Sq.
    exact Sq.
Qed.

Theorem nat_plus_changes_divides : ∀ p a b : nat,
                                    p ∣ a → ¬(p ∣ b) → ¬(p ∣ (a + b)).
Proof.
    intros p a b [c c_eq] not [d d_eq].
    subst a.
    destruct (connex d c) as [leq|leq].
    -   apply nat_le_ex in leq as [x x_eq]; subst c.
        rewrite rdist, <- plus_assoc in d_eq.
        rewrite <- (plus_rid (d * p)) in d_eq at 1.
        apply plus_lcancel in d_eq.
        apply nat_plus_zero in d_eq as [eq1 eq2].
        subst b.
        contradiction (not (divides_zero p)).
    -   apply nat_le_ex in leq as [x x_eq]; subst d.
        rewrite rdist in d_eq.
        apply plus_lcancel in d_eq.
        subst.
        contradiction (not (mult_div_rself _ _)).
Qed.

Theorem nat_even_neq_odd : ∀ m n : nat, m * 2 ≠ n * 2 + 1.
Proof.
    intros m n eq.
    assert (even (m * 2)) as m_even by (exists m; reflexivity).
    assert (even (n * 2)) as n_even by (exists n; reflexivity).
    assert (¬2 ∣ (1 : nat)) as ndiv.
    {
        intros [c c_eq].
        nat_destruct c.
        -   rewrite mult_lanni in c_eq.
            contradiction (not_trivial_one c_eq).
        -   rewrite nat_mult_lsuc in c_eq.
            do 2 rewrite nat_plus_lsuc in c_eq.
            change 1 with (nat_suc 0) in c_eq at 3.
            rewrite nat_suc_eq in c_eq.
            symmetry in c_eq; contradiction (nat_zero_suc c_eq).
    }
    pose proof (nat_plus_changes_divides 2 (n * 2) 1 n_even ndiv).
    rewrite <- eq in H.
    contradiction.
Qed.

Theorem nat_odd_plus_one : ∀ a : nat, odd a → ∃ b, a = 2 * b + 1.
Proof.
    intros a a_odd.
    assert ((0 : nat) ≠ 2) as two_nz by apply nat_zero_suc.
    pose proof (nat_euclidean a 2 two_nz) as [q [r [eq ltq]]].
    exists q.
    nat_destruct r.
    -   rewrite plus_rid in eq.
        exfalso; apply a_odd.
        rewrite eq.
        apply mult_div_lself.
    -   nat_destruct r; [>exact eq|].
        change 2 with (nat_suc (nat_suc 0)) in ltq.
        do 2 rewrite nat_sucs_lt in ltq.
        contradiction (not_neg ltq).
Qed.

Theorem nat_div_le : ∀ a b : nat, 0 ≠ b → a ∣ b → a ≤ b.
Proof.
    intros a b b_nz [c c_eq].
    rewrite <- c_eq.
    apply nat_le_self_lmult.
    intros contr; subst.
    rewrite mult_lanni in b_nz.
    contradiction.
Qed.

Theorem nat_unit : ∀ a : nat, unit a → a = 1.
Proof.
    intros a [b eq].
    nat_destruct a.
    1: rewrite mult_ranni in eq; contradiction (nat_zero_suc eq).
    nat_destruct a.
    1: reflexivity.
    nat_destruct b.
    1: rewrite mult_lanni in eq; contradiction (nat_zero_suc eq).
    rewrite nat_mult_lsuc in eq.
    do 2 rewrite nat_plus_lsuc in eq.
    change 1 with (nat_suc 0) in eq.
    rewrite nat_suc_eq in eq.
    symmetry in eq; contradiction (nat_zero_suc eq).
Qed.
