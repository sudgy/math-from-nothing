Require Import init.

Require Export real_base.
Require Import real_order.
Require Import real_plus.
Require Import real_mult1.
Require Import real_mult2.
Require Import real_mult3.

Require Export nat_abstract.

Require Import set.
Require Import nat.
Require Import int.
Require Import rat.

Definition real_pos := set_type (λ x, 0 < x).

Theorem nat_to_abstract_real : ∀ n, nat_to_abstract n = nat_to_real n.
    nat_induction n.
    -   reflexivity.
    -   cbn.
        rewrite IHn.
        change (nat_suc n) with (1 + n).
        rewrite <- nat_to_real_plus.
        reflexivity.
Qed.

Theorem real_archimedean_base : ∀ x y : real, 0 < x → 0 < y →
        ∃ n, x < n × y.
    intros x y x_pos y_pos.
    classic_contradiction contr.
    rewrite not_ex in contr.
    setoid_rewrite nlt_le in contr.
    pose (A a := ∃ n, a = n × y).
    assert (∃ a, A a) as A_ex.
    {
        exists y.
        exists 1.
        unfold one; cbn.
        rewrite plus_rid.
        reflexivity.
    }
    assert (has_upper_bound le A) as A_upper.
    {
        exists x.
        intros a [n n_eq].
        subst.
        apply contr.
    }
    pose proof (sup_complete A A_ex A_upper) as [α [α_upper α_least]].
    pose proof y_pos as ltq.
    apply pos_neg2 in ltq.
    apply lt_lplus with α in ltq.
    rewrite plus_rid in ltq.
    classic_case (is_upper_bound le A (α - y)) as [up|nup].
    +   specialize (α_least _ up).
        destruct (le_lt_trans α_least ltq); contradiction.
    +   unfold is_upper_bound in nup.
        rewrite not_all in nup.
        destruct nup as [a nup].
        rewrite not_impl, nle_lt in nup.
        destruct nup as [Aa nup].
        destruct Aa as [n eq]; subst a.
        apply lt_plus_lrmove in nup.
        rewrite neg_neg in nup.
        rewrite <- nat_to_abstract_mult in nup.
        rewrite nat_to_abstract_real in nup.
        rewrite <- (mult_lid y) in nup at 2.
        rewrite <- rdist in nup.
        assert (A ((nat_to_real n + 1) * y)) as n_in.
        {
            exists (n + 1).
            rewrite <- nat_to_abstract_mult.
            rewrite nat_to_abstract_real.
            rewrite <- nat_to_real_plus.
            reflexivity.
        }
        specialize (α_upper _ n_in).
        destruct (le_lt_trans α_upper nup); contradiction.
Qed.

Instance real_archimedean : Archimedean real := {
    archimedean := real_archimedean_base
}.

Lemma real_n_pos : ∀ n, 0 < nat_to_real (nat_suc n).
    intros n.
    change 0 with (nat_to_real 0).
    rewrite nat_to_real_lt.
    apply nat_zero_lt_suc.
Qed.
Lemma real_n_div_pos : ∀ n, 0 < / nat_to_real (nat_suc n).
    intros n.
    apply div_pos.
    apply real_n_pos.
Qed.

Theorem real_nested_interval : ∀ I : nat → real → Prop,
        (∀ n, ∃ a b, a <= b ∧ I n = closed_interval a b) →
        (∀ n, I (1 + n) ⊆ I n) →
        ∃ x, ∀ n, I n x.
    intros I I_closed I_sub.
    pose (an n := ex_val (I_closed n)).
    pose (bn n := ex_val (ex_proof (I_closed n))).
    assert (∀ m n, m <= n → I n ⊆ I m) as I_sub2.
    {
        intros m n leq.
        apply nat_le_ex in leq as [c c_eq].
        subst n.
        rewrite plus_comm.
        nat_induction c.
        -   apply refl.
        -   rewrite nat_plus_lsuc.
            exact (trans (I_sub _) IHc).
    }
    assert (∀ m n, an m <= bn n) as abn_leq.
    {
        intros m n.
        unfold an, bn.
        rewrite_ex_val a1 a1H.
        destruct a1H as [b1 [leq1 Im_eq]].
        unfold ex_proof.
        destruct (ex_to_type _) as [a2 C0]; cbn.
        rewrite_ex_val b2 b2H; clear C0.
        destruct b2H as [leq2 In_eq].
        destruct (connex m n) as [leq|leq].
        -   specialize (I_sub2 m n leq).
            rewrite Im_eq, In_eq in I_sub2.
            assert (closed_interval a2 b2 b2) as b2_in.
            {
                split.
                -   exact leq2.
                -   apply refl.
            }
            apply I_sub2 in b2_in.
            apply b2_in.
        -   specialize (I_sub2 n m leq).
            rewrite Im_eq, In_eq in I_sub2.
            assert (closed_interval a1 b1 a1) as a1_in.
            {
                split.
                -   apply refl.
                -   exact leq1.
            }
            apply I_sub2 in a1_in.
            apply a1_in.
    }
    assert (∃ x, ∃ n, an n = x) as S_ex.
    {
        exists (an 0).
        exists 0.
        reflexivity.
    }
    assert (∃ x, ∀ y, (∃ n, an n = y) → y <= x) as S_upper.
    {
        exists (bn 0).
        intros y [n n_eq].
        subst y.
        apply abn_leq.
    }
    pose proof (sup_complete _ S_ex S_upper) as [x [x_upper x_least]].
    exists x.
    intros n.
    pose proof (refl (an n)) as a_eq.
    pose proof (refl (bn n)) as b_eq.
    unfold an in a_eq at 2; unfold bn in b_eq at 2.
    unfold ex_val in a_eq; unfold ex_proof in b_eq.
    destruct (ex_to_type _) as [a C0]; cbn in *.
    rewrite_ex_val b bH; clear C0.
    destruct bH as [leq In_eq].
    rewrite In_eq; clear In_eq.
    split.
    -   apply x_upper.
        exists n.
        exact a_eq.
    -   apply x_least.
        intros am [m am_eq].
        subst am b.
        apply abn_leq.
Qed.

Lemma rat_dense_in_real_pos : ∀ a b : real, 0 <= a → a < b →
        ∃ r : rat, a < rat_to_real r ∧ rat_to_real r < b.
    intros a b a_pos ab.
    apply lt_plus_0_anb_b_a in ab.
    pose proof (archimedean2 _ ab) as [n ltq].
    rewrite nat_to_abstract_real in ltq.
    apply lt_rmult_pos with (nat_to_real (nat_suc n)) in ltq.
    2: apply real_n_pos.
    rewrite mult_linv in ltq by apply real_n_pos.
    remember (nat_to_real (nat_suc n)) as n'.
    rewrite rdist in ltq.
    apply lt_plus_rrmove in ltq.
    rewrite mult_lneg in ltq.
    rewrite neg_neg in ltq.
    pose proof (archimedean1 (a * n')) as [m' m'_ltq].
    rewrite nat_to_abstract_real in m'_ltq.
    assert (∃ m, a * n' < nat_to_real m) as S_ex
        by (exists m'; exact m'_ltq).
    pose proof (well_ordered _ S_ex) as [m [m_ltq m_least]].
    clear m' m'_ltq S_ex.
    remember (nat_to_real m) as m'.
    exists (nat_to_rat m / nat_to_rat (nat_suc n)).
    rewrite <- rat_to_real_mult.
    rewrite <- rat_to_real_div.
    2: {
        change 0 with (nat_to_rat 0).
        intros contr.
        apply nat_to_rat_eq in contr.
        inversion contr.
    }
    change (rat_to_real (nat_to_rat m)) with (nat_to_real m).
    change (rat_to_real (nat_to_rat (nat_suc n)))
        with (nat_to_real (nat_suc n)).
    rewrite <- Heqn', <- Heqm'.
    split.
    -   apply lt_mult_lrmove_pos.
        1: rewrite Heqn'; apply real_n_pos.
        exact m_ltq.
    -   apply lt_mult_rrmove_pos.
        1: rewrite Heqn'; apply real_n_pos.
        nat_destruct m.
        {
            rewrite lt_plus_0_anb_b_a in ab.
            rewrite Heqm'.
            change (nat_to_real 0) with 0.
            apply lt_mult.
            -   exact (le_lt_trans a_pos ab).
            -   rewrite Heqn'.
                apply real_n_pos.
        }
        assert (nat_to_real m <= a * n') as m_ltq2.
        {
            classic_contradiction contr.
            rewrite nle_lt in contr.
            specialize (m_least _ contr).
            rewrite <- nlt_le in m_least.
            contradiction (m_least (nat_lt_suc m)).
        }
        apply (le_lt_trans2 ltq).
        rewrite Heqm'.
        change (nat_suc m) with (1 + m).
        rewrite <- nat_to_real_plus.
        apply le_lplus.
        exact m_ltq2.
Qed.
Theorem rat_dense_in_real : ∀ a b : real, a < b →
        ∃ r : rat, a < rat_to_real r ∧ rat_to_real r < b.
    intros a b ab.
    classic_case (0 <= a) as [a_pos|a_neg].
    {
        apply rat_dense_in_real_pos; assumption.
    }
    rewrite nle_lt in a_neg.
    classic_case (0 < b) as [b_pos|b_neg].
    {
        exists 0.
        split; assumption.
    }
    rewrite nlt_le in b_neg.
    apply neg_pos in b_neg.
    apply lt_neg in ab.
    pose proof (rat_dense_in_real_pos (-b) (-a) b_neg ab) as [r [r_gt r_lt]].
    exists (-r).
    rewrite <- rat_to_real_neg.
    apply lt_neg in r_gt, r_lt.
    rewrite neg_neg in r_gt, r_lt.
    split; assumption.
Qed.
