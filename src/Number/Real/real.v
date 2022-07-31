Require Import init.

Require Export dedekind_real.

Require Export order_plus.
Require Export order_mult.

Require Export nat_abstract.
Require Export int_abstract.
Require Import rat_abstract.
Require Import fraction_base.

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
        rewrite nat_to_real_plus.
        reflexivity.
Qed.

Theorem int_to_abstract_real : ∀ n, int_to_abstract n = int_to_real n.
    intros n.
    equiv_get_value n.
    unfold int_to_abstract.
    rewrite equiv_unary_op.
    unfold int_to_abstract_base.
    do 2 rewrite nat_to_abstract_real.
    unfold nat_to_real, nat_to_rat.
    change (rat_to_real (int_to_rat (nat_to_int (fst n)))) with
        (int_to_real (nat_to_int (fst n))).
    change (rat_to_real (int_to_rat (nat_to_int (snd n)))) with
        (int_to_real (nat_to_int (snd n))).
    rewrite <- int_to_real_neg.
    rewrite <- int_to_real_plus.
    apply f_equal.
    unfold plus, neg, nat_to_int; equiv_simpl.
    rewrite plus_rid, plus_lid.
    reflexivity.
Qed.

Theorem rat_to_abstract_real : ∀ n, rat_to_abstract n = rat_to_real n.
    intros n.
    equiv_get_value n.
    unfold rat_to_abstract.
    rewrite equiv_unary_op.
    unfold rat_to_abstract_base.
    do 2 rewrite int_to_abstract_real.
    unfold int_to_real.
    rewrite <- rat_to_real_div.
    2: {
        intros contr.
        change (zero (U := rat)) with (int_to_rat 0) in contr.
        apply int_to_rat_eq in contr.
        apply [|snd n].
        exact contr.
    }
    rewrite <- rat_to_real_mult.
    apply f_equal.
    unfold mult, div; equiv_simpl.
    pose proof [|snd n].
    destruct (strong_excluded_middle (0 = [snd n|])) as [contr|x_nz];
        [>contradiction|]; cbn.
    unfold rat; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite mult_rid, mult_lid.
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
        rewrite <- nat_to_abstract_mult_abstract in nup.
        rewrite nat_to_abstract_real in nup.
        rewrite <- (mult_lid y) in nup at 2.
        rewrite <- rdist in nup.
        assert (A ((nat_to_real n + 1) * y)) as n_in.
        {
            exists (n + 1).
            rewrite <- nat_to_abstract_mult_abstract.
            rewrite nat_to_abstract_real.
            rewrite nat_to_real_plus.
            reflexivity.
        }
        specialize (α_upper _ n_in).
        destruct (le_lt_trans α_upper nup); contradiction.
Qed.

Global Instance real_archimedean : Archimedean real := {
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
    pose proof (Logic.eq_refl (an n)) as a_eq.
    pose proof (Logic.eq_refl (bn n)) as b_eq.
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

Theorem rat_dense_in_real : ∀ a b : real, a < b →
        ∃ r : rat, a < rat_to_real r ∧ rat_to_real r < b.
    intros a b ltq.
    pose proof (rat_dense_in_arch a b ltq) as [r r'].
    exists r.
    rewrite <- rat_to_abstract_real.
    exact r'.
Qed.
