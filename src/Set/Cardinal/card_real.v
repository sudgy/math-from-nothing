Require Import init.

Require Import real.
Require Import card.
Require Import card_types.
Require Import set.
Require Import analysis_geometric.
Require Import analysis_topology.
Require Import analysis_order.
Require Import analysis_series.
Require Import order_minmax.
Require Import plus_sum.

(* begin hide *)
Section CardReal.

Existing Instance abs_metric.

Open Scope card_scope.

Lemma real_size_leq1 : |real| ≤ 2 ^ |nat|.
Proof.
    apply arch_ordered_size.
Qed.

Lemma real_size_leq2 : 2 ^ |nat| ≤ |real|.
Proof.
    rewrite <- power_set_size.
Open Scope nat_scope.
Close Scope card_scope.
    unfold le; equiv_simpl.
    pose (F f := λ n, If f n then (/3)^n else 0).
    assert (∀ n, 0 < (/3)^n) as n3_pos.
    {
        nat_induction n.
        -   unfold zero at 2; cbn.
            exact one_pos.
        -   cbn.
            apply lt_mult.
            1: apply IHn.
            apply div_pos.
            exact three_pos.
    }
    assert (∀ f, seq_converges (series (F f))) as F_conv.
    {
        intros f.
        pose (g n := (/3)^n).
        apply (series_le_converge (F f) g).
        -   exists (/(1 - /3)).
            apply geometric_series_sum.
            unfold abs; cbn; case_if.
            +   apply inv_gt_one.
                rewrite <- (plus_rid 1) at 1.
                apply lt_lplus.
                exact two_pos.
            +   apply (trans2 one_pos).
                apply pos_neg2.
                apply div_pos.
                exact three_pos.
        -   intros n.
            unfold F.
            case_if.
            +   apply n3_pos.
            +   apply refl.
        -   intros n.
            unfold F, g; case_if.
            +   apply refl.
            +   apply n3_pos.
    }
    exists (λ f, ex_val (F_conv f)).
    split.
    intros a b eq.
    rewrite_ex_val x a_lim.
    rewrite_ex_val y b_lim.
    subst y.
    apply functional_ext.
    intros n'.
    classic_contradiction neq.
    assert (∃ n, a n ≠ b n) as S_ex by (exists n'; exact neq).
    pose proof (well_ordered _ S_ex) as [n [n_neq n_least]].
    clear n' neq S_ex.
    assert (∀ m, m < n → a m = b m) as ab_eq.
    {
        intros m m_ltq.
        classic_contradiction contr.
        specialize (n_least m contr).
        rewrite <- nle_lt in m_ltq.
        contradiction.
    }
    pose (A := sum (F a) 0 n).
    assert (A = sum (F b) 0 n) as A_eq.
    {
        unfold A.
        clear - ab_eq.
        assert (∀ m, m ≤ n → sum (F a) 0 m = sum (F b) 0 m) as eq.
        {
            nat_induction m.
            -   intros C0; clear C0.
                unfold zero; cbn.
                reflexivity.
            -   intros leq.
                cbn.
                rewrite IHm by exact (trans (nat_le_suc m) leq).
                apply lplus.
                rewrite plus_lid.
                specialize (ab_eq m (lt_le_trans (nat_lt_suc m) leq)).
                unfold F; do 2 case_if.
                +   reflexivity.
                +   rewrite ab_eq in a0.
                    contradiction.
                +   rewrite ab_eq in n0.
                    contradiction.
                +   reflexivity.
        }
        apply eq.
        apply refl.
    }
    pose (f' (f : nat → Prop) := λ n', F f (n + n')).
    assert (seq_lim (λ m, A + series (f' a) m) x) as a'_lim.
    {
        apply (subsequence_lim_eq _ _ _ a_lim).
        exists (λ m, n + m).
        split.
        -   intros n'.
            rewrite nat_plus_rsuc.
            apply nat_lt_suc.
        -   intros m.
            unfold f'.
            unfold series, A.
            nat_induction m.
            +   unfold zero at 5; cbn.
                do 2 rewrite plus_rid.
                reflexivity.
            +   rewrite nat_plus_rsuc.
                cbn.
                rewrite IHm.
                do 2 rewrite plus_lid.
                rewrite plus_assoc.
                reflexivity.
    }
    assert (seq_lim (λ m, A + series (f' b) m) x) as b'_lim.
    {
        apply (subsequence_lim_eq _ _ _ b_lim).
        exists (λ m, n + m).
        split.
        -   intros n'.
            rewrite nat_plus_rsuc.
            apply nat_lt_suc.
        -   intros m.
            unfold f'.
            unfold series.
            rewrite A_eq.
            nat_induction m.
            +   unfold zero at 5; cbn.
                do 2 rewrite plus_rid.
                reflexivity.
            +   rewrite nat_plus_rsuc.
                cbn.
                rewrite IHm.
                do 2 rewrite plus_lid.
                rewrite plus_assoc.
                reflexivity.
    }
    assert (∀ a, seq_converges (series (f' a))) as f'_conv.
    {
        clear - n3_pos.
        intros a.
        apply (series_le_converge _ (f' (λ n, True))).
        -   assert (f' (λ n, True) = (λ m, (/3) ^ n · (/3) ^ m)) as f_eq.
            {
                apply functional_ext.
                intros m.
                unfold f', F.
                case_if.
                -   unfold scalar_mult; cbn.
                    rewrite <- nat_pow_plus.
                    reflexivity.
                -   exfalso; apply n0; exact true.
            }
            rewrite f_eq.
            exists ((/3)^n · / (1 - /3)).
            apply geometric_series_sum_constant.
            apply abs_lt.
            split.
            +   pose proof one_pos as ltq.
                apply pos_neg2 in ltq.
                apply (trans ltq).
                apply div_pos.
                exact three_pos.
            +   apply inv_gt_one.
                rewrite <- (plus_rid 1) at 1.
                apply lt_lplus.
                exact two_pos.
        -   intros m.
            unfold f', F.
            case_if.
            +   apply n3_pos.
            +   apply refl.
        -   intros m.
            unfold f', F.
            do 2 case_if.
            +   apply refl.
            +   exfalso; apply n0; exact true.
            +   apply n3_pos.
            +   apply refl.
    }
    pose proof (f'_conv a) as [ax ax_lim].
    pose proof (f'_conv b) as [bx bx_lim].
    pose proof (constant_seq_lim A) as A_lim.
    pose proof (seq_lim_plus _ _ _ _ A_lim ax_lim) as a'_lim2.
    pose proof (seq_lim_plus _ _ _ _ A_lim bx_lim) as b'_lim2.
    cbn in *.
    pose proof (seq_lim_unique _ _ _ a'_lim a'_lim2) as x_eq1.
    pose proof (seq_lim_unique _ _ _ b'_lim b'_lim2) as x_eq2.
    rewrite x_eq2 in x_eq1.
    apply plus_lcancel in x_eq1.
    clear - n3_pos n_neq x_eq1 ax_lim bx_lim.
    assert (∀ a x, seq_lim (series (f' a)) x → a n → (/3)^n ≤ x) as lim_ge.
    {
        clear - n3_pos.
        intros a x x_lim an.
        apply (seq_lim_ge_constant (λ n, sum (f' a) 0 (nat_suc n))).
        -   intros m.
            nat_induction m.
            +   unfold one at 4; cbn.
                change nat_zero with (zero (U := nat)).
                do 2 rewrite plus_lid.
                unfold f', F.
                rewrite plus_rid.
                case_if.
                *   apply refl.
                *   contradiction.
            +   apply (trans IHm).
                cbn.
                rewrite <- plus_assoc.
                do 2 rewrite plus_lid.
                apply le_lplus.
                rewrite <- (plus_rid (f' a m)) at 1.
                apply le_lplus.
                unfold f', F; case_if.
                *   apply n3_pos.
                *   apply refl.
        -   apply (subsequence_lim_eq _ _ _ x_lim).
            exists (λ m, nat_suc m).
            split.
            +   intros m.
                apply nat_lt_suc.
            +   intros m.
                reflexivity.
    }
    assert (∀ a x, seq_lim (series (f' a)) x → ¬a n →
        x ≤ ((/3)^(n + 1) · /(1 - /3))) as lim_le.
    {
        clear - n3_pos.
        intros a x x_lim an.
        apply (seq_lim_le (series (f' a)) (series (f' (λ m, n < m)))).
        -   intros m.
            nat_induction m.
            +   unfold zero; cbn.
                apply refl.
            +   cbn.
                unfold series in IHm.
                rewrite plus_lid.
                apply le_rplus with (f' a m) in IHm.
                apply (trans IHm).
                apply le_lplus.
                unfold f', F.
                do 2 case_if.
                *   apply refl.
                *   rewrite nlt_le in n0.
                    pose proof (nat_le_self_rplus n m) as n_leq.
                    pose proof (antisym n0 n_leq) as eq.
                    rewrite <- (plus_rid n) in eq at 2.
                    apply plus_lcancel in eq.
                    subst m.
                    rewrite plus_rid in a0.
                    contradiction.
                *   apply n3_pos.
                *   apply refl.
        -   exact x_lim.
        -   apply (seq_lim_part _ 1).
            assert ((λ m, series (f' (λ n', n < n')) (m + 1))
                = series (λ m, (/3)^(n + 1) · (/3)^m)) as f_eq.
            {
                apply functional_ext.
                intros m.
                unfold scalar_mult; cbn.
                nat_induction m.
                -   rewrite plus_lid.
                    unfold one at 1, zero; cbn.
                    do 2 rewrite plus_lid.
                    change nat_zero with (zero (U := nat)).
                    unfold f', F; case_if.
                    +   rewrite plus_rid in s.
                        destruct s; contradiction.
                    +   reflexivity.
                -   rewrite nat_plus_lsuc.
                    cbn.
                    unfold series in IHm.
                    rewrite IHm.
                    apply lplus.
                    do 2 rewrite plus_lid.
                    unfold f', F; case_if.
                    +   rewrite (plus_comm m 1), (plus_assoc n 1 m).
                        rewrite <- nat_pow_plus.
                        reflexivity.
                    +   exfalso; apply n0.
                        rewrite <- (plus_rid n) at 1.
                        apply lt_lplus.
                        rewrite plus_comm.
                        apply nat_pos2.
            }
            rewrite f_eq.
            apply geometric_series_sum_constant.
            unfold abs; cbn; case_if.
            +   apply inv_gt_one.
                rewrite <- (plus_rid 1) at 1.
                apply lt_lplus.
                exact two_pos.
            +   exfalso; apply n0.
                apply div_pos.
                exact three_pos.
    }
    assert ((/3)^n ≤ (/3)^(n + 1) · / (1 - /3)) as leq.
    {
        classic_case (a n) as [an|an].
        -   assert (¬b n) as bn.
            {
                intros bn.
                rewrite (prop_eq_true (a n)) in an.
                rewrite (prop_eq_true (b n)) in bn.
                rewrite an, bn in n_neq.
                contradiction.
            }
            specialize (lim_ge a ax ax_lim an).
            specialize (lim_le b bx bx_lim bn).
            rewrite x_eq1 in lim_le.
            exact (trans lim_ge lim_le).
        -   assert (b n) as bn.
            {
                classic_contradiction bn.
                rewrite (prop_eq_false (a n)) in an.
                rewrite (prop_eq_false (b n)) in bn.
                rewrite an, bn in n_neq.
                contradiction.
            }
            specialize (lim_ge b bx bx_lim bn).
            specialize (lim_le a ax ax_lim an).
            rewrite x_eq1 in lim_ge.
            exact (trans lim_ge lim_le).
    }
    unfold scalar_mult in leq; cbn in leq.
    rewrite (plus_comm n 1) in leq.
    change (1 + n) with (nat_suc n) in leq; cbn in leq.
    rewrite <- (mult_rid ((/3)^n)) in leq at 1.
    rewrite <- mult_assoc in leq.
    apply le_mult_lcancel_pos in leq.
    2: apply n3_pos.
    clear - leq.
    rewrite <- div_mult in leq.
    2: apply three_pos.
    2: {
        intros contr.
        apply rplus with (/3) in contr.
        rewrite plus_rlinv, plus_lid in contr.
        apply rmult with 3 in contr.
        rewrite mult_linv, mult_lid in contr by apply three_pos.
        rewrite <- (plus_rid 1) in contr at 1.
        apply plus_lcancel in contr.
        apply two_pos in contr.
        exact contr.
    }
    rewrite ldist in leq.
    rewrite mult_rid in leq.
    rewrite mult_rneg in leq.
    rewrite mult_rinv in leq by apply three_pos.
    rewrite plus_assoc in leq.
    rewrite plus_rrinv in leq.
    rewrite <- nlt_le in leq.
    apply leq.
    apply inv_gt_one.
    rewrite <- (plus_rid 1) at 1.
    apply lt_lplus.
    exact one_pos.
Qed.

Close Scope nat_scope.
Open Scope card_scope.
(* end hide *)
Theorem real_size : |real| = 2 ^ |nat|.
Proof.
    apply antisym.
    -   exact real_size_leq1.
    -   exact real_size_leq2.
Qed.
(* begin hide *)
End CardReal.

Close Scope card_scope.
(* end hide *)
