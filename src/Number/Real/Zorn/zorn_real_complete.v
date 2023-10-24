Require Import init.

Require Import zorn_real_base.
Require Import zorn_real_arch.
Require Import zorn_real_zorn.
Require Import zorn_real_quotient.

Require Import fraction_base.
Require Import fraction_plus.
Require Import fraction_mult.
Require Import fraction_order.
Require Import set.
Require Import polynomial_base.
Require Import ring_ideal.
Require Import nat.

Global Program Instance real_sup_complete : SupremumComplete le (U := real).
Next Obligation.
    rename H into a.
    rename H1 into Sa.
    destruct H0 as [b b_upper].
    pose (cut x := ¬is_upper_bound le S x).
    assert (cut_in : ∃ a, cut a).
    {
        exists (a - 1).
        intros a_upper.
        specialize (a_upper a Sa).
        rewrite <- le_plus_0_a_b_ba in a_upper.
        apply pos_neg in a_upper.
        rewrite neg_neg in a_upper.
        rewrite <- nlt_le in a_upper.
        apply a_upper.
        exact one_pos.
    }
    assert (cut_out : ∃ b, ¬cut b).
    {
        exists (b + 1).
        unfold cut.
        rewrite not_not.
        intros x Sx.
        specialize (b_upper x Sx).
        apply (trans b_upper).
        rewrite <- le_plus_0_a_b_ba.
        apply one_pos.
    }
    assert (cut_lt : ∀ l u, cut u → l ≤ u → cut l).
    {
        intros l u u_cut lu l_upper.
        apply u_cut.
        intros x Sx.
        specialize (l_upper x Sx).
        exact (trans l_upper lu).
    }
    pose (ZP := zorn_real_plus cut cut_in cut_out cut_lt).
    pose (ZPA := zorn_real_plus_assoc cut cut_in cut_out cut_lt).
    pose (ZPC := zorn_real_plus_comm cut cut_in cut_out cut_lt).
    pose (ZZ := zorn_real_zero cut cut_in cut_out cut_lt).
    pose (ZPZ := zorn_real_plus_lid cut cut_in cut_out cut_lt).
    pose (ZN := zorn_real_neg cut cut_in cut_out cut_lt).
    pose (ZPN := zorn_real_plus_linv cut cut_in cut_out cut_lt).
    pose (ZM := zorn_real_mult cut cut_in cut_out cut_lt).
    pose (ZL := zorn_real_ldist cut cut_in cut_out cut_lt).
    pose (ZMA := zorn_real_mult_assoc cut cut_in cut_out cut_lt).
    pose (ZMC := zorn_real_mult_comm cut cut_in cut_out cut_lt).
    pose (ZE := zorn_real_one cut cut_in cut_out cut_lt).
    pose (ZME := zorn_real_mult_lid cut cut_in cut_out cut_lt).
    pose (ZML := zorn_real_mult_lcancel cut cut_in cut_out cut_lt).
    pose (ZO := zorn_real_order cut cut_in cut_out cut_lt).
    pose (ZOC := zorn_real_order_le_connex cut cut_in cut_out cut_lt).
    pose (ZOA := zorn_real_order_le_antisym cut cut_in cut_out cut_lt).
    pose (ZOT := zorn_real_order_le_trans cut cut_in cut_out cut_lt).
    pose (ZOP := zorn_real_order_le_lplus cut cut_in cut_out cut_lt).
    pose (ZOM := zorn_real_order_le_mult cut cut_in cut_out cut_lt).
    pose (ZOML := zorn_real_order_le_mult_lcancel cut cut_in cut_out cut_lt).
    pose (ZT := zorn_real_quotient_not_trivial cut cut_in cut_out cut_lt).
    pose (ZA := zorn_real_quotient_arch cut cut_in cut_out cut_lt).
    pose (zrq := zorn_real_quotient cut cut_in cut_out cut_lt).
    pose (real_ext := frac_type zrq).
    pose (real_ext_not_trivial := frac_not_trivial zrq).
    pose (real_ext_plus := frac_plus zrq).
    pose (real_ext_plus_comm := frac_plus_comm zrq).
    pose (real_ext_plus_assoc := frac_plus_assoc zrq).
    pose (real_ext_zero := frac_zero zrq).
    pose (real_ext_plus_lid := frac_plus_lid zrq).
    pose (real_ext_neg := frac_neg zrq).
    pose (real_ext_plus_linv := frac_plus_linv zrq).
    pose (real_ext_mult := frac_mult zrq).
    pose (real_ext_mult_comm := frac_mult_comm zrq).
    pose (real_ext_mult_assoc := frac_mult_assoc zrq).
    pose (real_ext_ldist := frac_ldist zrq).
    pose (real_ext_one := frac_one zrq).
    pose (real_ext_mult_lid := frac_mult_lid zrq).
    pose (real_ext_div := frac_div zrq).
    pose (real_ext_mult_linv := frac_mult_linv zrq).
    pose (real_ext_order := frac_order zrq).
    pose (real_ext_le_connex := frac_le_connex zrq).
    pose (real_ext_le_antisym := frac_le_antisym zrq).
    pose (real_ext_le_trans := frac_le_trans zrq).
    pose (real_ext_le_lplus := frac_le_lplus zrq).
    pose (real_ext_le_mult := frac_le_mult zrq).
    pose (real_ext_arch := frac_arch zrq).
    pose (real_ext_aof := aof_ex real_ext).
    pose (to_real_ext_plus := to_frac_plus zrq).
    pose (to_real_ext_mult := to_frac_mult zrq).
    pose (to_real_ext_one := to_frac_one zrq).
    pose (to_real_ext_le := to_frac_le zrq).
    pose (to_real_ext_inj := to_frac_inj zrq).
    pose (PL := polynomial_ldist real_cring).
    pose proof (real_maximal real_ext_aof) as f_ex.
    cbn in f_ex.
    change (set_type (aof_set real_aof)) with real in f_ex.
    pose (f1 (x : real) := to_polynomial real_cring x).
    pose (f2 (x : polynomial real_cring) := to_qring
                    (zorn_real_ideal cut cut_in cut_out cut_lt) x : zrq).
    pose (f3 (x : zrq) := to_frac zrq x).
    pose (f4 (x : frac_type zrq) := aof_ex_f x).
    pose (f x := f4 (f3 (f2 (f1 x)))).
    assert (arch_ordered_homo real_aof real_ext_aof f) as f_homo.
    {
        unfold f, f1, f2, f3, f4.
        split; [>|split; [>|split; [>|split]]].
        -   rewrite to_polynomial_zero.
            rewrite to_qring_zero.
            rewrite (homo_zero (f := to_frac zrq)).
            reflexivity.
        -   rewrite to_polynomial_one.
            rewrite to_qring_one.
            rewrite (homo_one (f := to_frac zrq)).
            reflexivity.
        -   intros x y.
            rewrite to_polynomial_plus.
            rewrite to_qring_plus.
            rewrite (homo_plus (f := to_frac zrq)).
            unfold plus at 2; cbn.
            do 2 rewrite aof_ex_f_eq1.
            reflexivity.
        -   intros x y.
            rewrite to_polynomial_mult.
            rewrite to_qring_mult.
            rewrite (homo_mult (f := to_frac zrq)).
            unfold mult at 2; cbn.
            do 2 rewrite aof_ex_f_eq1.
            reflexivity.
        -   intros x y xy.
            unfold le; cbn.
            do 2 rewrite aof_ex_f_eq1.
            rewrite <- homo_le2.
            apply (land (zorn_real_quotient_le _ _ _ _ _ _)).
            apply zorn_real_q_le_to_poly.
            exact xy.
    }
    prove_parts f_ex.
    {
        exists f.
        exact f_homo.
    }
    destruct f_ex as [f5 f5_homo].
    assert (∀ x, x = f5 (f x)) as f_eq.
    {
        intros x.
        assert ((λ x, f5 (f x)) = identity) as f_eq.
        {
            apply arch_ordered_homo_identity.
            apply (arch_ordered_homo_compose real_aof real_ext_aof real_aof).
            -   exact f_homo.
            -   exact f5_homo.
        }
        change x with (identity x) at 1.
        rewrite <- f_eq.
        reflexivity.
    }
    pose (α := f5 (f4 (f3 (f2 (polynomial_x real_cring))))).
    exists α.
    assert (∀ x y, zorn_real_q_le cut cut_in cut_out cut_lt x y →
        f5 (f4 (f3 (f2 x))) ≤ f5 (f4 (f3 (f2 y)))) as f_le.
    {
        intros x y xy.
        rewrite <- (arch_ordered_homo_le _ _ _ f5_homo).
        unfold f4, le; cbn.
        do 2 rewrite aof_ex_f_eq1.
        unfold f3.
        rewrite <- homo_le2.
        apply (land (zorn_real_quotient_le _ _ _ _ _ _)).
        exact xy.
    }
    assert (∀ x, ¬is_upper_bound le S x → x ≤ α) as α_ge.
    {
        intros x x_nupper.
        unfold α.
        rewrite (f_eq x).
        apply f_le.
        apply zorn_real_q_le_in.
        exact x_nupper.
    }
    assert (∀ x, is_upper_bound le S x → α ≤ x) as α_le.
    {
        intros x x_upper.
        unfold α.
        rewrite (f_eq x).
        apply f_le.
        apply zorn_real_q_le_out.
        unfold cut.
        rewrite not_not.
        exact x_upper.
    }
    split.
    -   intros x Sx.
        classic_case (is_upper_bound le S x) as [x_upper|x_nupper].
        2: exact (α_ge _ x_nupper).
        classic_contradiction ltq.
        specialize (α_ge ((x + α) / 2)).
        prove_parts α_ge.
        {
            intros upper.
            specialize (upper x Sx).
            rewrite rdist in upper.
            rewrite le_plus_rlmove in upper.
            rewrite <- (plus_half x) in upper at 2.
            rewrite plus_llinv in upper.
            apply le_mult_rcancel_pos in upper.
            2: apply div_pos; exact two_pos.
            contradiction.
        }
        rewrite rdist in α_ge.
        rewrite le_plus_lrmove in α_ge.
        rewrite <- (plus_half α) in α_ge at 1.
        rewrite plus_rrinv in α_ge.
        apply le_mult_rcancel_pos in α_ge.
        2: apply div_pos; exact two_pos.
        contradiction.
    -   intros y y_upper.
        apply α_le.
        exact y_upper.
Qed.
