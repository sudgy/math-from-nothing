Require Import init.

Require Import zorn_real_zorn.

Require Import polynomial_base.
Require Import linear_grade.

Require Import order_self_abs.
Require Import order_minmax.
Require Import mult_pow.
Require Import set.

Section Analysis.

Let PP := polynomial_plus real_cring.
Let PZ := polynomial_zero real_cring.
Let PN := polynomial_neg real_cring.
Let PPC := polynomial_plus_comm real_cring.
Let PPA := polynomial_plus_assoc real_cring.
Let PPZ := polynomial_plus_lid real_cring.
Let PPN := polynomial_plus_linv real_cring.
Let PM := polynomial_mult real_cring.
Let PO := polynomial_one real_cring.
Let PL := polynomial_ldist real_cring.
Let PMA := polynomial_mult_assoc real_cring.
Let PMC := polynomial_mult_comm real_cring.
Let PMO := polynomial_mult_lid real_cring.
Let PSM := polynomial_scalar real_cring.
Let PSMO := polynomial_scalar_id real_cring.
Let PSML := polynomial_scalar_ldist real_cring.
Let PSMR := polynomial_scalar_rdist real_cring.
Let PSMC := polynomial_scalar_comp real_cring.
Let PML := polynomial_scalar_lmult real_cring.
Let PMR := polynomial_scalar_rmult real_cring.
Let PG := polynomial_grade real_cring.

Local Existing Instances PP PZ PN PPC PPA PPZ PPN PM PO PL PMA PMC PMO PSM PSMO
    PSML PSMR PSMC PML PMR PG.

Variable cut : real → Prop.
Hypothesis cut_in : ∃ a, cut a.
Hypothesis cut_out : ∃ a, ¬cut a.
Hypothesis cut_lt : ∀ l u, cut u → l <= u → cut l.

Theorem cut_gt : ∀ l u, ¬cut l → l <= u → ¬cut u.
Proof.
    intros l u l_nin lu u_in.
    apply l_nin.
    exact (cut_lt _ _ u_in lu).
Qed.

Theorem cut_inout : ∀ a b, cut a → ¬cut b → a < b.
Proof.
    intros a b a_in b_nin.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    apply b_nin.
    exact (cut_lt _ _ a_in contr).
Qed.

Let top_of_cut δ x := cut x ∧ ¬cut (x + δ).

Theorem top_of_cut_in : ∀ a b x, a <= b → top_of_cut a x → top_of_cut b x.
Proof.
    intros a b x lt [x_in x_nin].
    split; [>exact x_in|].
    apply le_lplus with x in lt.
    exact (cut_gt _ _ x_nin lt).
Qed.

Notation "| a |" := (abs a) (at level 30).

Lemma polynomial_bounded_xn : ∀ n a b,
    ∃ M, ∀ x, a <= x → x <= b →
    |polynomial_eval (polynomial_xn real_cring n) x| <= M.
Proof.
    intros n a b.
    classic_case (|a| <= |b|) as [leq|leq].
    -   exists (|b|^n)%nat.
        intros x ax xb.
        rewrite polynomial_eval_xn.
        nat_induction n.
        +   do 2 rewrite pow_0_nat.
            rewrite abs_one.
            apply refl.
        +   cbn.
            rewrite abs_mult.
            apply (le_rmult_pos (|x|) (abs_pos _)) in IHn.
            apply (trans IHn).
            apply le_lmult_pos.
            *   clear.
                nat_induction n.
                --  rewrite pow_0_nat.
                    apply one_pos.
                --  cbn.
                    apply le_mult; [>exact IHn|apply abs_pos].
            *   apply abs_le.
                split.
                --  apply le_neg in leq.
                    apply (trans leq).
                    apply (trans2 ax).
                    apply le_neg.
                    rewrite neg_neg.
                    apply abs_le_neg.
                --  apply (trans xb).
                    apply abs_le_pos.
    -   rewrite nle_lt in leq.
        exists (|a|^n)%nat.
        intros x ax xb.
        rewrite polynomial_eval_xn.
        nat_induction n.
        +   do 2 rewrite pow_0_nat.
            rewrite abs_one.
            apply refl.
        +   cbn.
            rewrite abs_mult.
            apply (le_rmult_pos (|x|) (abs_pos _)) in IHn.
            apply (trans IHn).
            apply le_lmult_pos.
            *   clear.
                nat_induction n.
                --  rewrite pow_0_nat.
                    apply one_pos.
                --  cbn.
                    apply le_mult; [>exact IHn|apply abs_pos].
            *   apply abs_le.
                split.
                --  apply (trans2 ax).
                    apply le_neg.
                    rewrite neg_neg.
                    apply abs_le_neg.
                --  apply (le_lt_trans2 leq).
                    apply (trans xb).
                    apply abs_le_pos.
Qed.

Theorem polynomial_bounded : ∀ (f : polynomial real_cring) a b,
    ∃ M, ∀ x, a <= x → x <= b → |polynomial_eval f x| <= M.
Proof.
    intros f a b.
    induction f as [|f f' n fn fn' IHf] using grade_induction.
    {
        exists 0.
        intros x ax xb.
        rewrite polynomial_eval_zero.
        rewrite <- abs_zero.
        apply refl.
    }
    destruct IHf as [M1 M1_max].
    apply polynomial_xn_ex in fn as [α f_eq]; subst f.
    pose proof (polynomial_bounded_xn n a b) as [M2 M2_max].
    exists (M1 + |α| * M2).
    intros x ax xb.
    specialize (M1_max x ax xb).
    specialize (M2_max x ax xb).
    rewrite polynomial_eval_plus.
    rewrite polynomial_eval_scalar.
    apply (trans (abs_tri _ _)).
    rewrite plus_comm.
    apply le_lrplus; [>exact M1_max|].
    rewrite abs_mult.
    apply le_lmult_pos; [>apply abs_pos|].
    exact M2_max.
Qed.

Lemma polynomial_continuous_xn : ∀ n,
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x y, top_of_cut δ x → top_of_cut δ y →
    |(x^n)%nat - (y^n)%nat| < ε.
Proof.
    intros n.
    nat_induction n; intros ε ε_pos.
    {
        exists 1.
        split; [>exact one_pos|].
        intros x y x_in y_in.
        do 2 rewrite pow_0_nat.
        rewrite plus_rinv.
        rewrite <- abs_zero.
        exact ε_pos.
    }
    destruct cut_in as [a a_in].
    destruct cut_out as [b b_in].
    pose (m := max (|a - 1|) (|b|)).
    assert (0 < m) as m_pos.
    {
        unfold m.
        split.
        -   unfold max; case_if; apply abs_pos.
        -   intros contr.
            pose proof (lmax (|a - 1|) (|b|)) as leq1.
            pose proof (rmax (|a - 1|) (|b|)) as leq2.
            rewrite <- contr in leq1, leq2.
            pose proof (antisym (abs_pos _) leq1) as eq1.
            pose proof (antisym (abs_pos _) leq2) as eq2.
            rewrite abs_def in eq1, eq2.
            rewrite eq1 in eq2.
            pose proof (cut_inout _ _ a_in b_in) as ltq.
            rewrite <- eq2 in ltq.
            rewrite <- lt_plus_0_a_b_ba in ltq.
            apply pos_neg2 in ltq.
            rewrite neg_neg in ltq.
            destruct (trans ltq one_pos); contradiction.
    }
    pose proof (div_pos _ m_pos) as m'_pos.
    pose proof (half_pos ε ε_pos) as ε2_pos.
    pose proof (lt_mult _ _ ε2_pos m'_pos) as ε2m_pos.
    specialize (IHn _ ε2m_pos) as [δ1 [δ1_pos IHn]].
    destruct (polynomial_bounded (polynomial_xn real_cring n) (a-1) b) as [M' M'_max].
    pose (M := M' + 1).
    assert (0 < M) as M_pos.
    {
        specialize (M'_max a).
        rewrite polynomial_eval_xn in M'_max.
        prove_parts M'_max.
        {
            rewrite <- le_plus_a_0_ba_b.
            apply pos_neg.
            apply one_pos.
        }
        {
            apply cut_inout; assumption.
        }
        apply le_rplus with 1 in M'_max.
        apply (lt_le_trans2 M'_max).
        apply (lt_le_trans one_pos).
        rewrite <- le_plus_0_a_b_ab.
        apply abs_pos.
    }
    assert (∀ x, a - 1 <= x → x <= b → |(x^n)%nat| < M) as M_max.
    {
        intros x ax xb.
        specialize (M'_max x ax xb).
        rewrite polynomial_eval_xn in M'_max.
        apply (le_lt_trans M'_max).
        unfold M.
        rewrite <- lt_plus_0_a_b_ba.
        exact one_pos.
    }
    clearbody M.
    clear M' M'_max.
    pose (δ := min δ1 (min (ε / 2 / M) 1)).
    assert (0 < δ) as δ_pos.
    {
        unfold δ, min.
        case_if; [>|case_if].
        -   exact δ1_pos.
        -   apply lt_mult.
            +   exact ε2_pos.
            +   apply div_pos.
                exact M_pos.
        -   exact one_pos.
    }
    exists δ.
    split; [>exact δ_pos|].
    intros x y x_in y_in.
    cbn.
    assert (∀ z, top_of_cut δ z → a - 1 < z ∧ z < b) as cut_ab.
    {
        intros z z_in.
        split.
        -   destruct z_in as [z_in z_nin].
            pose proof (cut_inout _ _ a_in z_nin) as ltq.
            assert (δ <= 1) as leq.
            {
                apply (trans (rmin _ _)).
                apply (rmin _ _).
            }
            apply le_lplus with z in leq.
            pose proof (lt_le_trans ltq leq) as ltq2.
            rewrite lt_plus_rrmove in ltq2.
            apply ltq2.
        -   apply cut_inout.
            +   apply z_in.
            +   exact b_in.
    }
    specialize (M_max y (land (land (cut_ab _ y_in)))
                        (land (rand (cut_ab _ y_in)))).
    assert (|x| < m) as x'_lt.
    {
        apply cut_ab in x_in as [x_gt x_lt].
        unfold m.
        unfold abs at 1; case_if.
        -   apply (lt_le_trans2 (rmax _ _)).
            rewrite (abs_pos_eq _ (land (le_lt_trans l x_lt))).
            exact x_lt.
        -   apply (lt_le_trans2 (lmax _ _)).
            rewrite nle_lt in n0.
            rewrite (abs_neg_eq _ (land (trans x_gt n0))).
            apply lt_neg.
            do 2 rewrite neg_neg.
            exact x_gt.
    }
    assert (|x - y| < ε / 2 / M) as xy_lt.
    {
        destruct x_in as [x_in x_nin].
        destruct y_in as [y_in y_nin].
        pose proof (cut_inout _ _ x_in y_nin) as ltq1.
        pose proof (cut_inout _ _ y_in x_nin) as ltq2.
        rewrite lt_plus_rlmove in ltq1, ltq2.
        rewrite plus_comm in ltq1.
        apply lt_neg in ltq2.
        rewrite neg_plus, neg_neg in ltq2.
        apply (lt_le_trans (rand (abs_lt _ _) (make_and ltq2 ltq1))).
        apply (trans (rmin _ _)).
        apply lmin.
    }
    assert (∀ z, top_of_cut δ z → top_of_cut δ1 z) as to_cut_in.
    {
        intros z.
        apply top_of_cut_in.
        apply lmin.
    }
    apply to_cut_in in x_in, y_in.
    specialize (IHn x y x_in y_in).
    rewrite <- (plus_lrinv y x) at 2.
    rewrite ldist.
    rewrite neg_plus.
    rewrite plus_assoc.
    rewrite <- mult_lneg.
    rewrite <- rdist.
    rewrite <- mult_rneg.
    rewrite neg_plus, neg_neg.
    apply (le_lt_trans (abs_tri _ _)).
    do 2 rewrite abs_mult.
    pose proof (lt_lrmult_pos _ _ _ _ (abs_pos _) (abs_pos _) IHn x'_lt)
        as ltq1.
    rewrite (mult_comm _ (|x - y|)).
    pose proof (lt_lrmult_pos _ _ _ _ (abs_pos _) (abs_pos _) xy_lt M_max)
        as ltq2.
    rewrite mult_rlinv in ltq1 by apply m_pos.
    rewrite mult_rlinv in ltq2 by apply M_pos.
    pose proof (lt_lrplus ltq1 ltq2) as ltq.
    rewrite plus_half in ltq.
    exact ltq.
Qed.

Theorem polynomial_continuous : ∀ (f : polynomial real_cring),
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ x y, top_of_cut δ x → top_of_cut δ y →
    |polynomial_eval f x - polynomial_eval f y| < ε.
Proof.
    intros f.
    induction f as [|f f' n fn fn' IHf] using grade_induction.
    {
        intros ε ε_pos.
        exists 1.
        split; [>exact one_pos|].
        intros x y x_in y_in.
        rewrite polynomial_eval_zero.
        rewrite polynomial_eval_zero.
        rewrite neg_zero, plus_rid.
        rewrite <- abs_zero.
        exact ε_pos.
    }
    intros ε ε_pos.
    apply polynomial_xn_ex in fn as [a f_eq]; subst f.
    pose proof (polynomial_continuous_xn n) as xn_lim.
    classic_case (0 = a) as [a_z|a_nz].
    {
        subst a.
        rewrite scalar_lanni.
        rewrite plus_lid.
        exact (IHf ε ε_pos).
    }
    assert (0 < |a|) as a_pos.
    {
        split.
        -   apply abs_pos.
        -   apply abs_nz.
            exact a_nz.
    }
    pose proof (div_pos _ a_pos) as a'_pos.
    pose proof (half_pos ε ε_pos) as ε2_pos.
    pose proof (lt_mult _ _ ε2_pos a'_pos) as ε2a_pos.
    specialize (IHf _ ε2_pos) as [δ1 [δ1_pos IHf]].
    specialize (xn_lim _ ε2a_pos) as [δ2 [δ2_pos xn_lim]].
    exists (min δ1 δ2).
    split; [>unfold min; case_if; assumption|].
    intros x y x_lt y_lt.
    specialize (IHf x y (top_of_cut_in _ _ _ (lmin _ _) x_lt)
                        (top_of_cut_in _ _ _ (lmin _ _) y_lt)).
    specialize (xn_lim x y (top_of_cut_in _ _ _ (rmin _ _) x_lt)
                           (top_of_cut_in _ _ _ (rmin _ _) y_lt)).
    rewrite <- lt_mult_lrmove_pos in xn_lim by exact a_pos.
    rewrite mult_comm in xn_lim.
    pose proof (lt_lrplus xn_lim IHf) as ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans2 ltq).
    do 2 rewrite polynomial_eval_plus.
    do 2 rewrite polynomial_eval_scalar.
    do 2 rewrite polynomial_eval_xn.
    rewrite <- abs_mult.
    rewrite ldist.
    rewrite mult_rneg.
    rewrite neg_plus.
    rewrite plus_assoc.
    rewrite <- (plus_assoc (a * (x^n)%nat)).
    rewrite (plus_comm _ (-(a * (y^n)%nat))).
    rewrite plus_assoc.
    rewrite <- (plus_assoc _ (polynomial_eval _ _)).
    apply abs_tri.
Qed.

End Analysis.
