Require Import init.

Require Export analysis_base.
Require Import analysis_topology.
Require Import analysis_sequence.
Require Export analysis_norm.
Require Import analysis_series.
Require Import mult_pow.
Require Import analysis_order.
Require Import norm_mult.
Require Import plus_sum.

(* begin hide *)
Section GeometricSeries.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    UD : Div U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusRid U UP UZ,
    @PlusLinv U UP UZ UN,
    @PlusRinv U UP UZ UN,
    @MultComm U UM,
    @MultAssoc U UM,
    @Ldist U UP UM,
    @Rdist U UP UM,
    @MultLid U UM UO,
    @MultRid U UM UO,
    @MultLinv U UZ UM UO UD,
    @MultRinv U UZ UM UO UD,
    @NotTrivial U UZ UO,

    SM : ScalarMult real U,
    @ScalarComp real U real_mult_class SM,
    @ScalarId real U real_one SM,
    @ScalarLdist real U UP SM,
    @ScalarRdist real U real_plus_class UP SM,
    @ScalarLMult real U UM SM,
    @ScalarRMult real U UM SM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP,
    @AbsPositive U UA,
    @AbsCauchySchwarz U UA UM,
    @AbsMult U UA UM,
    @AbsScalar U UA SM
}.

Local Open Scope nat_scope.

Existing Instance abs_metric.
(* end hide *)
Theorem geometric_sequence_zero : ∀ r, |r| < 1 → seq_lim (λ n, r ^ n) 0.
    intros r r_small.
    apply seq_lim_zero.
    assert (∀ n, |r^n| <= 1) as r_bound.
    {
        nat_induction n.
        -   unfold zero; cbn.
            rewrite abs_one.
            apply refl.
        -   cbn.
            apply (trans (abs_cs _ _)).
            apply le_rmult_pos with (|r|) in IHn.
            2: apply abs_pos.
            rewrite mult_lid in IHn.
            apply (le_lt_trans IHn r_small).
    }
    assert (seq_converges (λ n, |r^n|)) as [L L_lim].
    {
        apply decreasing_seq_converges.
        -   exists 1.
            intros n.
            rewrite abs_abs.
            apply r_bound.
        -   intros n.
            cbn.
            apply (trans (abs_cs _ _)).
            rewrite <- (mult_rid (|r^n|)) at 2.
            apply le_lmult_pos.
            1: apply abs_pos.
            apply r_small.
    }
    pose (f n := |r ^ (n + n)|).
    assert (subsequence (λ n, |r^n|) f) as f_sub.
    {
        exists (λ n, n + n).
        split.
        -   intros n.
            rewrite nat_plus_lsuc, nat_plus_rsuc.
            apply (trans (nat_lt_suc _)).
            apply nat_lt_suc.
        -   reflexivity.
    }
    pose proof (subsequence_lim_eq _ _ _ L_lim f_sub) as L_lim2.
    pose (g n := |r^n| * |r^n|).
    assert (seq_lim g (L*L)) as L2_lim.
    {
        unfold g.
        apply seq_lim_mult; exact L_lim.
    }
    assert (∀ n, f n <= g n) as fg_leq.
    {
        intros n.
        unfold f, g.
        rewrite <- pow_mult_nat.
        apply abs_cs.
    }
    pose proof (seq_lim_le _ _ _ _ fg_leq L_lim2 L2_lim) as leq.
    assert (0 <= L) as L_pos.
    {
        classic_contradiction contr.
        rewrite nle_lt in contr.
        apply neg_pos2 in contr.
        rewrite metric_seq_lim in L_lim.
        specialize (L_lim _ contr) as [N L_lim].
        specialize (L_lim N (refl _)).
        cbn in L_lim.
        rewrite abs_minus in L_lim.
        unfold abs in L_lim at 1; cbn in L_lim; case_if.
        -   rewrite <- (plus_lid (-L)) in L_lim at 2.
            apply lt_plus_rcancel in L_lim.
            rewrite <- nle_lt in L_lim.
            exfalso; apply L_lim.
            apply abs_pos.
        -   rewrite nle_lt in n.
            rewrite lt_plus_anb_0_a_b in n.
            apply pos_neg2 in contr.
            rewrite neg_neg in contr.
            pose proof (trans n contr) as ltq.
            rewrite <- nle_lt in ltq.
            apply ltq.
            apply abs_pos.
    }
    assert (L < 1) as L_small.
    {
        split.
        -   apply (seq_lim_le_constant (λ n, |r^n|)).
            +   exact r_bound.
            +   exact L_lim.
        -   intros contr; subst.
            apply lt_rplus with (-|r|) in r_small as r1_pos.
            rewrite plus_rinv in r1_pos.
            rewrite metric_seq_lim in L_lim.
            specialize (L_lim _ r1_pos) as [N L_lim].
            specialize (L_lim (nat_suc N) (nat_le_suc N)).
            cbn in L_lim.
            rewrite <- nle_lt in L_lim.
            apply L_lim; clear L_lim.
            nat_induction N.
            +   unfold zero; cbn.
                rewrite mult_lid.
                apply abs_le_pos.
            +   apply (trans IHN).
                cbn.
                apply (trans2 (abs_le_pos _)).
                unfold abs at 1; cbn; case_if.
                *   apply le_lplus.
                    apply le_neg.
                    apply (trans (abs_cs _ _)).
                    destruct r_small as [r_small C0]; clear C0.
                    apply le_lmult_pos with (|r^N * r|) in r_small.
                    2: apply abs_pos.
                    rewrite mult_rid in r_small.
                    exact r_small.
                *   rewrite nle_lt in n.
                    rewrite lt_plus_anb_0_a_b in n.
                    specialize (r_bound (nat_suc N)); cbn in r_bound.
                    clear - n r_bound.
                    destruct (lt_le_trans n r_bound); contradiction.
    }
    classic_case (0 = L) as [L_z|L_nz].
    {
        subst.
        exact L_lim.
    }
    exfalso; clear - leq L_pos L_small L_nz.
    rewrite <- (mult_rid L) in leq at 1.
    apply le_mult_lcancel_pos in leq.
    2: split; assumption.
    destruct (lt_le_trans L_small leq); contradiction.
Qed.

Theorem geometric_series_partial : ∀ r n, r ≠ 1 →
        series (λ n', r ^ n') n = (1 - r^n) / (1 - r).
    intros r n r_neq.
    nat_induction n.
    -   unfold zero; cbn.
        rewrite plus_rinv.
        rewrite mult_lanni.
        reflexivity.
    -   cbn.
        unfold series in IHn.
        rewrite IHn; clear IHn.
        rewrite plus_lid.
        do 2 rewrite rdist.
        rewrite <- plus_assoc.
        apply lplus.
        assert (0 ≠ 1 - r) as neq.
        {
            intros contr.
            apply plus_rrmove in contr.
            rewrite neg_neg, plus_lid in contr.
            contradiction.
        }
        apply mult_rcancel with (1 - r).
        1: exact neq.
        rewrite rdist.
        do 2 rewrite mult_rlinv by exact neq.
        rewrite ldist.
        rewrite mult_rid.
        rewrite plus_llinv.
        rewrite mult_rneg.
        reflexivity.
Qed.

Theorem geometric_series_sum : ∀ r, |r| < 1 →
        seq_lim (series (λ n, r ^ n)) (/(1 - r)).
    intros r r_small.
    assert (series (λ n, (r ^ n)) = (λ n, (1 - r^n) / (1 - r))) as f_eq.
    {
        apply functional_ext.
        intros n.
        rewrite geometric_series_partial.
        -   reflexivity.
        -   intros contr; subst.
            rewrite abs_one in r_small.
            destruct r_small; contradiction.
    }
    rewrite f_eq.
    rewrite <- mult_lid.
    apply seq_lim_mult.
    -   rewrite <- plus_rid.
        apply seq_lim_plus.
        +   apply constant_seq_lim.
        +   rewrite <- neg_zero.
            apply seq_lim_neg.
            apply geometric_sequence_zero.
            exact r_small.
    -   apply constant_seq_lim.
Qed.

Theorem geometric_series_sum_constant : ∀ a r, |r| < 1 →
        seq_lim (series (λ n, a · r ^ n)) (a · / (1 - r)).
    intros a r r_small.
    apply series_scalar.
    apply geometric_series_sum.
    exact r_small.
Qed.
(* begin hide *)
End GeometricSeries.
(* end hide *)
