Require Import init.

Require Export analysis_algebraic.
Require Export analysis_frechet_derivative.
Require Import order_minmax.

Section AnalysisDerivative.

Context {U V1 V2 W} `{
    NormedSpaceClass U,
    NormedSpaceClass V1,
    NormedSpaceClass V2,
    NormedSpaceClass W,
    NotTrivial V1
}.
Lemma V12_not_trivial_ : (not_trivial_a, 0 : V2) ≠ (not_trivial_b, 0).
Proof.
    intro contr; inversion contr as [eq].
    exact (not_trivial eq).
Qed.
Local Instance V12_not_trivial : NotTrivial (V1 * V2) := {
    not_trivial_a := (not_trivial_a, 0);
    not_trivial_b := (not_trivial_b, 0);
    not_trivial := V12_not_trivial_
}.
Existing Instance abs_metric.
Existing Instance ab_plus.
Existing Instance ab_zero.
Existing Instance ab_neg.
Existing Instance ab_scalar.
Existing Instance ab_abs.
Existing Instance ab_plus_assoc.
Existing Instance ab_plus_comm.
Existing Instance ab_plus_lid.
Existing Instance ab_plus_linv.
Existing Instance ab_scalar_comp.
Existing Instance ab_scalar_id.
Existing Instance ab_scalar_ldist.
Existing Instance ab_scalar_rdist.
Existing Instance ab_abs_definite.
Existing Instance ab_abs_pos.
Existing Instance ab_abs_scalar.
Existing Instance ab_abs_tri.

Variable A : bilinear_map V1 V2 W.
Variable A_bounded : bounded_bilinear_map A.

Definition bilinear_d_f (a : V1 * V2) (r : V1 * V2) :=
    A(fst a, snd r) + A(fst r, snd a).

Lemma bilinear_d_f_scalar : ∀ a α v,
    bilinear_d_f a (α · v) = α · bilinear_d_f a v.
Proof.
    intros [a1 a2] α [v1 v2].
    unfold bilinear_d_f; cbn.
    unfold scalar_mult at 1 2; cbn.
    rewrite bilinear_map_lscalar, bilinear_map_rscalar.
    rewrite scalar_ldist.
    reflexivity.
Qed.

Lemma bilinear_d_f_plus : ∀ a u v,
    bilinear_d_f a (u + v) = bilinear_d_f a u + bilinear_d_f a v.
Proof.
    intros [a1 a2] [u1 u2] [v1 v2].
    unfold bilinear_d_f; cbn.
    unfold plus at 2 3; cbn.
    rewrite bilinear_map_lplus, bilinear_map_rplus.
    apply plus_4.
Qed.

Definition bilinear_d (a : V1 * V2) := make_linear_map
    (bilinear_d_f a) (bilinear_d_f_scalar a) (bilinear_d_f_plus a).

Theorem bilinear_d_bounded : ∀ a, bounded_linear_map (bilinear_d a).
Proof.
    intros [a1 a2].
    apply bounded_bilinear_map_pos in A_bounded as [M [M_pos M_bound]].
    exists (M * max (|a1|) (|a2|)).
    cbn.
    unfold bilinear_d_f; cbn.
    intros [x1 x2]; cbn.
    unfold abs at 4; cbn.
    apply (trans (abs_tri _ _)).
    apply (trans (le_lrplus (M_bound _ _) (M_bound _ _))).
    do 2 rewrite <- mult_assoc.
    rewrite <- ldist.
    rewrite (mult_comm (|x1|)).
    pose proof (lmax (|a1|) (|a2|)) as leq1.
    apply (le_rmult_pos (|x2|)) in leq1; [>|apply abs_pos].
    pose proof (rmax (|a1|) (|a2|)) as leq2.
    apply (le_rmult_pos (|x1|)) in leq2; [>|apply abs_pos].
    pose proof (le_lrplus leq1 leq2) as leq.
    rewrite <- ldist in leq.
    rewrite <- mult_assoc.
    apply le_lmult_pos; [>apply M_pos|].
    rewrite (plus_comm (|x1|)).
    exact leq.
Qed.

Theorem frechet_derivative_bilinear : ∀ a,
    frechet_derivative_at [_|all_open] (λ x, A [x|]) a
        [bilinear_d [a|]|bilinear_d_bounded [a|]].
Proof.
    intros [a a_in]; cbn.
    unfold frechet_derivative_at; cbn.
    clear a_in.
    assert (limit_point all a) as a_lim.
    {
        apply norm_open_limit_point.
        -   apply all_open.
        -   exact true.
    }
    split; [>exact a_lim|].
    destruct a as [a1 a2].
    rewrite metric_func_lim.
    intros ε ε_pos.
    cbn.
    unfold bilinear_d_f; cbn.
    unfold neg at 1 4 5 6; cbn.
    unfold plus at 1 6 7 8; cbn.
    apply bounded_bilinear_map_pos in A_bounded as [M [M_pos A_bounded]].
    exists (2*ε/M).
    split.
    {
        apply lt_mult.
        -   apply double_pos.
            exact ε_pos.
        -   apply div_pos.
            exact M_pos.
    }
    intros [[x1 x2] x_in]; cbn.
    clear x_in.
    intros neq ltq.
    unfold abs in ltq; cbn in ltq.
    rewrite neg_zero, plus_rid.
    unfold abs at 3; cbn.
    rewrite bilinear_map_rplus, bilinear_map_rneg.
    rewrite (plus_comm (A(a1, x2))).
    do 2 rewrite neg_plus.
    rewrite neg_neg.
    do 2 rewrite plus_assoc.
    rewrite plus_rlinv.
    rewrite <- bilinear_map_lneg, <- bilinear_map_lplus.
    rewrite <- bilinear_map_rneg, <- bilinear_map_rplus.
    remember (x1 - a1) as r1.
    remember (x2 - a2) as r2.
    assert (0 < |r1| + |r2|) as neq2.
    {
        classic_case (0 = r1) as [r1_z|r1_nz].
        -   rewrite <- r1_z.
            rewrite <- r1_z in Heqr1.
            rewrite plus_0_anb_a_b in Heqr1.
            subst x1.
            rewrite <- abs_zero, plus_lid.
            apply abs_pos2.
            intros contr.
            rewrite <- contr in Heqr2.
            rewrite plus_0_anb_a_b in Heqr2.
            subst x2.
            contradiction.
        -   rewrite <- (plus_lid 0).
            apply lt_le_lrplus.
            +   apply abs_pos2.
                exact r1_nz.
            +   apply abs_pos.
    }
    clear a1 a2 x1 x2 Heqr1 Heqr2 a_lim neq.
    rewrite abs_mult.
    rewrite abs_abs.
    specialize (A_bounded r1 r2).
    apply (lt_rmult_pos (|r1| + |r2|)) in ltq.
    2: assumption.
    rewrite ldist in ltq.
    do 2 rewrite rdist in ltq.
    rewrite <- plus_assoc in ltq.
    rewrite (plus_assoc (|r2| * |r1|)) in ltq.
    rewrite (mult_comm (|r2|) (|r1|)) in ltq.
    rewrite plus_two in ltq.
    pose proof (le_mult (abs_pos r1) (abs_pos r1)) as pos1.
    pose proof (le_mult (abs_pos r2) (abs_pos r2)) as pos2.
    rewrite (le_plus_0_a_b_ab _ (2 * (|r1|*|r2|))) in pos1.
    rewrite (le_plus_0_a_b_ba _ (2 * (|r1|*|r2|))) in pos2.
    apply (le_lplus (|r1| * |r1|)) in pos2.
    pose proof (trans pos1 pos2) as leq.
    pose proof (le_lt_trans leq ltq) as ltq2.
    clear ltq pos1 pos2 leq.
    do 2 rewrite <- mult_assoc in ltq2.
    apply lt_mult_lcancel_pos in ltq2; [>|exact two_pos].
    apply (lt_lmult_pos M) in ltq2; [>|exact M_pos].
    rewrite mult_assoc in ltq2.
    pose proof (le_lt_trans A_bounded ltq2) as ltq.
    do 2 rewrite mult_assoc in ltq.
    rewrite (mult_comm M) in ltq.
    rewrite mult_rrinv in ltq by apply M_pos.
    rewrite lt_mult_rrmove_pos in ltq.
    2: exact neq2.
    rewrite <- abs_div.
    2: apply neq2.
    rewrite abs_pos_eq.
    2: apply neq2.
    exact ltq.
Qed.

Context (O : set_type (open (U := U))).
Context (F1 : set_type [O|] → V1).
Context (F2 : set_type [O|] → V2).
Context (a : set_type [O|]).
Context F1' (F1_dif : frechet_derivative_at O F1 a F1').
Context F2' (F2_dif : frechet_derivative_at O F2 a F2').

Let G (x : set_type [O|]) := A(F1 x, F2 x).
Let G' (x : U) := A(F1 a, [F2'|] x) + A([F1'|] x, F2 a).

Lemma frechet_derivative_product_plus : ∀ u v, G' (u + v) = G' u + G' v.
Proof.
    intros u v.
    unfold G'.
    do 2 rewrite linear_map_plus.
    rewrite bilinear_map_lplus, bilinear_map_rplus.
    apply plus_4.
Qed.

Lemma frechet_derivative_product_scalar : ∀ a v, G' (a · v) = a · G' v.
Proof.
    intros b v.
    unfold G'.
    do 2 rewrite linear_map_scalar.
    rewrite bilinear_map_lscalar, bilinear_map_rscalar.
    rewrite <- scalar_ldist.
    reflexivity.
Qed.

Definition frechet_derivative_product_linear := make_linear_map
    G' frechet_derivative_product_scalar frechet_derivative_product_plus.

Lemma frechet_derivative_product_bounded :
    bounded_linear_map frechet_derivative_product_linear.
Proof.
    unfold bounded_linear_map; cbn.
    unfold G'; clear G'.
    pose proof (bilinear_d_bounded (F1 a, F2 a)) as F_bound.
    pose proof (operator_norm_bound _ F_bound) as M_bound.
    pose proof (operator_norm_pos _ F_bound) as M_pos.
    pose (M := operator_norm _ F_bound).
    fold M in M_bound, M_pos.
    clearbody M.
    clear F_bound.
    cbn in M_bound.
    unfold bilinear_d_f in M_bound; cbn in M_bound.
    pose proof (operator_norm_bound [F1'|] [|F1']) as F1_bound.
    pose proof (operator_norm_bound [F2'|] [|F2']) as F2_bound.
    pose proof (operator_norm_pos [F1'|] [|F1']) as N1_pos.
    pose proof (operator_norm_pos [F2'|] [|F2']) as N2_pos.
    pose (N1 := operator_norm [F1'|] [|F1']).
    pose (N2 := operator_norm [F2'|] [|F2']).
    fold N1 in F1_bound, N1_pos.
    fold N2 in F2_bound, N2_pos.
    clearbody N1 N2.
    exists (M * (N1 + N2)).
    intros x.
    apply (trans (M_bound ([F1'|] x, [F2'|] x))).
    rewrite <- mult_assoc.
    apply le_lmult_pos; [>exact M_pos|].
    unfold abs at 1; cbn.
    rewrite rdist.
    apply le_lrplus.
    -   apply F1_bound.
    -   apply F2_bound.
Qed.

Theorem frechet_derivative_product : frechet_derivative_at O G a
    [_|frechet_derivative_product_bounded].
Proof.
    pose (K x := (F1 x, F2 x)).
    pose (K'_f x := ([F1'|] x, [F2'|] x)).
    assert (∀ u v, K'_f (u + v) = K'_f u + K'_f v) as K'_plus.
    {
        intros u v.
        unfold K'_f.
        do 2 rewrite linear_map_plus.
        unfold plus at 3; cbn.
        reflexivity.
    }
    assert (∀ a v, K'_f (a · v) = a · K'_f v) as K'_scalar.
    {
        intros b v.
        unfold K'_f.
        do 2 rewrite linear_map_scalar.
        unfold scalar_mult at 3; cbn.
        reflexivity.
    }
    pose (K' := make_linear_map K'_f K'_scalar K'_plus).
    assert (bounded_linear_map K') as K'_bound.
    {
        unfold K', bounded_linear_map; cbn.
        unfold K'_f.
        unfold abs at 1; cbn.
        clear - F1' F2'.
        destruct F1' as [F1 [M1 M1_bound]].
        destruct F2' as [F2 [M2 M2_bound]].
        cbn.
        exists (M1 + M2).
        intros x.
        rewrite rdist.
        apply le_lrplus.
        -   apply M1_bound.
        -   apply M2_bound.
    }
    assert (frechet_derivative_at O K a [K'|K'_bound]) as K_dif.
    {
        split; [>apply F1_dif|].
        cbn.
        clear K' K'_bound.
        unfold K, K'_f.
        clear K'_f K'_plus K'_scalar G G' K.
        unfold neg at 1 2; cbn.
        unfold plus at 1 2; cbn.
        unfold abs at 1; cbn.
        destruct F1_dif as [a_lim F1_lim]; clear a_lim.
        destruct F2_dif as [a_lim F2_lim]; clear a_lim.
        pose proof (func_lim_plus _ _ _ _ _ _ F1_lim F2_lim) as lim.
        cbn in lim.
        rewrite plus_lid in lim.
        applys_eq lim.
        apply functional_ext.
        intros x.
        apply rdist.
    }
    pose proof (frechet_derivative_compose O [all|all_open]
        (λ x, A [x|]) (λ x, [K x|true]) _ [K'|K'_bound] a
        (frechet_derivative_bilinear [K a|true]) K_dif) as dif.
    cbn in dif.
    unfold G.
    unfold K in dif.
    applys_eq dif.
    apply set_type_eq; cbn.
    apply linear_map_eq.
    intros x.
    cbn.
    unfold G', bilinear_d_f; cbn.
    reflexivity.
Qed.

End AnalysisDerivative.
