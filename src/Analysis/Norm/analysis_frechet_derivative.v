Require Import init.

Require Import set.
Require Import order_minmax.

Require Export analysis_norm.
Require Import analysis_linear.
Require Import analysis_topology.
Require Import analysis_function.
Require Import norm_function.
Require Import analysis_func_order.
Require Import analysis_subspace.

(* begin hide *)
Section AnalysisDerivative.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,

    USM : ScalarMult real U,
    @ScalarId real U real_one USM,
    @ScalarLdist real U UP USM,
    @ScalarRdist real U real_plus_class UP USM,
    @ScalarComp real U real_mult_class USM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP,
    @AbsPositive U UA,
    @AbsScalar U UA USM,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    VSM : ScalarMult real V,
    @ScalarId real V real_one VSM,
    @ScalarLdist real V VP VSM,
    @ScalarRdist real V real_plus_class VP VSM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsScalar V VA VSM
}.
Existing Instance abs_metric.

(* end hide *)
Definition frechet_derivative_at
    (O : set_type (open (U := U)))
    (f : set_type [O|] → V)
    (a : set_type [O|])
    (A : set_type (bounded_linear_map (U := U) (V := V)))
    := func_lim
        [O|]
        (λ x, |f x - f a - linear_map_f [A|] ([x|] - [a|])| / |[x|] - [a|]|)
        [a|]
        0.

Definition frechet_differentiable_at
    (O : set_type (open (U := U)))
    (f : set_type [O|] → V)
    (a : set_type [O|])
    := ∃ A, frechet_derivative_at O f a A.

Context (O : set_type (open (U := U))).
Context (f : set_type [O|] → V).

Theorem frechet_derivative_unique : ∀ a A B,
        frechet_derivative_at O f a A → frechet_derivative_at O f a B →
        A = B.
    intros a [A A_bound] [B B_bound] A_dif B_dif.
    apply set_type_eq; cbn.
    apply linear_map_eq.
    intros x.
    classic_case (0 = x) as [x_z|x_nz].
    {
        subst x.
        do 2 rewrite linear_map_zero.
        reflexivity.
    }
    assert (0 ≠ |x|) as x_nz'.
    {
        intros contr.
        rewrite abs_def in contr.
        contradiction.
    }
    unfold frechet_derivative_at in *; cbn in *.
    clear A_bound B_bound.
    pose proof (land A_dif) as Oa.
    rewrite metric_func_lim in A_dif, B_dif by exact Oa.
    apply all_lt_eq.
    intros ε ε_pos.
    cbn.
    assert (0 < ε / |x|) as ε'_pos.
    {
        apply lt_mult; [>exact ε_pos|].
        apply div_pos.
        split; [>apply abs_pos|exact x_nz'].
    }
    pose proof (half_pos _ ε'_pos) as ε2_pos.
    specialize (A_dif _ ε2_pos) as [δ1 [δ1_pos A_dif]].
    specialize (B_dif _ ε2_pos) as [δ2 [δ2_pos B_dif]].
    pose proof [|O] as O_open.
    rewrite open_all_balls in O_open.
    specialize (O_open [a|] [|a]) as [[δ3 δ3_pos] sub].
    pose (δ := min (min δ1 δ2) δ3).
    assert (0 < δ) as δ_pos.
    {
        unfold δ, min.
        case_if; [>case_if|]; assumption.
    }
    pose (x' := (δ/2) / |x| · x).
    pose (x'' := [a|] + x').
    assert (d x'' [a|] < δ) as x_lt.
    {
        unfold x'', x'; cbn.
        rewrite abs_minus.
        rewrite neg_plus.
        rewrite plus_lrinv.
        rewrite abs_neg.
        rewrite abs_scalar.
        rewrite abs_mult.
        rewrite <- abs_div by apply x_nz'.
        rewrite abs_abs.
        rewrite mult_rlinv by exact x_nz'.
        rewrite abs_pos_eq by (apply half_pos; exact δ_pos).
        rewrite <- lt_mult_rrmove_pos by apply two_pos.
        rewrite ldist.
        rewrite mult_rid.
        rewrite <- lt_plus_0_a_b_ab.
        exact δ_pos.
    }
    assert ([O|] x'') as Ox.
    {
        apply sub.
        unfold open_ball.
        rewrite d_sym.
        apply (lt_le_trans x_lt); cbn.
        apply rmin.
    }
    assert (x'' - [a|] = x') as xa_eq.
    {
        unfold x''.
        rewrite plus_comm.
        apply plus_llinv.
    }
    assert (x'' ≠ [a|]) as x_neq.
    {
        unfold x''.
        intros contr.
        symmetry in contr.
        rewrite <- plus_0_a_b_ba in contr.
        unfold x' in contr.
        rewrite <- (scalar_lanni x) in contr.
        apply scalar_rcancel in contr; [>|exact x_nz].
        rewrite <- mult_lrmove in contr by exact x_nz'.
        rewrite <- mult_lrmove in contr by apply two_pos.
        do 2 rewrite mult_lanni in contr.
        destruct δ_pos; contradiction.
    }
    assert (0 < |x'' - [a|]|) as x_neq'.
    {
        split; [>apply abs_pos|].
        intros contr.
        rewrite abs_def in contr.
        rewrite plus_0_anb_a_b in contr.
        contradiction.
    }
    assert (d x'' [a|] < δ1) as x_lt1.
    {
        apply (lt_le_trans x_lt).
        apply (trans (lmin _ _)).
        apply lmin.
    }
    assert (d x'' [a|] < δ2) as x_lt2.
    {
        apply (lt_le_trans x_lt).
        apply (trans (lmin _ _)).
        apply rmin.
    }
    specialize (A_dif [x''|Ox] x_neq x_lt1).
    specialize (B_dif [x''|Ox] x_neq x_lt2).
    cbn in *.
    rewrite neg_zero, plus_rid in A_dif, B_dif.
    pose proof (lt_lrplus A_dif B_dif) as ltq.
    rewrite plus_half in ltq.
    rewrite <- (abs_neg (f [x'' | Ox] - _ - _)) in ltq.
    do 2 rewrite abs_mult in ltq.
    rewrite <- abs_div in ltq by apply x_neq'.
    do 3 rewrite abs_abs in ltq.
    rewrite <- rdist in ltq.
    rewrite <- lt_mult_rrmove_pos in ltq by exact x_neq'.
    apply (le_lt_trans (abs_tri _ _)) in ltq.
    rewrite xa_eq in ltq.
    do 2 rewrite neg_plus in ltq.
    do 2 rewrite neg_neg in ltq.
    rewrite <- (plus_assoc (-f [x'' | Ox])) in ltq.
    rewrite (plus_comm (-f [x'' | Ox])) in ltq.
    do 2 rewrite plus_assoc in ltq.
    rewrite <- (plus_assoc _ (-f [x'' | Ox])) in ltq.
    rewrite plus_linv in ltq.
    rewrite plus_rid in ltq.
    rewrite <- (plus_assoc (f a)) in ltq.
    rewrite (plus_comm _ (-f a)) in ltq.
    rewrite plus_lrinv in ltq.
    unfold x' in ltq.
    do 2 rewrite linear_map_scalar in ltq.
    rewrite <- scalar_rneg in ltq.
    rewrite <- scalar_ldist in ltq.
    do 2 rewrite abs_scalar in ltq.
    rewrite (mult_comm (ε / |x|)) in ltq.
    rewrite <- (mult_assoc _ (|x|)) in ltq.
    apply lt_mult_lcancel_pos in ltq.
    2: {
        split; [>apply abs_pos|].
        intros contr.
        rewrite abs_def in contr.
        rewrite <- mult_lrmove in contr by exact x_nz'.
        rewrite <- mult_lrmove in contr by apply two_pos.
        do 2 rewrite mult_lanni in contr.
        destruct δ_pos; contradiction.
    }
    rewrite mult_comm in ltq.
    rewrite mult_rlinv in ltq by apply x_nz'.
    exact ltq.
Qed.
(* begin hide *)

End AnalysisDerivative.
(* end hide *)
