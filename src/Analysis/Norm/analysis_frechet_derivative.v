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
Require Import analysis_continuous.
Require Import analysis_scalar.

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

Existing Instance subspace_metric.

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
    assert (func_lim [O|] (λ x, | -f x + f a + linear_map_f B ([x|] - [a|])|
        / |[x|] - [a|]|) [a|] 0) as B_dif'.
    {
        apply (func_lim_eq _ _ _ _ _ B_dif).
        intros y y_neq.
        rewrite <- abs_neg.
        do 2 rewrite neg_plus.
        do 2 rewrite neg_neg.
        reflexivity.
    }
    pose proof (func_lim_plus _ _ _ _ _ _ A_dif B_dif') as lim1.
    clear A_dif B_dif B_dif'.
    cbn in lim1.
    rewrite plus_rid in lim1.
    assert (func_lim [O|] (λ x,
        |linear_map_f B ([x|] - [a|]) - linear_map_f A ([x|] - [a|])|
        / |[x|] - [a|]|) [a|] 0) as lim2.
    {
        pose proof (constant_func_lim [O|] [a|] (zero (U := real)) Oa) as lim2.
        eapply (func_squeeze _ _ _ _ _ _ _ lim2 lim1).
        Unshelve.
        intros y y_neq; cbn.
        assert (0 < |[y|] - [a|]|) as ya_pos.
        {
            split; [>apply abs_pos|].
            intros contr.
            rewrite abs_def in contr.
            rewrite plus_0_anb_b_a in contr.
            contradiction.
        }
        split.
        -   apply le_mult.
            +   apply abs_pos.
            +   apply div_pos.
                exact ya_pos.
        -   rewrite <- rdist.
            apply le_rmult_pos; [>apply div_pos; exact ya_pos|].
            apply (trans2 (abs_tri _ _)).
            rewrite <- (plus_assoc (f y)).
            rewrite (plus_comm (f y)).
            do 2 rewrite plus_assoc.
            rewrite <- (plus_assoc _ (f y)).
            rewrite plus_rinv, plus_rid.
            rewrite (plus_comm (-f a)).
            rewrite plus_rlinv.
            rewrite plus_comm.
            apply refl.
    }
    clear lim1.
    pose proof [|O] as O_open.
    rewrite open_all_balls in O_open.
    specialize (O_open [a|] [|a]) as [[ε ε_pos] sub].
    pose (εS (t : real) := 0 ≠ t ∧ |t| < ε / |x|).
    pose (g' (t : set_type εS) := [a|] + [t|] · x).
    assert (∀ t, [O|] (g' t)) as g_in.
    {
        intros [t [t_nz t_lt]].
        apply sub.
        unfold open_ball, g'; cbn.
        rewrite neg_plus.
        rewrite plus_lrinv.
        rewrite abs_neg.
        rewrite abs_scalar.
        rewrite lt_mult_lrmove_pos.
        -   exact t_lt.
        -   split; [>apply abs_pos|exact x_nz'].
    }
    pose (g t := [_|g_in t]).
    assert (limit_point εS 0) as εS0.
    {
        assert (0 < ε / |x|) as ε'_pos.
        {
            apply lt_mult.
            -   exact ε_pos.
            -   apply div_pos.
                split; [>apply abs_pos|exact x_nz'].
        }
        assert (limit_point (open_ball (zero (U := real)) [_|ε'_pos]) 0)
            as εS0.
        {
            apply norm_open_limit_point.
            -   apply open_ball_open.
            -   unfold open_ball; cbn.
                rewrite neg_zero, plus_rid, <- abs_zero.
                exact ε'_pos.
        }
        eapply (limit_point_sub _ _ _ _ εS0).
        Unshelve.
        intros y [y_lt y_nz].
        split.
        -   exact y_nz.
        -   unfold open_ball in y_lt; cbn in y_lt.
            rewrite plus_lid, abs_neg in y_lt.
            exact y_lt.
    }
    assert (func_lim _ g 0 a) as g_lim.
    {
        unfold g, g'.
        rewrite <- metric_subspace_topology.
        apply func_lim_subset; cbn.
        rewrite <- (plus_rid [a|]) at 1.
        apply func_lim_plus.
        -   apply constant_func_lim.
            exact εS0.
        -   rewrite <- (scalar_lanni x).
            apply (func_lim_scalar2 εS (λ n, [n|])).
            +   apply func_lim_id.
                exact εS0.
            +   apply constant_func_lim.
                exact εS0.
    }
    rewrite <- metric_subspace_topology in g_lim.
    epose proof (func_lim_compose2 _ _ _ _ _ _ _ _ g_lim lim2) as lim3.
    Unshelve.
    2: {
        intros [t [t_nz t_lt]] contr.
        unfold g, g' in contr; cbn in contr.
        apply eq_set_type in contr; cbn in contr.
        rewrite <- plus_0_a_b_ba in contr.
        rewrite <- (scalar_lanni x) in contr.
        apply scalar_rcancel in contr; [>|exact x_nz].
        contradiction.
    }
    clear lim2.
    cbn in lim3.
    unfold g' in lim3.
    pose proof (constant_func_lim εS 0 (|x|) εS0) as lim4.
    pose proof (func_lim_mult _ _ _ _ _ _ lim3 lim4) as lim5.
    cbn in lim5.
    clear lim3 lim4 g_lim.
    rewrite mult_lanni in lim5.
    assert (func_lim εS (λ _, |linear_map_f B x - linear_map_f A x|) 0 0)
        as lim6.
    {
        apply (func_lim_eq _ _ _ _ _ lim5).
        intros y y_nz.
        rewrite (plus_comm [a|]).
        rewrite plus_rrinv.
        do 2 rewrite linear_map_scalar.
        rewrite <- scalar_rneg.
        rewrite <- scalar_ldist.
        do 2 rewrite abs_scalar.
        assert (0 ≠ |[y|]|) as y_nz'.
        {
            intros contr.
            rewrite abs_def in contr.
            contradiction.
        }
        rewrite div_mult by assumption.
        rewrite mult_assoc.
        rewrite mult_rlinv by exact x_nz'.
        rewrite (mult_comm (|[y|]|)).
        apply mult_rrinv.
        exact y_nz'.
    }
    pose proof (constant_func_lim εS 0 (|linear_map_f B x - linear_map_f A x|)
        εS0) as lim7.
    pose proof (func_lim_unique _ _ _ _ _ lim6 lim7) as eq.
    rewrite abs_def in eq.
    rewrite plus_0_anb_b_a in eq.
    exact eq.
Qed.

Theorem frechet_differentiable_continuous : ∀ a,
        frechet_differentiable_at O f a → continuous_at f a.
    intros a [A A_lim].
    unfold frechet_derivative_at in A_lim.
    pose proof (land A_lim) as Aa.
    rewrite <- metric_subspace_topology.
    rewrite func_lim_continuous by exact Aa.
    pose (bf (x : set_type [O|]) := |[x|] - [a|]|).
    assert (func_lim [O|] bf [a|] 0) as bf_lim.
    {
        unfold bf.
        rewrite (abs_zero (U := U)).
        apply abs_func_lim.
        rewrite <- (plus_rinv [a|]).
        apply (func_lim_plus [O|] (λ x, [x|])).
        -   cbn.
            apply func_lim_id.
            exact Aa.
        -   apply constant_func_lim.
            exact Aa.
    }
    pose proof (func_lim_mult _ _ _ _ _ _ A_lim bf_lim) as lim.
    unfold bf in lim; cbn in lim.
    rewrite mult_lanni in lim.
    destruct A as [A A_bounded]; cbn in *.
    assert (func_lim [O|]
        (λ x, |f x - f a - linear_map_f A ([x|] - [a|])|) [a|] 0) as lim1.
    {
        apply (func_lim_eq _ _ _ _ _ lim).
        intros x x_neq.
        apply mult_rlinv.
        intros contr.
        rewrite abs_def in contr.
        rewrite plus_0_anb_b_a in contr.
        contradiction.
    }
    clear A_lim lim.
    apply func_lim_zero in lim1.
    assert (func_lim [O|]
        (λ x, linear_map_f A [x|] - linear_map_f A [a|]) [a|] 0) as lim2.
    {
        rewrite <- (plus_rinv (linear_map_f A [a|])).
        apply func_lim_plus.
        -   apply bounded_uniformly_continuous in A_bounded.
            apply unformly_implies_continuous in A_bounded.
            specialize (A_bounded [a|]).
            pose (A' (x : set_type [O|]) := linear_map_f A [x|]).
            assert (continuous_at A' a) as A'_cont.
            {
                unfold A'.
                rewrite <- metric_subspace_topology.
                apply continuous_subspace.
                exact A_bounded.
            }
            rewrite <- metric_subspace_topology in A'_cont.
            rewrite func_lim_continuous in A'_cont by exact Aa.
            exact A'_cont.
        -   apply constant_func_lim.
            exact Aa.
    }
    pose proof (func_lim_plus _ _ _ _ _ _ lim1 lim2) as lim3; clear lim1 lim2.
    cbn in lim3.
    rewrite plus_rid in lim3.
    pose proof (constant_func_lim [O|] [a|] (f a) Aa) as lim4.
    pose proof (func_lim_plus _ _ _ _ _ _ lim3 lim4) as lim5; clear lim3 lim4.
    cbn in lim5.
    rewrite plus_lid in lim5.
    apply (func_lim_eq _ _ _ _ _ lim5).
    intros x x_neq.
    rewrite (plus_comm [x|]).
    rewrite linear_map_plus, linear_map_neg.
    rewrite neg_plus, neg_neg.
    do 2 rewrite plus_assoc.
    rewrite plus_rlinv.
    rewrite plus_rrinv.
    apply plus_rlinv.
Qed.
(* begin hide *)

End AnalysisDerivative.
(* end hide *)
