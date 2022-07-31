Require Import init.

Require Import set.
Require Import order_minmax.

Require Export analysis_algebraic.
Require Import analysis_func_order.

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
    @ScalarRdist real U real_plus UP USM,
    @ScalarComp real U real_mult USM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP,
    @AbsPositive U UA,
    @AbsScalar U UA USM,
    NotTrivial U,

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
    @ScalarRdist real V real_plus VP VSM,

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
        (λ x, |f x - f a - linear_map_f [A|] ([x|] - [a|])| / |[x|] - [a|]|)
        [a|]
        0.

Definition frechet_differentiable_at
    (O : set_type (open (U := U)))
    (f : set_type [O|] → V)
    (a : set_type [O|])
    := ∃ A, frechet_derivative_at O f a A.

Context (O : set_type (open (U := U))).
Context (f g : set_type [O|] → V).

Existing Instance subspace_metric.

Theorem frechet_derivative_unique : ∀ a A B,
        frechet_derivative_at O f a A → frechet_derivative_at O f a B →
        A = B.
    clear g.
    intros a [A A_bound] [B B_bound] [Oa A_dif] [Oa' B_dif]; clear Oa'.
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
    assert (func_lim_base (λ x, | -f x + f a + linear_map_f B ([x|] - [a|])|
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
    assert (func_lim_base (λ x : set_type [O|],
        |linear_map_f B ([x|] - [a|]) - linear_map_f A ([x|] - [a|])|
        / |[x|] - [a|]|) [a|] 0) as lim2.
    {
        pose proof (constant_func_lim [O|] [a|] (zero (U := real))) as lim2.
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
    assert (func_lim_base g 0 a) as g_lim.
    {
        unfold g, g'.
        rewrite <- metric_subspace_topology.
        apply func_lim_set; cbn.
        rewrite <- (plus_rid [a|]) at 1.
        apply func_lim_plus.
        -   apply constant_func_lim.
        -   rewrite <- (scalar_lanni x).
            apply (func_lim_scalar2 εS (λ n, [n|])).
            +   apply func_lim_id.
            +   apply constant_func_lim.
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
    pose proof (constant_func_lim εS 0 (|x|)) as lim4.
    pose proof (func_lim_mult _ _ _ _ _ _ lim3 lim4) as lim5.
    cbn in lim5.
    clear lim3 lim4 g_lim.
    rewrite mult_lanni in lim5.
    assert (func_lim_base (λ _ : set_type εS,
        |linear_map_f B x - linear_map_f A x|) 0 0) as lim6.
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
    pose proof (constant_func_lim εS 0 (|linear_map_f B x - linear_map_f A x|))
        as lim7.
    pose proof (func_lim_unique _ _ _ _ εS0 lim6 lim7) as eq.
    rewrite abs_def in eq.
    rewrite plus_0_anb_b_a in eq.
    exact eq.
Qed.

Theorem frechet_differentiable_continuous : ∀ a,
        frechet_differentiable_at O f a → continuous_at f a.
    intros a [A [Aa A_lim]].
    rewrite <- metric_subspace_topology.
    rewrite func_lim_continuous by exact Aa.
    pose (bf (x : set_type [O|]) := |[x|] - [a|]|).
    assert (func_lim_base bf [a|] 0) as bf_lim.
    {
        unfold bf.
        rewrite (abs_zero (U := U)).
        apply abs_func_lim.
        rewrite <- (plus_rinv [a|]).
        apply (func_lim_plus [O|] (λ x, [x|])).
        -   apply func_lim_id.
        -   apply constant_func_lim.
    }
    pose proof (func_lim_mult _ _ _ _ _ _ A_lim bf_lim) as lim.
    unfold bf in lim; cbn in lim.
    rewrite mult_lanni in lim.
    destruct A as [A A_bounded]; cbn in *.
    assert (func_lim_base
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
    assert (func_lim_base (λ x : set_type [O|],
        linear_map_f A [x|] - linear_map_f A [a|]) [a|] 0) as lim2.
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
    }
    pose proof (func_lim_plus _ _ _ _ _ _ lim1 lim2) as lim3; clear lim1 lim2.
    cbn in lim3.
    rewrite plus_rid in lim3.
    pose proof (constant_func_lim [O|] [a|] (f a)) as lim4.
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

Theorem frechet_derivative_linear : ∀ (F : set_type bounded_linear_map) a,
        frechet_derivative_at [_|all_open] (λ x, linear_map_f [F|] [x|]) a F.
    intros [F F_bound] [a a_in].
    unfold frechet_derivative_at; cbn.
    clear F_bound a_in.
    assert (limit_point all a) as a_lim.
    {
        apply norm_open_limit_point.
        -   apply all_open.
        -   exact true.
    }
    split; [>exact a_lim|].
    pose proof (constant_func_lim all a (zero (U := real))) as lim.
    apply (func_lim_eq _ _ _ _ _ lim).
    intros [x x_in] x_neq; cbn in *.
    clear x_in.
    rewrite linear_map_plus.
    rewrite linear_map_neg.
    rewrite neg_plus, neg_neg.
    rewrite (plus_comm (linear_map_f F x)).
    rewrite plus_assoc.
    rewrite plus_rrinv.
    rewrite plus_linv.
    rewrite <- abs_zero.
    rewrite mult_lanni.
    reflexivity.
Qed.

Theorem frechet_derivative_constant : ∀ x a,
        frechet_derivative_at [_|all_open] (λ _, x) a
            [zero_linear_map|zero_linear_bounded].
    intros x [a a_in].
    unfold frechet_derivative_at; cbn.
    clear a_in.
    assert (limit_point all a) as a_lim.
    {
        apply norm_open_limit_point.
        -   apply all_open.
        -   exact true.
    }
    split; [>exact a_lim|].
    pose proof (constant_func_lim all a (zero (U := real))) as lim.
    apply (func_lim_eq _ _ _ _ _ lim).
    intros [y y_in] y_neq; cbn in *.
    clear y_in.
    rewrite neg_zero, plus_rid.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    rewrite mult_lanni.
    reflexivity.
Qed.

Theorem frechet_derivative_plus : ∀ a A B,
        frechet_derivative_at O f a A → frechet_derivative_at O g a B →
        frechet_derivative_at O (λ x, f x + g x) a
            [plus_linear_map [A|] [B|] | plus_linear_bounded A B].
    intros a A B [Oa f_lim] [Oa' g_lim]; clear Oa'.
    pose proof (func_lim_plus _ _ _ _ _ _ f_lim g_lim) as lim1.
    clear f_lim g_lim.
    cbn in lim1.
    rewrite plus_rid in lim1.
    pose proof (constant_func_lim [O|] [a|] (zero (U := real))) as lim2.
    split; [>exact Oa|].
    eapply (func_squeeze _ _ _ _ _ _ _ lim2 lim1).
    Unshelve.
    intros x x_neq.
    cbn.
    assert (0 < |[x|] - [a|]|) as xa_pos.
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
            exact xa_pos.
    -   rewrite <- rdist.
        apply le_rmult_pos; [>apply div_pos; exact xa_pos|].
        apply (trans2 (abs_tri _ _ )).
        do 2 rewrite neg_plus.
        plus_bring_left (g x).
        plus_bring_left (-g a).
        rewrite (plus_comm (-linear_map_f _ _)).
        apply refl.
Qed.

(* begin hide *)
End AnalysisDerivative.

Section ChainRule.

Context {U V W} `{
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
    @ScalarRdist real U real_plus UP USM,
    @ScalarComp real U real_mult USM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP,
    @AbsPositive U UA,
    @AbsScalar U UA USM,
    NotTrivial U,

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
    @ScalarRdist real V real_plus VP VSM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsScalar V VA VSM,

    WP : Plus W,
    WZ : Zero W,
    WN : Neg W,
    @PlusComm W WP,
    @PlusAssoc W WP,
    @PlusLid W WP WZ,
    @PlusLinv W WP WZ WN,

    WSM : ScalarMult real W,
    @ScalarId real W real_one WSM,
    @ScalarLdist real W WP WSM,
    @ScalarRdist real W real_plus WP WSM,

    WA : AbsoluteValue W,
    @AbsDefinite W WA WZ,
    @AbsNeg W WA WN,
    @AbsTriangle W WA WP,
    @AbsPositive W WA,
    @AbsScalar W WA WSM
}.

Existing Instance abs_metric.
Existing Instance subspace_metric.

(* end hide *)
Theorem frechet_derivative_compose :
        ∀ (O1 : set_type (open (U := U))) (O2 : set_type (open (U := V)))
        (f : set_type [O2|] → W) (g : set_type [O1|] → set_type [O2|]) f' g' a,
        frechet_derivative_at O2 f (g a) f' →
        frechet_derivative_at O1 (λ x, [g x|]) a g' →
        frechet_derivative_at O1 (λ x, f (g x)) a
            [linear_map_compose [f'|] [g'|] |
                linear_map_compose_bounded [f'|] [g'|] [|f'] [|g']].
    intros O1 O2 f g [f' f'_bound] [g' g'_bound] a f'_lim g'_lim.
    assert (continuous_at g a) as g_cont.
    {
        rewrite <- (metric_subspace_topology [O2|]).
        apply continuous_subspace2.
        apply frechet_differentiable_continuous.
        exists [g'|g'_bound].
        exact g'_lim.
    }
    destruct g'_lim as [O1a g'_lim].
    destruct f'_lim as [O2ga f'_lim].
    split; [>exact O1a|].
    cbn in *.
    assert (func_lim_base (λ x, |linear_map_f f'
        ([g x|] - [g a|] - linear_map_f g' ([x|] - [a|]))| / |[x|] - [a|]|)
        [a|] 0) as lim1.
    {
        destruct f'_bound as [M M_bound].
        apply (func_lim_constant _ _ M) in g'_lim.
        rewrite mult_ranni in g'_lim.
        pose proof (constant_func_lim [O1|] [a|] (zero (U := real))) as lim1.
        eapply (func_squeeze _ _ _ _ _ _ _ lim1 g'_lim).
        Unshelve.
        intros x x_neq; cbn.
        assert (0 < |[x|] - [a|]|) as xa_pos.
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
                exact xa_pos.
        -   rewrite mult_assoc.
            apply le_rmult_pos; [>apply div_pos; exact xa_pos|].
            apply M_bound.
    }
    assert (func_bounded_around (λ x, |[g x|] - [g a|]| / |[x|] - [a|]|) [a|])
        as g_bound.
    {
        assert (func_bounded_around (λ x, (/ |[x|] - [a|]|) ·
                ([g x|] - [g a|] - linear_map_f g' ([x|] - [a|]))) [a|])
                as bound1.
        {
            apply (func_lim_bounded_around _ _ _ 0).
            apply func_lim_zero.
            apply (func_lim_eq _ _ _ _ _ g'_lim).
            intros x x_neq.
            assert (0 < |[x|] - [a|]|) as xa_pos.
            {
                split; [>apply abs_pos|].
                intros contr.
                rewrite abs_def in contr.
                rewrite plus_0_anb_b_a in contr.
                contradiction.
            }
            rewrite abs_scalar.
            rewrite mult_comm.
            apply rmult.
            rewrite <- abs_div by apply xa_pos.
            rewrite abs_abs.
            reflexivity.
        }
        assert (func_bounded_around (λ x : set_type [O1|],
            (/ |[x|] - [a|]|) · linear_map_f g' ([x|] - [a|])) [a|]) as bound2.
        {
            destruct g'_bound as [M M_bound].
            exists [1|one_pos], M.
            intros x x_neq x_lt.
            assert (0 < |[x|] - [a|]|) as xa_pos.
            {
                split; [>apply abs_pos|].
                intros contr.
                rewrite abs_def in contr.
                rewrite plus_0_anb_b_a in contr.
                contradiction.
            }
            rewrite abs_scalar.
            rewrite <- abs_div by apply xa_pos.
            rewrite abs_abs.
            rewrite <- le_mult_rlmove_pos by apply xa_pos.
            rewrite mult_comm.
            apply M_bound.
        }
        pose proof (func_bounded_around_plus _ _ _ _ bound1 bound2)
            as [[ε ε_pos] [M M_bound]].
        exists [ε|ε_pos], M.
        intros x x_neq x_lt.
        assert (0 < |[x|] - [a|]|) as xa_pos.
        {
            split; [>apply abs_pos|].
            intros contr.
            rewrite abs_def in contr.
            rewrite plus_0_anb_b_a in contr.
            contradiction.
        }
        specialize (M_bound x x_neq x_lt).
        apply (trans2 M_bound).
        rewrite <- scalar_ldist.
        rewrite abs_mult.
        rewrite abs_scalar.
        rewrite mult_comm.
        rewrite <- abs_div by apply xa_pos.
        do 2 rewrite abs_abs.
        apply le_lmult_pos; [>apply div_pos; exact xa_pos|].
        rewrite plus_rlinv.
        apply refl.
    }
    assert (func_lim_base (λ x,
        |f (g x) - f (g a) - linear_map_f f' ([g x|] - [g a|])|
        / |[x|] - [a|]|) [a|] 0) as lim2.
    {
        apply func_lim_forget.
        cbn.
        apply (func_lim_eq _ (λ x, let x' := [[x|] | land [|x]] in
            (|[g x'|] - [g a|]| / |[x|] - [a|]|) *
            (|f (g x') - f (g a) - linear_map_f f' ([g x'|] - [g a|])|
                / |[g x'|] - [g a|]|))).
        -   apply func_lim_zero_mult.
            +   eapply (func_bounded_around_subset _ _ _ _ _ _ _ g_bound).
                Unshelve.
                Unshelve.
                *   intros x [O1x x_nz].
                    exact O1x.
                *   cbn.
                    intros [x [O1x x_nz]]; cbn.
                    rewrite (proof_irrelevance _ O1x).
                    reflexivity.
            +   rewrite <- metric_subspace_topology in g_cont.
                rewrite func_lim_continuous in g_cont.
                rewrite <- metric_subspace_topology in g_cont.
                assert (func_lim_base (λ x : set_type
                    (λ x, [O1|] x ∧ (∀ H, |f (g [x|H]) - f (g a) -
                        linear_map_f f' ([g [x|H]|] - [g a|])| /
                        |x - [a|]| ≠ 0)),
                    g [[x|] | land [|x]]) [a|] (g a)) as lim2.
                {
                    rewrite <- metric_subspace_topology.
                    eapply (func_lim_subset _ _ _ _ _ _ _ _ g_cont).
                    Unshelve.
                    Unshelve.
                    -   intros x [O1x C0].
                        exact O1x.
                    -   cbn.
                        intros [x [O1x x_neq]]; cbn.
                        apply f_equal.
                        apply f_equal.
                        apply proof_irrelevance.
                }
                rewrite <- metric_subspace_topology in lim2.
                eapply (func_lim_compose2 _ _
                    (λ x, |f x - f (g a) - linear_map_f f' ([x|] - [g a|])| /
                        |[x|] - [g a|]|)_ _ _ _ _ lim2).
                Unshelve.
                *   exact f'_lim.
                *   cbn.
                    intros [x [O1x x_neq]]; cbn.
                    rewrite (proof_irrelevance _ O1x).
                    specialize (x_neq O1x).
                    intros contr.
                    rewrite <- contr in x_neq.
                    do 2 rewrite plus_rinv in x_neq.
                    rewrite linear_map_zero in x_neq.
                    rewrite neg_zero, plus_rid in x_neq.
                    rewrite <- abs_zero in x_neq.
                    rewrite mult_lanni in x_neq.
                    contradiction.
        -   intros [x [O1x x_nz]] x_neq; cbn.
            rewrite (proof_irrelevance _ O1x).
            rewrite mult_comm.
            rewrite <- mult_assoc.
            apply lmult.
            apply mult_llinv.
            intros contr.
            rewrite abs_def in contr.
            cbn in x_neq.
            specialize (x_nz O1x).
            apply x_nz.
            rewrite plus_0_anb_a_b in contr.
            apply set_type_eq in contr.
            rewrite contr.
            do 2 rewrite plus_rinv.
            rewrite linear_map_zero.
            rewrite neg_zero, plus_rid.
            rewrite <- abs_zero.
            apply mult_lanni.
    }
    pose proof (func_lim_plus _ _ _ _ _ _ lim1 lim2) as lim3.
    cbn in lim3.
    rewrite plus_rid in lim3.
    pose proof (constant_func_lim [O1|] [a|] (zero (U := real))) as lim4.
    eapply (func_squeeze _ _ _ _ _ _ _ lim4 lim3).
    Unshelve.
    intros [x O1x] x_neq; cbn in *.
    assert (0 < |x - [a|]|) as xa_pos.
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
            exact xa_pos.
    -   rewrite <- rdist.
        apply le_rmult_pos; [>apply div_pos; exact xa_pos|].
        apply (trans2 (abs_tri _ _ )).
        rewrite (linear_map_plus f').
        rewrite (plus_comm (linear_map_f f' _ + _)).
        rewrite plus_assoc.
        rewrite plus_rlinv.
        rewrite linear_map_neg.
        apply refl.
Qed.
(* begin hide *)

End ChainRule.
(* end hide *)
