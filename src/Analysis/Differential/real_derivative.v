Require Import init.

Require Export analysis_algebraic.
Require Import derivative.
Require Import analysis_frechet_derivative.
Require Import analysis_frechet_bilinear.

Section AnalysisDerivative.

Context {U} `{NormedSpaceClass U}.
Existing Instance abs_metric.

Definition real_derivative_at
    {O : set_type (open (U := real))}
    (f : set_type [O|] → U)
    (a : set_type [O|])
    (c : U)
    := func_lim_base (λ x, (/([x|] - [a|]) · (f x - f a))) [a|] c.

Definition real_differentiable_at
    {O : set_type (open (U := real))}
    (f : set_type [O|] → U)
    (a : set_type [O|])
    := ∃ c, real_derivative_at f a c.

Theorem real_derivative_frechet : ∀ {O} (f : set_type [O|] → U) a c,
    real_derivative_at f a c ↔
    (∃ A, frechet_derivative_at O f a A ∧ [A|] 1 = c).
Proof.
    intros O f a c.
    assert (∀ A : linear_map real U, func_lim_base (λ x : set_type [O|],
        /([x|] - [a|]) · (A ([x|] - [a|]))) [a|] (A 1)) as A_lim.
    {
        intros A.
        rewrite metric_func_lim.
        intros ε ε_pos.
        exists 1.
        split; [>exact one_pos|].
        intros x neq lt.
        cbn.
        rewrite linear_map_plus, linear_map_neg.
        rewrite <- (mult_rid [x|]) at 2.
        rewrite <- (mult_rid [a|]) at 2.
        change ([x|] * 1) with ([x|] · 1 : real).
        change ([a|] * 1) with ([a|] · 1 : real).
        do 2 rewrite linear_map_scalar.
        rewrite <- scalar_lneg.
        rewrite <- scalar_rdist.
        rewrite scalar_comp.
        rewrite mult_linv.
        2: {
            rewrite plus_0_anb_a_b.
            exact neq.
        }
        rewrite scalar_id.
        rewrite plus_rinv.
        rewrite <- abs_zero.
        exact ε_pos.
    }
    split.
    -   unfold real_derivative_at.
        unfold frechet_derivative_at.
        intros lim.
        pose (Af (x : real) := x · c).
        assert (∀ u v, Af (u + v) = Af u + Af v) as A_plus.
        {
            intros u v.
            apply scalar_rdist.
        }
        assert (∀ a v, Af (a · v) = a · Af v) as A_scalar.
        {
            intros b v.
            rewrite scalar_comp.
            reflexivity.
        }
        pose (A := make_linear_map Af A_scalar A_plus).
        assert (bounded_linear_map A) as A_bound.
        {
            exists (|c|).
            intros x.
            cbn.
            unfold Af.
            rewrite abs_scalar.
            rewrite mult_comm.
            apply refl.
        }
        exists [_|A_bound]; cbn.
        split.
        +   pose proof (func_lim_neg _ _ _ _ (A_lim A)) as lim1.
            pose proof (func_lim_plus _ _ _ _ _ _ lim lim1) as lim2.
            cbn in lim2.
            apply abs_func_lim in lim2.
            unfold Af in lim2.
            rewrite scalar_id in lim2.
            rewrite plus_rinv in lim2.
            rewrite <- abs_zero in lim2.
            apply (func_lim_eq _ _ _ _ _ lim2).
            intros x neq.
            rewrite <- scalar_rneg.
            rewrite <- scalar_ldist.
            rewrite abs_scalar.
            rewrite mult_comm.
            unfold Af.
            rewrite abs_div.
            *   reflexivity.
            *   rewrite plus_0_anb_b_a.
                exact neq.
        +   unfold Af.
            apply scalar_id.
    -   intros [A [A_dif c_eq]].
        subst c.
        unfold real_derivative_at.
        unfold frechet_derivative_at in A_dif.
        destruct A as [A A_bound]; cbn in *.
        assert (func_lim_base (λ x : set_type [O|],
            /([x|] - [a|]) · (f x - f a - A ([x|] - [a|]))) [a|] 0) as lim1.
        {
            apply func_lim_zero.
            apply (func_lim_eq _ _ _ _ _ A_dif).
            intros x x_neq.
            rewrite abs_scalar.
            rewrite mult_comm.
            rewrite abs_div.
            -   reflexivity.
            -   rewrite plus_0_anb_b_a.
                exact x_neq.
        }
        clear A_dif.
        pose proof (func_lim_plus _ _ _ _ _ _ lim1 (A_lim A)) as lim.
        cbn in lim.
        rewrite plus_lid in lim.
        applys_eq lim.
        apply functional_ext; intros x.
        rewrite <- scalar_ldist.
        rewrite plus_rlinv.
        reflexivity.
Qed.

End AnalysisDerivative.
Section AnalysisDerivative.

Context {U V W} `{NormedAlgebraClass U, NormedAlgebraClass V, NormedAlgebraClass W}.
Existing Instance abs_metric.

Theorem real_derivative_derivative : ∀ {O} (f : set_type [O|] → real) a c,
    real_derivative_at f a c ↔ derivative_at f a c.
Proof.
    intros O f a c.
    unfold real_derivative_at, derivative_at.
    assert ((λ x : set_type [O|], /([x|] - [a|]) · (f x - f a)) =
            (λ x : set_type [O|], (f x - f a) / ([x|] - [a|]))) as f_eq.
    {
        apply functional_ext; intros x.
        unfold scalar_mult; cbn.
        rewrite mult_comm.
        reflexivity.
    }
    rewrite f_eq.
    reflexivity.
Qed.

Theorem real_derivative_unique : ∀ {O} (f : set_type [O|] → U) a c1 c2,
    real_derivative_at f a c1 → real_derivative_at f a c2 → c1 = c2.
Proof.
    intros O f a c1 c2 c1_d c2_d.
    pose proof (norm_open_limit_point _ _ [|O] [|a]) as a_lim.
    exact (func_lim_unique _ [a|] c1 c2 a_lim c1_d c2_d).
Qed.

Existing Instance subspace_metric.

Theorem real_derivative_continuous : ∀ {O} (f : set_type [O|] → U) a,
    real_differentiable_at f a → continuous_at f a.
Proof.
    intros O f a [c df].
    rewrite real_derivative_frechet in df.
    destruct df as [A [df A_eq]].
    assert (frechet_differentiable_at O f a) as df'.
    {
        exists A.
        exact df.
    }
    apply frechet_differentiable_continuous in df'.
    exact df'.
Qed.

Theorem real_derivative_constant : ∀ (O : set_type open) a x,
    real_derivative_at (λ _ : set_type [O|], a) x 0.
Proof.
    intros O a x.
    apply metric_func_lim.
    intros ε ε_pos.
    exists 1.
    split; [>exact one_pos|].
    intros y neq lt.
    cbn.
    rewrite plus_rinv.
    rewrite scalar_ranni.
    rewrite neg_zero, plus_lid.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Theorem real_derivative_identity : ∀ (O : set_type open) a,
    real_derivative_at (λ x : set_type [O|], [x|]) a 1.
Proof.
    intros O a.
    rewrite real_derivative_derivative.
    apply derivative_identity.
Qed.

Theorem real_derivative_plus : ∀ {O} (f g : set_type [O|] → U) a c d,
    real_derivative_at f a c → real_derivative_at g a d →
    real_derivative_at (λ x, f x + g x) a (c + d).
Proof.
    intros O f g a c d.
    do 3 rewrite real_derivative_frechet.
    intros [A [df A_eq]] [B [dg B_eq]].
    subst c d.
    pose proof (frechet_derivative_plus _ _ _ _ _ _ df dg) as dfg.
    exists [_|plus_linear_bounded A B]; cbn.
    split; [>|reflexivity].
    exact dfg.
Qed.

Theorem real_chain_rule : ∀ {A B : set_type open}
    (f : set_type [B|] → U) (g : set_type [A|] → set_type [B|]) a c d,
    real_derivative_at f (g a) c → derivative_at (λ x, [g x|]) a d →
    real_derivative_at (λ x, f (g x)) a (d · c).
Proof.
    intros A B f g a c d.
    rewrite <- real_derivative_derivative.
    do 3 rewrite real_derivative_frechet.
    intros [F [df F_eq]] [G [dg G_eq]].
    subst c d.
    pose proof (frechet_derivative_compose _ _ _ _ _ _ _ df dg) as dfg.
    exists [_|linear_map_compose_bounded [F|] [G|] [|F] [|G]]; cbn.
    split.
    -   exact dfg.
    -   rewrite <- linear_map_scalar.
        unfold scalar_mult; cbn.
        rewrite mult_rid.
        reflexivity.
Qed.

Theorem real_derivative_bilinear : ∀
    (A : bilinear_map U V W) (A_bounded : bounded_bilinear_map A)
    {O} (f : set_type [O|] → U) (g : set_type [O|] → V) a c d,
    real_derivative_at f a c → real_derivative_at g a d →
    real_derivative_at (λ x, A(f x, g x)) a (A(c, g a) + A(f a, d)).
Proof.
    intros A A_bound O f g a c d.
    do 3 rewrite real_derivative_frechet.
    intros [F [df F_eq]] [G [dg G_eq]].
    subst c d.
    pose proof (frechet_derivative_product A A_bound _ _ _ _ _ df _ dg) as dfg.
    exists [_|frechet_derivative_product_bounded A A_bound O f g a F G]; cbn.
    split.
    -   exact dfg.
    -   rewrite plus_comm.
        reflexivity.
Qed.

End AnalysisDerivative.
Section AnalysisDerivative.

Context {U V W} `{NormedAlgebraClass U, NormedAlgebraClass V, NormedAlgebraClass W}.
Existing Instance abs_metric.

Theorem real_derivative_mult : ∀ {O} (f g : set_type [O|] → U) a c d,
    real_derivative_at f a c → real_derivative_at g a d →
    real_derivative_at (λ x, f x * g x) a (c * g a + f a * d).
Proof.
    intros O.
    pose (A := make_bilinear_map (λ x : U * U, fst x * snd x)
        scalar_lmult scalar_rmult rdist ldist).
    assert (bounded_bilinear_map A) as A_bound.
    {
        pose proof (mult_bound (U := U)) as [M bound].
        exists M.
        intros x y.
        rewrite <- mult_assoc.
        apply bound.
    }
    exact (real_derivative_bilinear A A_bound).
Qed.

Theorem real_derivative_constant_mult : ∀ {O} (f : set_type [O|] → U) α a c,
    real_derivative_at f a c → real_derivative_at (λ x, α * f x) a (α * c).
Proof.
    intros O f α a c df.
    pose proof (real_derivative_constant O α a) as lim1.
    pose proof (real_derivative_mult _ _ _ _ _ lim1 df) as lim2.
    cbn in lim2.
    rewrite mult_lanni in lim2.
    rewrite plus_lid in lim2.
    exact lim2.
Qed.

Theorem real_derivative_scalar : ∀ {O} f (g : set_type [O|] → U) a c d,
    derivative_at f a c → real_derivative_at g a d →
    real_derivative_at (λ x, f x · g x) a (c · g a + f a · d).
Proof.
    pose (Af (x : real * U) := fst x · snd x).
    assert (∀ a u v, Af(a · u, v) = a · Af(u, v)) as A_lscalar.
    {
        intros a u v.
        unfold Af; cbn.
        rewrite scalar_comp.
        reflexivity.
    }
    assert (∀ a u v, Af(u, a · v) = a · Af(u, v)) as A_rscalar.
    {
        intros a u v.
        unfold Af; cbn.
        do 2 rewrite scalar_comp.
        rewrite mult_comm.
        reflexivity.
    }
    pose (A := make_bilinear_map Af
        A_lscalar A_rscalar scalar_rdist scalar_ldist).
    assert (bounded_bilinear_map A) as A_bound.
    {
        exists 1.
        intros x y.
        cbn; unfold Af; cbn.
        rewrite abs_scalar, mult_lid.
        apply refl.
    }
    intros O f g a c d.
    rewrite <- real_derivative_derivative.
    apply (real_derivative_bilinear A A_bound).
Qed.

Theorem real_derivative_constant_scalar : ∀ {O} (f : set_type [O|] → U) α a c,
    real_derivative_at f a c → real_derivative_at (λ x, α · f x) a (α · c).
Proof.
    intros O f α a c df.
    pose proof (derivative_constant O α a) as lim1.
    pose proof (real_derivative_scalar _ _ _ _ _ lim1 df) as lim2.
    cbn in lim2.
    rewrite scalar_lanni in lim2.
    rewrite plus_lid in lim2.
    exact lim2.
Qed.

Theorem real_derivative_neg : ∀ {O} (f : set_type [O|] → U) a c,
    real_derivative_at f a c → real_derivative_at (λ x, -f x) a (-c).
Proof.
    intros O f a c df.
    apply (real_derivative_constant_scalar _ (-1)) in df.
    rewrite scalar_neg_one in df.
    applys_eq df.
    apply functional_ext; intros x.
    rewrite scalar_neg_one.
    reflexivity.
Qed.

Local Open Scope nat_scope.

Theorem real_derivative_nat_power : ∀ n a, real_derivative_at
    (λ x : set_type [[all|all_open]|], [x|]^nat_suc n) a (nat_suc n × [a|]^n).
Proof.
    intros n a.
    rewrite real_derivative_derivative.
    apply derivative_nat_power.
Qed.

End AnalysisDerivative.
