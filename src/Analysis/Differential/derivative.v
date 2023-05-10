Require Import init.

Require Export analysis_algebraic.

Section Derivative.

Context {U} `{NormedFieldClass U}.
Existing Instance abs_metric.

Definition derivative_at
    {O : set_type (open (U := U))}
    (f : set_type [O|] → U)
    (a : set_type [O|])
    (c : U)
    := func_lim_base (λ x, (f x - f a) / ([x|] - [a|])) [a|] c.

Definition differentiable_at
    {O : set_type (open (U := U))}
    (f : set_type [O|] → U)
    (a : set_type [O|])
    := ∃ c, derivative_at f a c.

Theorem derivative_unique : ∀ {O} (f : set_type [O|] → U) a c1 c2,
    derivative_at f a c1 → derivative_at f a c2 → c1 = c2.
Proof.
    intros O f a c1 c2 c1_d c2_d.
    pose proof (norm_open_limit_point _ _ [|O] [|a]) as a_lim.
    exact (func_lim_unique _ [a|] c1 c2 a_lim c1_d c2_d).
Qed.

Existing Instance subspace_metric.

Theorem derivative_continuous : ∀ {O} (f : set_type [O|] → U) a,
    differentiable_at f a → continuous_at f a.
Proof.
    intros O f a [c c_d].
    assert (func_lim_base (λ x : set_type [O|], [x|] - [a|]) [a|] 0) as lim.
    {
        rewrite <- (plus_rinv [a|]).
        apply func_lim_plus.
        -   apply func_lim_id.
        -   apply func_lim_neg.
            apply constant_func_lim.
    }
    pose proof (func_lim_mult _ _ _ _ _ _ c_d lim) as lim2.
    cbn in lim2.
    rewrite mult_ranni in lim2.
    rewrite <- metric_subspace_topology.
    apply func_lim_continuous.
    pose proof (constant_func_lim [O|] [a|] (f a)) as lim3.
    pose proof (func_lim_plus _ _ _ _ _ _ lim2 lim3) as lim4.
    cbn in lim4.
    rewrite plus_lid in lim4.
    apply (func_lim_eq _ _ _ _ _ lim4).
    intros x neq.
    rewrite <- plus_0_anb_b_a in neq.
    rewrite mult_rlinv by exact neq.
    apply plus_rlinv.
Qed.

Theorem derivative_constant : ∀ (O : set_type open) a x,
    derivative_at (λ _ : set_type [O|], a) x 0.
Proof.
    intros O a x.
    unfold derivative_at.
    applys_eq constant_func_lim.
    apply functional_ext.
    intros y.
    rewrite plus_rinv.
    apply mult_lanni.
Qed.

Theorem derivative_identity : ∀ (O : set_type open) a,
    derivative_at (λ x : set_type [O|], [x|]) a 1.
Proof.
    intros O a.
    cbn.
    apply (func_lim_eq _ _ _ _ _ (constant_func_lim [O|] [a|] 1)).
    intros x neq.
    symmetry; apply mult_rinv.
    rewrite plus_0_anb_b_a.
    exact neq.
Qed.

Theorem derivative_plus : ∀ {O} (f g : set_type [O|] → U) a c d,
    derivative_at f a c → derivative_at g a d →
    derivative_at (λ x, f x + g x) a (c + d).
Proof.
    intros O f g a c d fd gd.
    unfold derivative_at.
    applys_eq (func_lim_plus _ _ _ _ _ _ fd gd); cbn.
    apply functional_ext; intros x.
    rewrite <- rdist.
    rewrite neg_plus.
    rewrite plus_4.
    reflexivity.
Qed.

Theorem chain_rule : ∀ {A B : set_type open}
    (f : set_type [B|] → U) (g : set_type [A|] → set_type [B|]) a c d,
    derivative_at f (g a) c → derivative_at (λ x, [g x|]) a d →
    derivative_at (λ x, f (g x)) a (c * d).
Proof.
    intros A B f g a c d fd gd.
    pose (D x := If x = g a then 0 else (f x - f (g a)) / ([x|] - [g a|]) - c).
    assert (continuous_at D (g a)) as D_cont.
    {
        rewrite <- metric_subspace_topology.
        apply func_lim_continuous.
        unfold D at 2.
        rewrite if_true by reflexivity.
        pose proof (constant_func_lim [B|] [g a|] (-c)) as lim1.
        pose proof (func_lim_plus _ _ _ _ _ _ fd lim1) as lim2.
        cbn in lim2.
        rewrite plus_rinv in lim2.
        apply (func_lim_eq _ _ _ _ _ lim2).
        intros x x_neq.
        unfold D.
        case_if [eq|neq].
        -   subst x.
            contradiction.
        -   reflexivity.
    }
    pose proof (constant_func_lim [A|] [a|] c) as lim1.
    assert (func_lim_base (λ x, D (g x)) [a|] 0) as lim2.
    {
        replace 0 with (D (g a)).
        apply func_lim_compose.
        -   apply func_lim_continuous.
            rewrite <- (metric_subspace_topology [B|]).
            apply continuous_subspace2.
            rewrite metric_subspace_topology.
            apply derivative_continuous.
            exists d.
            exact gd.
        -   exact D_cont.
        -   unfold D.
            rewrite if_true by reflexivity.
            reflexivity.
    }
    pose proof (func_lim_plus _ _ _ _ _ _ lim1 lim2) as lim3.
    cbn in lim3.
    rewrite plus_rid in lim3.
    pose proof (func_lim_mult _ _ _ _ _ _ lim3 gd) as lim4.
    cbn in lim4.
    apply (func_lim_eq _ _ _ _ _ lim4).
    intros x neq.
    unfold D.
    case_if [eq|neq'].
    -   rewrite plus_rid.
        rewrite eq.
        do 2 rewrite plus_rinv.
        rewrite mult_lanni.
        apply mult_ranni.
    -   rewrite (plus_comm c).
        rewrite plus_rlinv.
        rewrite mult_assoc.
        rewrite mult_rlinv.
        +   reflexivity.
        +   rewrite plus_0_anb_a_b.
            rewrite set_type_eq.
            exact neq'.
Qed.

Theorem derivative_mult : ∀ {O} (f g : set_type [O|] → U) a c d,
    derivative_at f a c → derivative_at g a d →
    derivative_at (λ x, f x * g x) a (c * g a + f a * d).
Proof.
    intros O f g a c d fd gd.
    pose proof (derivative_continuous f a (ex_intro _ _ fd)) as f_cont.
    rewrite <- metric_subspace_topology in f_cont.
    apply func_lim_continuous in f_cont.
    pose proof (func_lim_mult _ _ _ _ _ _ f_cont gd) as lim1.
    pose proof (constant_func_lim [O|] [a|] (g a)) as lim2.
    pose proof (func_lim_mult _ _ _ _ _ _ fd lim2) as lim3.
    cbn in *.
    pose proof (func_lim_plus _ _ _ _ _ _ lim3 lim1) as lim4.
    cbn in lim4.
    apply (func_lim_eq _ _ _ _ _ lim4).
    intros x neq.
    rewrite <- mult_assoc.
    rewrite (mult_comm _ (g a)).
    do 2 rewrite mult_assoc.
    rewrite <- rdist.
    rewrite (rdist _ _ (g a)).
    rewrite ldist.
    rewrite plus_comm.
    rewrite plus_assoc.
    rewrite mult_rneg, mult_lneg.
    rewrite plus_rlinv.
    reflexivity.
Qed.

Theorem derivative_constant_mult : ∀ {O} (f : set_type [O|] → U) α a c,
    derivative_at f a c → derivative_at (λ x, α * f x) a (α * c).
Proof.
    intros O f α a c df.
    pose proof (derivative_constant O α a) as lim1.
    pose proof (derivative_mult _ _ _ _ _ lim1 df) as lim2.
    cbn in lim2.
    rewrite mult_lanni in lim2.
    rewrite plus_lid in lim2.
    exact lim2.
Qed.

Theorem derivative_neg : ∀ {O} (f : set_type [O|] → U) a c,
    derivative_at f a c → derivative_at (λ x, -f x) a (-c).
Proof.
    intros O f a c df.
    apply (derivative_constant_mult _ (-1)) in df.
    rewrite mult_neg_one in df.
    applys_eq df.
    apply functional_ext; intros x.
    rewrite mult_neg_one.
    reflexivity.
Qed.

Local Open Scope nat_scope.

Theorem derivative_nat_power : ∀ n a, derivative_at
    (λ x : set_type [[all|all_open]|], [x|]^nat_suc n) a (nat_suc n × [a|]^n).
Proof.
    intros n a.
    cbn in *.
    nat_induction n.
    -   rewrite nat_pow_zero.
        rewrite nat_mult_lid.
        applys_eq derivative_identity.
        apply functional_ext; intros x.
        apply nat_pow_one.
    -   pose proof (derivative_identity [all|all_open] a) as d1.
        pose proof (derivative_mult _ _ _ _ _ IHn d1) as d2.
        cbn in d2.
        rewrite mult_rid in d2.
        rewrite <- nat_mult_assoc in d2.
        rewrite <- nat_pow_suc in d2.
        rewrite plus_comm in d2.
        rewrite <- nat_mult_suc in d2.
        exact d2.
Qed.

Theorem nz_open : open (λ x, 0 ≠ x).
Proof.
    rewrite <- compl_compl.
    applys_eq (point_closed 0).
    rewrite compl_compl.
    reflexivity.
Qed.

Theorem derivative_div : ∀ a,
    derivative_at (λ x : set_type [[_|nz_open]|], /[x|]) a (-/([a|]*[a|])).
Proof.
    cbn.
    intros [a a_nz]; cbn.
    unfold derivative_at; cbn.
    pose proof (constant_func_lim (λ x, 0 ≠ x) a a) as lim1.
    pose proof (func_lim_id (λ x, 0 ≠ x) a) as lim2.
    pose proof (func_lim_mult _ _ _ _ _ _ lim1 lim2) as lim3.
    cbn in lim3.
    pose proof (func_lim_div _ _ _ _ (mult_nz _ _ a_nz a_nz) lim3) as lim4.
    cbn in lim4.
    pose proof (func_lim_neg _ _ _ _ lim4) as lim5.
    cbn in lim5.
    apply (func_lim_eq _ _ _ _ _ lim5).
    intros [x x_nz]; cbn.
    intros neq.
    rewrite <- mult_lrmove.
    2: {
        rewrite plus_0_anb_b_a.
        exact neq.
    }
    rewrite div_mult by assumption.
    rewrite ldist.
    rewrite mult_lneg.
    rewrite mult_rlinv by exact x_nz.
    rewrite mult_comm.
    rewrite mult_lrneg, neg_neg.
    rewrite mult_lrinv by exact a_nz.
    apply plus_comm.
Qed.

End Derivative.
