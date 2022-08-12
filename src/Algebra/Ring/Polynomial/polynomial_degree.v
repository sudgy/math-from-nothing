Require Import init.

Require Export polynomial_base.

Require Import euclidean_domain.
Require Import ring_category.

Require Import linear_free.
Require Import linear_grade.
Require Import linear_grade_sum.
Require Import nat.
Require Import set.
Require Import card.
Require Import mult_pow.
Require Import order_minmax.

Section Polynomial.

Context (F : CRingObj).
Let U := cring_U F.
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD.
Context `{
    UML : @MultLcancel U UZ UM,
    UMR : @MultRcancel U UZ UM,
    UD : Div U,
    UMDL : @MultLinv U UZ UM UO UD,
    UMDR : @MultRinv U UZ UM UO UD,
    @NotTrivial U
}.

Let PP := polynomial_plus F.
Let PZ := polynomial_zero F.
Let PN := polynomial_neg F.
Let PPC := polynomial_plus_comm F.
Let PPA := polynomial_plus_assoc F.
Let PPZ := polynomial_plus_lid F.
Let PPN := polynomial_plus_linv F.
Let PM := polynomial_mult F.
Let PO := polynomial_one F.
Let PL := polynomial_ldist F.
Let PMA := polynomial_mult_assoc F.
Let PMC := polynomial_mult_comm F.
Let PMO := polynomial_mult_lid F.
Let PSM := polynomial_scalar F.
Let PSMO := polynomial_scalar_id F.
Let PSML := polynomial_scalar_ldist F.
Let PSMR := polynomial_scalar_rdist F.
Let PSMC := polynomial_scalar_comp F.
Let PML := polynomial_scalar_lmult F.
Let PMR := polynomial_scalar_rmult F.
Let PG := polynomial_grade F.

Local Existing Instances PP PZ PN PPC PPA PPZ PPN PM PO PL PMA PMC PMO PSM PSMO
    PSML PSMR PSMC PML PMR PG.

Definition polynomial_coefficient (f : polynomial F) (n : nat) := [f|] n : U.
Let co := polynomial_coefficient.

Theorem polynomial_coefficient_plus : ∀ f g n, co (f + g) n = co f n + co g n.
Proof.
    intros f g n.
    unfold plus at 1; cbn.
    reflexivity.
Qed.

Theorem polynomial_coefficient_scalar : ∀ a f n, co (a · f) n = a * co f n.
Proof.
    intros a f n.
    unfold scalar_mult; cbn.
    reflexivity.
Qed.

Theorem polynomial_coefficient_neg : ∀ f n, co (-f) n = -(co f n).
Proof.
    intros f n.
    rewrite <- scalar_neg_one.
    rewrite polynomial_coefficient_scalar.
    rewrite mult_lneg.
    rewrite mult_lid.
    reflexivity.
Qed.

Theorem polynomial_coefficient_zero : ∀ n, co 0 n = 0.
Proof.
    intros n.
    unfold zero at 1; cbn.
    reflexivity.
Qed.

Theorem polynomial_coefficient_one_zero : co 1 0 = 1.
Proof.
    unfold co, polynomial_coefficient.
    unfold one, PO, polynomial_one at 1; cbn.
    unfold single_to_grade_sum_base; cbn.
    destruct (strong_excluded_middle (0 = 0)) as [eq|neq]; [>|contradiction].
    destruct eq; cbn.
    reflexivity.
Qed.

Theorem polynomial_coefficient_xn : ∀ (f : polynomial F) m n,
    co (f * polynomial_xn F m) (m + n) = co f n.
Proof.
    intros f m n.
    induction f as [|f f' i fi f'i IHf] using grade_induction.
    {
        rewrite mult_lanni.
        do 2 rewrite polynomial_coefficient_zero.
        reflexivity.
    }
    rewrite rdist.
    do 2 rewrite polynomial_coefficient_plus.
    rewrite IHf.
    apply rplus.
    clear f' f'i IHf.
    apply polynomial_xn_ex in fi as [a f_eq].
    subst f.
    rewrite scalar_lmult.
    do 2 rewrite polynomial_coefficient_scalar.
    rewrite polynomial_xn_mult.
    apply lmult.
    rewrite (plus_comm m).
    unfold co, polynomial_coefficient.
    unfold polynomial_xn; cbn.
    unfold single_to_grade_sum_base; cbn.
    unfold grade_I, PG, polynomial_grade in i; cbn in i.
    destruct (strong_excluded_middle (i + m = n + m)) as [eq1|neq1]; cbn.
    all: destruct (strong_excluded_middle (i = n)) as [eq2|neq2]; cbn.
    -   destruct eq1, eq2; cbn.
        reflexivity.
    -   exfalso.
        apply plus_rcancel in eq1.
        contradiction.
    -   destruct eq2.
        contradiction.
    -   reflexivity.
Qed.

Theorem to_polynomial_coefficient_zero : ∀ x, co (to_polynomial F x) 0 = x.
Proof.
    intros x.
    unfold to_polynomial.
    rewrite polynomial_coefficient_scalar.
    rewrite polynomial_coefficient_one_zero.
    apply mult_rid.
Qed.

Theorem polynomial_coefficient_eval_zero : ∀ f, polynomial_eval f 0 = co f 0.
Proof.
    intros f.
    induction f as [|f f' n fn f'n IHf] using grade_induction.
    {
        rewrite <- to_polynomial_zero.
        rewrite polynomial_eval_constant by exact UMER.
        unfold co, polynomial_coefficient.
        unfold to_polynomial.
        rewrite scalar_lanni.
        reflexivity.
    }
    rewrite polynomial_eval_plus.
    rewrite polynomial_coefficient_plus.
    rewrite IHf.
    apply rplus.
    clear f' f'n IHf.
    apply polynomial_xn_ex in fn as [a eq]; subst f.
    rewrite polynomial_eval_scalar.
    rewrite polynomial_coefficient_scalar.
    apply f_equal.
    rewrite polynomial_eval_xn.
    nat_destruct n.
    -   rewrite pow_0_nat.
        change (polynomial_xn F 0) with 1.
        rewrite <- to_polynomial_one.
        rewrite to_polynomial_coefficient_zero.
        reflexivity.
    -   cbn.
        rewrite mult_ranni.
        unfold single_to_grade_sum_base; cbn.
        destruct (strong_excluded_middle (nat_suc n = 0)) as [eq|neq];
            [>inversion eq|].
        reflexivity.
Qed.

Lemma polynomial_degree_ex : ∀ f : polynomial F, ∃ n, ∀ m, n < m → 0 = co f m.
Proof.
    intros f.
    destruct f as [f f_fin]; cbn in *.
    unfold grade_sum_base in f.
    unfold grade_sum_finite in f_fin.
    cbn in *.
    classic_case (∀ n, 0 = f n) as [f_z|f_nz].
    {
        exists 0.
        intros m m_gt.
        apply f_z.
    }
    rewrite not_all in f_nz.
    pose proof (finite_well_ordered_set_max _ f_fin f_nz)
        as [n [n_nz n_greatest]].
    exists n.
    intros m m_gt.
    classic_contradiction contr.
    specialize (n_greatest m contr).
    destruct (lt_le_trans m_gt n_greatest); contradiction.
Qed.

Definition polynomial_degree f
    := ex_val (well_ordered _ (polynomial_degree_ex f)).

Theorem polynomial_degree_gt : ∀ f n, polynomial_degree f < n → 0 = co f n.
Proof.
    intros f n n_gt.
    unfold polynomial_degree in n_gt.
    rewrite_ex_val m [m_deg m_least].
    apply m_deg.
    exact n_gt.
Qed.

Theorem polynomial_degree_nz : ∀ f, 0 ≠ f → 0 ≠ co f (polynomial_degree f).
Proof.
    intros f f_nz f_z.
    unfold polynomial_degree in f_z.
    rewrite_ex_val n [n_deg n_least].
    nat_destruct n.
    {
        apply f_nz.
        apply set_type_eq.
        apply functional_ext.
        intros m.
        nat_destruct m.
        -   unfold co, polynomial_coefficient in f_z.
            rewrite <- f_z.
            reflexivity.
        -   apply n_deg.
            apply nat_pos2.
    }
    specialize (n_least n).
    prove_parts n_least.
    {
        intros m m_gt.
        nat_destruct m.
        -   apply nat_neg2 in m_gt.
            contradiction m_gt.
        -   rewrite nat_lt_suc_le in m_gt.
            classic_case (n = m) as [eq|neq].
            +   subst.
                exact f_z.
            +   apply n_deg.
                rewrite nat_sucs_lt.
                split; assumption.
    }
    rewrite <- nlt_le in n_least.
    apply n_least.
    apply nat_lt_suc.
Qed.

Theorem polynomial_degree_leq :
    ∀ f n, (∀ m, n < m → 0 = co f m) → polynomial_degree f <= n.
Proof.
    intros f m m_gt.
    unfold polynomial_degree.
    rewrite_ex_val n [n_deg n_least].
    apply n_least.
    exact m_gt.
Qed.

Theorem polynomial_degree_geq : ∀ f n, 0 ≠ co f n → n <= polynomial_degree f.
Proof.
    intros f n fn_nz.
    classic_contradiction contr.
    apply fn_nz.
    apply polynomial_degree_gt.
    rewrite nle_lt in contr.
    exact contr.
Qed.

Theorem polynomial_degree_xn : ∀ n, polynomial_degree (polynomial_xn F n) = n.
Proof.
    intros n.
    apply antisym.
    -   apply polynomial_degree_leq.
        intros m m_gt.
        unfold polynomial_xn; cbn.
        unfold single_to_grade_sum_base; cbn.
        destruct (strong_excluded_middle (n = m)) as [eq|neq].
        +   destruct m_gt; contradiction.
        +   reflexivity.
    -   apply polynomial_degree_geq.
        unfold polynomial_xn; cbn.
        unfold single_to_grade_sum_base; cbn.
        destruct (strong_excluded_middle (n = n)) as [eq|neq].
        +   destruct eq; cbn.
            apply not_trivial_one.
        +   contradiction.
Qed.

Theorem polynomial_degree_zero : polynomial_degree 0 = 0.
Proof.
    apply antisym; [>|apply nat_pos].
    apply polynomial_degree_leq.
    intros m m_gt.
    reflexivity.
Qed.

Theorem polynomial_degree_zero_ex : ∀ f, polynomial_degree f = 0 →
    ∃ a, f = to_polynomial F a.
Proof.
    intros f f_zero.
    exists (polynomial_coefficient f 0).
    unfold to_polynomial, polynomial_coefficient.
    apply set_type_eq.
    apply functional_ext.
    intros n.
    unfold scalar_mult, polynomial_scalar; cbn.
    unfold one, polynomial_one; cbn.
    unfold single_to_grade_sum_base; cbn.
    destruct (strong_excluded_middle (0 = n)) as [n_z|n_nz]; cbn.
    -   destruct n_z; cbn.
        unfold scalar_mult; cbn.
        rewrite mult_rid.
        reflexivity.
    -   unfold scalar_mult; cbn.
        rewrite mult_ranni.
        symmetry; apply polynomial_degree_gt.
        rewrite f_zero.
        split; [>apply nat_pos|exact n_nz].
Qed.

Theorem polynomial_degree_plus : ∀ f g,
    polynomial_degree (f+g) <= max (polynomial_degree f) (polynomial_degree g).
Proof.
    assert (∀ f g, polynomial_degree f <= polynomial_degree g →
        polynomial_degree (f + g) <= polynomial_degree g) as wlog.
    {
        intros f g leq.
        apply polynomial_degree_leq.
        intros m m_gt.
        rewrite polynomial_coefficient_plus.
        rewrite <- (polynomial_degree_gt _ _ m_gt).
        rewrite <- (polynomial_degree_gt _ _ (le_lt_trans leq m_gt)).
        rewrite plus_lid.
        reflexivity.
    }
    intros f g.
    unfold max; case_if.
    -   apply wlog.
        exact l.
    -   rewrite plus_comm.
        apply wlog.
        rewrite nle_lt in n.
        apply n.
Qed.

Theorem polynomial_degree_plus_gt : ∀ f g,
    polynomial_degree f < polynomial_degree g →
    polynomial_degree (f + g) = polynomial_degree g.
Proof.
    intros f g fg.
    assert (0 ≠ g) as g_nz.
    {
        intros contr.
        pose proof polynomial_degree_zero as g0.
        rewrite contr in g0.
        rewrite g0 in fg.
        apply nat_neg2 in fg.
        exact fg.
    }
    apply antisym.
    -   apply polynomial_degree_leq.
        intros m m_gt.
        pose proof (trans fg m_gt) as m_gt2.
        apply polynomial_degree_gt in m_gt, m_gt2.
        unfold plus, PP, polynomial_plus; cbn.
        unfold co, polynomial_coefficient in m_gt, m_gt2.
        rewrite <- m_gt, <- m_gt2.
        rewrite plus_lid.
        reflexivity.
    -   apply polynomial_degree_geq.
        intros contr.
        unfold plus, PP, polynomial_plus in contr; cbn in contr.
        apply polynomial_degree_gt in fg.
        unfold co, polynomial_coefficient in fg.
        rewrite <- fg in contr.
        rewrite plus_lid in contr.
        apply polynomial_degree_nz in g_nz.
        contradiction.
Qed.

Theorem polynomial_degree_scalar : ∀ a f, 0 ≠ a →
    polynomial_degree (a · f) = polynomial_degree f.
Proof.
    intros a f a_nz.
    classic_case (0 = f) as [f_z|f_nz].
    {
        subst f.
        rewrite scalar_ranni.
        reflexivity.
    }
    apply antisym.
    -   apply polynomial_degree_leq.
        intros n n_gt.
        unfold co, polynomial_coefficient; cbn.
        unfold scalar_mult; cbn.
        unfold scalar_mult; cbn.
        rewrite <- (mult_ranni a).
        apply lmult.
        apply polynomial_degree_gt.
        exact n_gt.
    -   apply polynomial_degree_geq.
        unfold co, polynomial_coefficient; cbn.
        unfold scalar_mult; cbn.
        unfold scalar_mult; cbn.
        intros contr.
        rewrite <- (mult_ranni a) in contr.
        apply mult_lcancel in contr; [>|exact a_nz].
        apply polynomial_degree_nz in contr; [>|exact f_nz].
        exact contr.
Qed.

Theorem polynomial_degree_split : ∀ f, 0 ≠ polynomial_degree f → ∃ a g,
    0 ≠ a ∧ polynomial_degree g < polynomial_degree f ∧
    f = a · polynomial_xn F (polynomial_degree f) + g.
Proof.
    intros f f_nz.
    assert (0 ≠ f) as f_nz'.
    {
        intros contr.
        rewrite <- contr in f_nz.
        apply f_nz.
        symmetry; exact polynomial_degree_zero.
    }
    exists (co f (polynomial_degree f)),
       (f - co f (polynomial_degree f) · polynomial_xn F (polynomial_degree f)).
    split; [>|split].
    -   apply polynomial_degree_nz.
        exact f_nz'.
    -   remember (polynomial_degree f) as n.
        nat_destruct n; [>contradiction|].
        clear f_nz.
        rewrite nat_lt_suc_le.
        apply polynomial_degree_leq.
        intros m m_gt.
        classic_case (m = nat_suc n) as [eq|neq].
        +   rewrite eq.
            rewrite polynomial_coefficient_plus.
            rewrite <- scalar_lneg.
            rewrite polynomial_coefficient_scalar.
            unfold co, polynomial_coefficient.
            unfold polynomial_xn; cbn.
            unfold single_to_grade_sum_base; cbn.
            destruct (strong_excluded_middle (nat_suc n = nat_suc n)) as
                [eq'|neq]; [>destruct eq'; cbn|contradiction].
            rewrite mult_rid.
            rewrite plus_rinv.
            reflexivity.
        +   rewrite polynomial_coefficient_plus.
            assert (polynomial_degree f < m) as m_gt2.
            {
                rewrite <- Heqn.
                split.
                -   rewrite <- nlt_le.
                    rewrite nat_lt_suc_le.
                    rewrite nle_lt.
                    exact m_gt.
                -   rewrite neq_sym.
                    exact neq.
            }
            rewrite <- (polynomial_degree_gt _ _ m_gt2).
            rewrite plus_lid.
            rewrite <- scalar_lneg.
            rewrite polynomial_coefficient_scalar.
            unfold co, polynomial_coefficient.
            unfold polynomial_xn; cbn.
            unfold single_to_grade_sum_base; cbn.
            rewrite neq_sym in neq.
            destruct (strong_excluded_middle (nat_suc n = m)) as [eq|neq'];
                [>contradiction|clear neq'].
            rewrite mult_ranni.
            reflexivity.
    -   rewrite plus_comm.
        rewrite plus_rlinv.
        reflexivity.
Qed.

Theorem polynomial_degree_mult : ∀ f g, 0 ≠ f → 0 ≠ g →
    polynomial_degree (f * g) = polynomial_degree f + polynomial_degree g.
Proof.
    intros f g f_nz g_nz.

    assert (∀ m n, polynomial_degree (polynomial_xn F m * polynomial_xn F n)
        = m + n) as lem1.
    {
        intros m n.
        applys_eq polynomial_degree_xn.
        apply f_equal.
        unfold polynomial_xn.
        unfold mult, PM, polynomial_mult; cbn.
        rewrite (free_bilinear_free _ _ _ m n).
        reflexivity.
    }
    remember (polynomial_degree f) as m.
    remember (polynomial_degree g) as n.
    revert n f g f_nz g_nz Heqm Heqn.
    induction m as [m IHm] using strong_induction; intros.
    assert (∀ m, polynomial_degree (polynomial_xn F m * g)
        = m + polynomial_degree g) as lem2.
    {
        clear f f_nz m IHm Heqm.
        intros m.
        revert g g_nz Heqn.
        induction n as [n IHn] using strong_induction; intros.
        classic_case (0 = polynomial_degree g) as [g_z|g_nz'].
        {
            rewrite <- g_z.
            rewrite plus_rid.
            symmetry in g_z.
            apply polynomial_degree_zero_ex in g_z as [a g_eq].
            rewrite g_eq.
            rewrite <- to_polynomial_comm.
            rewrite to_polynomial_scalar.
            rewrite polynomial_degree_scalar; [>apply polynomial_degree_xn|].
            intros contr.
            subst a.
            rewrite g_eq in g_nz.
            apply g_nz.
            unfold to_polynomial.
            rewrite scalar_lanni.
            reflexivity.
        }
        apply polynomial_degree_split in g_nz' as [a [g' [a_nz [g_lt g_eq]]]].
        rewrite <- Heqn.
        rewrite g_eq.
        rewrite ldist.
        assert (polynomial_degree (polynomial_xn F m *
            (a · polynomial_xn F (polynomial_degree g)) + polynomial_xn F m * g')
            =
            polynomial_degree (polynomial_xn F m *
                (a · polynomial_xn F (polynomial_degree g)))) as deg_eq.
        {
            classic_case (0 = g') as [g'_z|g'_nz].
            -   rewrite <- g'_z.
                rewrite mult_ranni, plus_rid.
                reflexivity.
            -   rewrite <- Heqn in g_lt.
                specialize (IHn _ g_lt _ g'_nz
                    (Logic.eq_refl (polynomial_degree g'))).
                rewrite plus_comm.
                apply polynomial_degree_plus_gt.
                rewrite IHn.
                rewrite <- Heqn.
                rewrite scalar_rmult.
                rewrite polynomial_degree_scalar by exact a_nz.
                rewrite lem1.
                apply lt_lplus.
                exact g_lt.
        }
        rewrite deg_eq; clear deg_eq.
        rewrite <- Heqn.
        rewrite scalar_rmult.
        rewrite polynomial_degree_scalar by exact a_nz.
        apply lem1.
    }
    classic_case (0 = polynomial_degree f) as [f_z|f_nz'].
    {
        rewrite Heqm, <- f_z.
        rewrite plus_lid.
        symmetry in f_z.
        apply polynomial_degree_zero_ex in f_z as [a f_eq].
        rewrite f_eq.
        rewrite to_polynomial_scalar.
        rewrite polynomial_degree_scalar; [>symmetry; exact Heqn|].
        intros contr.
        subst a.
        rewrite f_eq in f_nz.
        apply f_nz.
        unfold to_polynomial.
        rewrite scalar_lanni.
        reflexivity.
    }
    apply polynomial_degree_split in f_nz' as [a [f' [a_nz [f_lt f_eq]]]].
    rewrite f_eq.
    rewrite rdist.
    assert (polynomial_degree (a · polynomial_xn F (polynomial_degree f) * g
        + f' * g) =
        polynomial_degree (a · polynomial_xn F (polynomial_degree f) * g))
        as deg_eq.
    {
        classic_case (0 = f') as [f'_z|f'_nz].
        -   rewrite <- f'_z.
            rewrite mult_lanni, plus_rid.
            reflexivity.
        -   rewrite <- Heqm in f_lt.
            specialize (IHm _ f_lt _ _ _ f'_nz g_nz
                (Logic.eq_refl (polynomial_degree f')) Heqn).
            rewrite plus_comm.
            apply polynomial_degree_plus_gt.
            rewrite IHm.
            rewrite <- Heqm.
            rewrite scalar_lmult.
            rewrite polynomial_degree_scalar by exact a_nz.
            rewrite lem2.
            rewrite <- Heqn.
            apply lt_rplus.
            exact f_lt.
    }
    rewrite deg_eq; clear deg_eq.
    rewrite scalar_lmult.
    rewrite polynomial_degree_scalar by exact a_nz.
    rewrite lem2.
    rewrite Heqm, Heqn.
    reflexivity.
Qed.

Local Program Instance polynomial_euclidean : EuclideanDomain (polynomial F) :={
    euclidean_f := polynomial_degree
}.
Next Obligation.
    rename H0 into b_nz.
    remember (polynomial_degree a) as n.
    pose (m := polynomial_degree b).
    revert a Heqn.
    induction n as [n IHn] using strong_induction.
    intros a Heqn.
    classic_case (n < m) as [nm|mn].
    {
        exists 0, a.
        split.
        -   rewrite mult_ranni.
            rewrite plus_lid.
            reflexivity.
        -   right.
            rewrite <- Heqn.
            exact nm.
    }
    rewrite nlt_le in mn.
    classic_case (0 = n) as [n_z|n_nz].
    {
        rewrite <- n_z in mn.
        apply nat_neg_eq in mn.
        unfold m in mn.
        rewrite Heqn in n_z.
        symmetry in mn, n_z.
        apply polynomial_degree_zero_ex in mn, n_z.
        destruct mn as [b' b_eq].
        destruct n_z as [a' a_eq].
        subst a b.
        exists (to_polynomial F (a' / b')), 0.
        split; [>|left; reflexivity].
        rewrite plus_rid.
        rewrite <- to_polynomial_mult.
        rewrite mult_comm.
        rewrite mult_rlinv; [>reflexivity|].
        intros contr; subst b'.
        rewrite to_polynomial_zero in b_nz.
        contradiction.
    }
    apply nat_le_ex in mn as [c c_eq].
    pose (a' := a - co a n / co b m · polynomial_xn F c * b).
    specialize (IHn (polynomial_degree a')).
    prove_parts IHn.
    {
        classic_case (0 = a') as [a'_z|a'_nz].
        {
            rewrite <- a'_z.
            rewrite polynomial_degree_zero.
            split; [>apply nat_pos|exact n_nz].
        }
        rewrite Heqn.
        split.
        -   apply polynomial_degree_leq.
            intros z z_gt.
            unfold a'.
            rewrite polynomial_coefficient_plus.
            rewrite polynomial_coefficient_neg.
            rewrite scalar_lmult.
            rewrite polynomial_coefficient_scalar.
            rewrite <- (polynomial_degree_gt _ _ z_gt).
            rewrite plus_lid.
            apply nat_lt_ex in z_gt as [d [d_nz d_eq]].
            rewrite <- d_eq.
            rewrite <- Heqn.
            rewrite <- c_eq at 2.
            rewrite (mult_comm _ b).
            rewrite (plus_comm m c).
            rewrite <- plus_assoc.
            rewrite polynomial_coefficient_xn.
            assert (m < m + d) as d_gt.
            {
                rewrite <- (plus_rid m) at 1.
                apply lt_lplus.
                split; [>apply nat_pos|exact d_nz].
            }
            rewrite <- (polynomial_degree_gt _ _ d_gt).
            rewrite mult_ranni.
            rewrite neg_zero.
            reflexivity.
        -   intros contr.
            apply (polynomial_degree_nz _ a'_nz).
            rewrite contr.
            rewrite <- Heqn.
            unfold a'.
            rewrite polynomial_coefficient_plus.
            rewrite polynomial_coefficient_neg.
            rewrite scalar_lmult.
            rewrite polynomial_coefficient_scalar.
            rewrite <- c_eq at 3.
            rewrite (mult_comm _ b).
            rewrite (plus_comm m c).
            rewrite polynomial_coefficient_xn.
            rewrite mult_rlinv.
            +   rewrite plus_rinv.
                reflexivity.
            +   apply polynomial_degree_nz.
                exact b_nz.
    }
    specialize (IHn a' (Logic.eq_refl _)) as [q' [r [a'_eq r_lt]]].
    exists (q' + co a n / co b m · polynomial_xn F c), r.
    split; [>|exact r_lt].
    rewrite ldist.
    rewrite <- plus_assoc.
    rewrite (plus_comm _ r).
    rewrite plus_assoc.
    rewrite <- a'_eq.
    unfold a'.
    rewrite mult_comm.
    rewrite plus_rlinv.
    reflexivity.
Qed.

End Polynomial.
