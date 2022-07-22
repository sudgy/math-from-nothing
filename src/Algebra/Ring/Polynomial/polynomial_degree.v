Require Import init.

Require Export polynomial_base.

Require Import linear_free.
Require Import linear_grade.
Require Import linear_grade_sum.
Require Import nat.
Require Import set.
Require Import card.
Require Import mult_pow.
Require Import order_minmax.

Section Polynomial.

Context U `{Field U}.

Let PP := polynomial_plus U.
Let PZ := polynomial_zero U.
Let PN := polynomial_neg U.
Let PPC := polynomial_plus_comm U.
Let PPA := polynomial_plus_assoc U.
Let PPZ := polynomial_plus_lid U.
Let PPN := polynomial_plus_linv U.
Let PM := polynomial_mult U.
Let PO := polynomial_one U.
Let PL := polynomial_ldist U.
Let PMA := polynomial_mult_assoc U.
Let PMC := polynomial_mult_comm U.
Let PMO := polynomial_mult_lid U.
Let PSM := polynomial_scalar U.
Let PSMO := polynomial_scalar_id U.
Let PSML := polynomial_scalar_ldist U.
Let PSMR := polynomial_scalar_rdist U.
Let PSMC := polynomial_scalar_comp U.
Let PML := polynomial_scalar_lmult U.
Let PMR := polynomial_scalar_rmult U.
Let PG := polynomial_grade U.

Local Existing Instances PP PZ PN PPC PPA PPZ PPN PM PO PL PMA PMC PMO PSM PSMO
    PSML PSMR PSMC PML PMR PG.

Definition polynomial_coefficient (f : polynomial U) (n : nat) := [f|] n : U.
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

Theorem polynomial_coefficient_zero : ∀ n, co 0 n = 0.
Proof.
    intros n.
    unfold zero at 1; cbn.
    reflexivity.
Qed.

Theorem polynomial_coefficient_one_zero : co 1 0 = 1.
Proof.
    unfold co, polynomial_coefficient.
    unfold one at 1; cbn.
    unfold single_to_grade_sum_base; cbn.
    destruct (strong_excluded_middle (0 = 0)) as [eq|neq]; [>|contradiction].
    destruct eq; cbn.
    reflexivity.
Qed.

Theorem to_polynomial_coefficient_zero : ∀ x, co (to_polynomial U x) 0 = x.
Proof.
    intros x.
    unfold to_polynomial.
    rewrite polynomial_coefficient_scalar.
    rewrite polynomial_coefficient_one_zero.
    apply mult_rid.
Qed.

Theorem polynomial_coefficient_eval_zero : ∀ f, polynomial_eval U f 0 = co f 0.
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
        change (polynomial_xn U 0) with 1.
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

Lemma polynomial_degree_ex : ∀ f : polynomial U, ∃ n, ∀ m, n < m → 0 = co f m.
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
    intros f n n_gt.
    unfold polynomial_degree in n_gt.
    rewrite_ex_val m [m_deg m_least].
    apply m_deg.
    exact n_gt.
Qed.

Theorem polynomial_degree_nz : ∀ f, 0 ≠ f → 0 ≠ co f (polynomial_degree f).
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
            apply nat_zero_lt_suc.
    }
    specialize (n_least n).
    prove_parts n_least.
    {
        intros m m_gt.
        nat_destruct m.
        -   apply nat_lt_zero in m_gt.
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
    intros f n fn_nz.
    classic_contradiction contr.
    apply fn_nz.
    apply polynomial_degree_gt.
    rewrite nle_lt in contr.
    exact contr.
Qed.

Theorem polynomial_degree_xn : ∀ n, polynomial_degree (polynomial_xn U n) = n.
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
    apply antisym; [>|apply nat_le_zero].
    apply polynomial_degree_leq.
    intros m m_gt.
    reflexivity.
Qed.

Theorem polynomial_degree_zero_ex : ∀ f, polynomial_degree f = 0 →
    ∃ a, f = to_polynomial U a.
Proof.
    intros f f_zero.
    exists (polynomial_coefficient f 0).
    unfold to_polynomial, polynomial_coefficient.
    apply set_type_eq.
    apply functional_ext.
    intros n.
    unfold scalar_mult; cbn.
    unfold one; cbn.
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
        split; [>apply nat_le_zero|exact n_nz].
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
        apply nat_lt_zero in fg.
        exact fg.
    }
    apply antisym.
    -   apply polynomial_degree_leq.
        intros m m_gt.
        pose proof (trans fg m_gt) as m_gt2.
        apply polynomial_degree_gt in m_gt, m_gt2.
        unfold plus; cbn.
        unfold co, polynomial_coefficient in m_gt, m_gt2.
        rewrite <- m_gt, <- m_gt2.
        rewrite plus_lid.
        reflexivity.
    -   apply polynomial_degree_geq.
        intros contr.
        unfold plus in contr; cbn in contr.
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
    f = a · polynomial_xn U (polynomial_degree f) + g.
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
       (f - co f (polynomial_degree f) · polynomial_xn U (polynomial_degree f)).
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

    assert (∀ m n, polynomial_degree (polynomial_xn U m * polynomial_xn U n)
        = m + n) as lem1.
    {
        intros m n.
        applys_eq polynomial_degree_xn.
        apply f_equal.
        unfold polynomial_xn.
        unfold mult; cbn.
        rewrite (free_bilinear_free _ _ _ m n).
        reflexivity.
    }
    remember (polynomial_degree f) as m.
    remember (polynomial_degree g) as n.
    revert n f g f_nz g_nz Heqm Heqn.
    induction m as [m IHm] using strong_induction; intros.
    assert (∀ m, polynomial_degree (polynomial_xn U m * g)
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
        assert (polynomial_degree (polynomial_xn U m *
            (a · polynomial_xn U (polynomial_degree g)) + polynomial_xn U m * g')
            =
            polynomial_degree (polynomial_xn U m *
                (a · polynomial_xn U (polynomial_degree g)))) as deg_eq.
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
    assert (polynomial_degree (a · polynomial_xn U (polynomial_degree f) * g
        + f' * g) =
        polynomial_degree (a · polynomial_xn U (polynomial_degree f) * g))
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

End Polynomial.
