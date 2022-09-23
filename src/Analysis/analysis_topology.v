Require Import init.

Require Export analysis_base.
Require Export topology.

Require Import order_minmax.
Require Import order_abs.

(* begin hide *)
Section MetricTopology.

Context {U} `{Metric U}.
(* end hide *)
Definition open_ball x (ε : real_pos) := λ y, d x y < [ε|].
Definition closed_ball x (ε : real_pos) := λ y, d x y ≤ [ε|].

Definition bounded X := ∃ M, ∀ a b, X a → X b → d a b ≤ M.
(* begin hide *)
Local Open Scope card_scope.
(* end hide *)
Definition totally_bounded X := ∀ ε,
    ∃ A, finite (|set_type A|) ∧ X ⊆ ⋃ (image_under (λ a, open_ball a ε) A).

Theorem open_ball_ex : ∀ x y ε, open_ball x ε y →
    ∃ δ, open_ball y δ ⊆ open_ball x ε.
Proof.
    intros x y ε y_in.
    assert (0 < [ε|] - d x y) as δ_pos.
    {
        unfold open_ball in y_in.
        apply lt_rplus with (-d x y) in y_in.
        rewrite plus_rinv in y_in.
        exact y_in.
    }
    exists [_|δ_pos].
    intros a a_in.
    unfold open_ball in *; cbn in *.
    apply (le_lt_trans (d_tri _ y _)).
    apply lt_rplus with (d x y) in a_in.
    rewrite <- plus_assoc, plus_linv, plus_rid in a_in.
    rewrite plus_comm.
    exact a_in.
Qed.

Theorem open_ball_sub : ∀ x ε1 ε2, ε1 ≤ ε2 → open_ball x ε1 ⊆ open_ball x ε2.
Proof.
    intros x ε1 ε2 leq a a1.
    unfold open_ball in *.
    exact (lt_le_trans a1 leq).
Qed.

Theorem open_ball_self : ∀ x ε, open_ball x ε x.
Proof.
    intros x ε.
    unfold open_ball.
    rewrite d_zero.
    exact [|ε].
Qed.

Theorem open_closed_ball_sub : ∀ x ε, open_ball x ε ⊆ closed_ball x ε.
Proof.
    intros x ε a a_lt.
    apply a_lt.
Qed.

Theorem closed_ball_sub : ∀ x ε1 ε2, ε1 ≤ ε2 →
    closed_ball x ε1 ⊆ closed_ball x ε2.
Proof.
    intros x ε1 ε2 leq a a1.
    unfold closed_ball in *.
    exact (trans a1 leq).
Qed.

Theorem closed_ball_self : ∀ x ε, closed_ball x ε x.
Proof.
    intros x ε.
    unfold closed_ball.
    rewrite d_zero.
    apply [|ε].
Qed.

(* begin show *)
Global Program Instance metric_topology : TopologyBasis U := {
    top_basis S := ∃ x ε, S = open_ball x ε
}.
(* end show *)
Next Obligation.
    exists (open_ball x [1|one_pos]).
    split.
    -   exists x, [1|one_pos].
        reflexivity.
    -   apply open_ball_self.
Qed.
Next Obligation.
    rename H6 into ε1, H4 into ε2, H0 into a, H1 into b, H2 into xa, H3 into xb.
    pose proof (open_ball_ex _ _ _ xa) as [δ1 sub1].
    pose proof (open_ball_ex _ _ _ xb) as [δ2 sub2].
    exists (open_ball x (min δ1 δ2)).
    split.
    2: split.
    -   exists x, (min δ1 δ2).
        reflexivity.
    -   apply open_ball_self.
    -   intros m m_in.
        split.
        +   apply sub1.
            apply (open_ball_sub _ (min δ1 δ2) _); try exact m_in.
            apply lmin.
        +   apply sub2.
            apply (open_ball_sub _ (min δ1 δ2) _); try exact m_in.
            apply rmin.
Qed.

Theorem open_ball_basis : ∀ x ε, top_basis (open_ball x ε).
Proof.
    intros x ε.
    exists x, ε.
    reflexivity.
Qed.

Theorem open_ball_open : ∀ x ε, open (open_ball x ε).
Proof.
    intros x ε.
    apply basis_open.
    apply open_ball_basis.
Qed.

Theorem open_ball_le_sub : ∀ x ε δ, δ ≤ ε → open_ball x δ ⊆ open_ball x ε.
Proof.
    intros x ε δ leq y y_in.
    unfold open_ball in *.
    exact (lt_le_trans y_in leq).
Qed.

Theorem closed_ball_closed : ∀ x ε, closed (closed_ball x ε).
Proof.
    intros x ε.
    rewrite closed_limit_points.
    intros a a_lim.
    classic_contradiction contr.
    unfold closed_ball in contr.
    rewrite nle_lt in contr.
    apply lt_rplus with (-[ε|]) in contr.
    rewrite plus_rinv in contr.
    pose proof (open_ball_open a [_|contr]) as a_open.
    pose proof (open_ball_self a [_|contr]) as a_in.
    specialize (a_lim _ a_open a_in).
    apply empty_neq in a_lim.
    destruct a_lim as [b [[b_in1 b_na] b_in2]].
    unfold open_ball, closed_ball in *; cbn in *.
    clear - b_in1 b_in2.
    destruct ε as [ε ε_pos]; cbn in *.
    apply lt_rplus with ε in b_in2.
    rewrite <- plus_assoc, plus_linv, plus_rid in b_in2.
    apply lt_lplus with (-d a b) in b_in2.
    rewrite plus_assoc, plus_linv, plus_lid in b_in2.
    pose proof (le_lt_trans b_in1 b_in2) as ltq.
    apply lt_lplus with (d a b) in ltq.
    rewrite plus_assoc, plus_rinv, plus_lid in ltq.
    pose proof (d_tri x b a) as leq.
    pose proof (lt_le_trans ltq leq) as eq.
    rewrite plus_comm in eq.
    rewrite (d_sym a b) in eq.
    destruct eq; contradiction.
Qed.

Theorem open_all_balls : ∀ S, open S ↔ (∀ x, S x → ∃ δ, open_ball x δ ⊆ S).
Proof.
    intros S.
    split.
    -   intros S_open x Sx.
        unfold open in S_open; cbn in S_open.
        specialize (S_open x Sx) as [B [[x' [δ B_eq]] [Bx sub]]].
        subst B.
        pose proof (open_ball_ex _ _ _ Bx) as [δ' sub2].
        exists δ'.
        apply (trans sub2).
        exact sub.
    -   intros all_ex.
        unfold open; cbn.
        intros x Sx.
        specialize (all_ex x Sx) as [δ sub].
        exists (open_ball x δ).
        split.
        2: split.
        +   exists x, δ.
            reflexivity.
        +   apply open_ball_self.
        +   exact sub.
Qed.

(* begin hide *)
Lemma metric_hausdorff_base : ∀ x1 x2, x1 ≠ x2 →
        ∃ S1 S2, open S1 ∧ open S2 ∧ S1 x1 ∧ S2 x2 ∧ disjoint S1 S2.
Proof.
    intros x1 x2 neq.
    pose (ε := d x1 x2).
    assert (0 < ε / 2) as ε_pos.
    {
        apply lt_mult_rcancel_pos with 2.
        1: exact two_pos.
        rewrite mult_lanni.
        rewrite <- mult_assoc, mult_linv, mult_rid by apply two_pos.
        unfold ε.
        apply d_neq_pos.
        exact neq.
    }
    exists (open_ball x1 [_|ε_pos]), (open_ball x2 [_|ε_pos]).
    split.
    2: split.
    3: split.
    4: split.
    -   apply open_ball_open.
    -   apply open_ball_open.
    -   apply open_ball_self.
    -   apply open_ball_self.
    -   unfold disjoint.
        apply empty_eq.
        intros x [x_in1 x_in2].
        unfold open_ball in *.
        cbn in *.
        pose proof (lt_lrplus x_in1 x_in2) as ltq.
        rewrite (d_sym x2 x) in ltq.
        apply (le_lt_trans (d_tri _ _ _)) in ltq.
        rewrite plus_half in ltq.
        unfold ε in ltq.
        destruct ltq; contradiction.
Qed.
(* end hide *)
Global Instance metric_hausdorff : HausdorffSpace U := {
    hausdorff_space := metric_hausdorff_base
}.

Theorem totally_bounded_bounded : ∀ X, totally_bounded X → bounded X.
Proof.
    intros X X_bounded.
    specialize (X_bounded [1|one_pos]) as [A [A_fin sub_A]].
    apply fin_nat_ex in A_fin as [n n_eq].
    classic_case (0 = n) as [n0|n0].
    {
        subst.
        apply zero_is_empty in n_eq.
        exists 0.
        intros x y Xx Xy.
        apply sub_A in Xx.
        destruct Xx as [S [[a [Aa S_eq]] Sx]].
        rewrite n_eq in Aa.
        contradiction Aa.
    }
    pose (Ms x := ∃ a b : set_type A, x = d [a|] [b|]).
    assert (finite (|set_type Ms|)) as Ms_fin.
    {
        assert (|set_type (A * A)%set| ≤ nat_to_card (n * n)) as A2_size.
        {
            rewrite <- nat_to_card_mult.
            symmetry in n_eq.
            unfold nat_to_card in n_eq; equiv_simpl in n_eq.
            destruct n_eq as [f f_bij].
            unfold le, nat_to_card, mult; equiv_simpl.
            exists (λ aa,
                (f [fst [aa|] | land [|aa]], f [snd [aa|] | rand [|aa]])).
            intros [[a1 a2] [Aa1 Aa2]] [[a3 a4] [Aa3 Aa4]] eq; cbn in *.
            inversion eq as [[eq1 eq2]]; clear eq.
            apply f_bij in eq1, eq2.
            apply set_type_eq; cbn.
            inversion eq1.
            inversion eq2.
            reflexivity.
        }
        assert (finite (|set_type (A * A)%set|)) as A2_fin.
        {
            apply (le_lt_trans A2_size).
            apply nat_is_finite.
        }
        apply (le_lt_trans2 A2_fin).
        unfold le; equiv_simpl.
        exists (λ M : set_type Ms,
            let a1 := ex_val [|M] in
            let  a2 := ex_val (ex_proof [|M]) in
            [([a1|], [a2|]) | make_and [|a1] [|a2]]).
        intros x y eq; cbn in eq.
        inversion eq as [[eq1 eq2]]; clear eq.
        apply set_type_eq in eq1, eq2.
        unfold ex_val in eq1.
        unfold ex_proof in eq2.
        destruct (ex_to_type _) as [a1 [b1 x_eq]]; cbn in *.
        destruct (ex_to_type _) as [a2 [b2 y_eq]]; cbn in *.
        subst.
        rewrite_ex_val a3 x_eq2.
        rewrite_ex_val b3 y_eq2.
        subst.
        apply set_type_eq.
        rewrite x_eq2, y_eq2.
        reflexivity.
    }
    assert (∃ x, Ms x) as Ms_ex.
    {
        exists 0.
        assert (set_type A) as a.
        {
            classic_contradiction contr.
            apply card_false_0 in contr.
            rewrite contr in n_eq.
            change 0 with (nat_to_card 0) in n_eq.
            apply nat_to_card_eq in n_eq.
            symmetry in n_eq; contradiction.
        }
        exists a, a.
        symmetry; apply d_zero.
    }
    pose proof (finite_well_ordered_set_max Ms Ms_fin Ms_ex) as [M [MsM M_max]].
    exists (M + 2).
    intros x y Xx Xy.
    apply sub_A in Xx, Xy.
    destruct Xx as [S1 [[a1 [Aa1 S1_eq]] S1x]]; subst S1.
    destruct Xy as [S2 [[a2 [Aa2 S2_eq]] S2x]]; subst S2.
    unfold open_ball in S1x, S2x; cbn in *.
    assert (Ms (d a1 a2)) as a12_in.
    {
        exists [a1|Aa1], [a2|Aa2].
        reflexivity.
    }
    specialize (M_max (d a1 a2) a12_in).
    pose proof (land S1x) as leq1.
    pose proof (land S2x) as leq2.
    clear - M_max leq1 leq2.
    apply (le_lrplus leq1) in M_max.
    rewrite d_sym in M_max.
    apply (trans (d_tri x a1 a2)) in M_max.
    apply (le_lrplus leq2) in M_max.
    rewrite d_sym in M_max.
    rewrite (d_sym x a2) in M_max.
    apply (trans (d_tri y a2 x)) in M_max.
    rewrite d_sym in M_max.
    do 2 rewrite (plus_comm 1) in M_max.
    rewrite <- plus_assoc in M_max.
    exact M_max.
Qed.

(* begin hide *)
End MetricTopology.

Section RealMetricTopologyEq.

Existing Instance abs_metric.
(* end hide *)
Theorem real_metric_topology_eq :
    @basis_topology _ (@metric_topology _ real_metric) =
    @basis_topology _ real_order_topology.
Proof.
    apply topology_finer_antisym.
    -   apply topology_basis_finer.
        intros x B2.
        rewrite real_open_interval_eq.
        intros [a [b B2_eq]] B2x.
        exists B2.
        split.
        2: split.
        2: exact B2x.
        2: apply refl.
        unfold top_basis; cbn.
        subst B2.
        assert (0 < (b - a)/2) as ε_pos.
        {
            apply half_pos.
            apply lt_plus_0_anb_b_a.
            destruct B2x as [ltq1 ltq2].
            exact (trans ltq1 ltq2).
        }
        exists ((a + b)/2), [_|ε_pos].
        apply antisym.
        +   intros c [ac cb].
            unfold open_ball.
            unfold d; cbn.
            apply abs_lt.
            split.
            *   do 2 rewrite rdist.
                rewrite neg_plus, mult_lneg, neg_neg.
                rewrite plus_comm, <- plus_assoc.
                apply lt_lplus.
                apply lt_plus_lrmove.
                apply lt_plus_rlmove.
                rewrite plus_half.
                exact cb.
            *   do 2 rewrite rdist.
                rewrite mult_lneg.
                rewrite (plus_comm (a/2)), <- plus_assoc.
                apply lt_lplus.
                apply lt_plus_rrmove.
                apply lt_plus_llmove.
                rewrite plus_half.
                exact ac.
        +   intros c c_in.
            unfold open_ball in c_in; cbn in c_in.
            apply abs_lt in c_in.
            destruct c_in as [eq1 eq2].
            do 2 rewrite rdist in eq1, eq2.
            rewrite neg_plus, mult_lneg, neg_neg in eq1.
            rewrite mult_lneg in eq2.
            rewrite plus_comm, <- plus_assoc in eq1.
            rewrite (plus_comm (a/2)), <- plus_assoc in eq2.
            apply lt_plus_lcancel in eq1, eq2.
            apply lt_plus_rrmove in eq1.
            apply lt_plus_llmove in eq1.
            apply lt_plus_lrmove in eq2.
            apply lt_plus_rlmove in eq2.
            do 2 rewrite neg_neg in eq1, eq2.
            rewrite plus_half in eq1, eq2.
            split; assumption.
    -   apply topology_basis_finer.
        intros y S [x [[ε ε_pos] S_eq]] y_in.
        subst S.
        exists (open_ball x [ε|ε_pos]).
        split.
        2: split.
        2: exact y_in.
        2: apply refl.
        rewrite real_open_interval_eq.
        exists (x - ε), (x + ε).
        unfold open_ball, open_interval; cbn.
        apply antisym.
        +   intros c c_in.
            apply abs_lt in c_in.
            destruct c_in as [eq1 eq2].
            apply lt_plus_rrmove in eq1.
            apply lt_plus_llmove in eq1.
            rewrite neg_neg, neg_neg, plus_comm in eq1.
            apply lt_plus_lrmove in eq2.
            apply lt_plus_rlmove in eq2.
            rewrite neg_neg, plus_comm in eq2.
            split; assumption.
        +   intros c c_in.
            apply abs_lt.
            destruct c_in as [eq1 eq2].
            apply lt_plus_lrmove in eq1.
            apply lt_plus_rlmove in eq1.
            rewrite neg_neg, plus_comm in eq1.
            apply lt_plus_rrmove in eq2.
            apply lt_plus_llmove in eq2.
            rewrite plus_comm in eq2.
            split; assumption.
Qed.
(* begin hide *)
End RealMetricTopologyEq.
(* end hide *)
