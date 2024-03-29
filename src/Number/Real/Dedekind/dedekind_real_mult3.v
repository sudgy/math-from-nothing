Require Import init.

Require Import rat.
Require Import set.
Require Import nat.
Require Import int. (* Get rid of this later *)

Require Export dedekind_real_base.
Require Import dedekind_real_order.
Require Import dedekind_real_plus.
Require Import dedekind_real_mult1.
Require Import dedekind_real_mult2.

(** This file contains the definition of division *)

Open Scope real_scope.

Definition real_div_base (a : rat → Prop) := λ p, p ≤ 0 ∨ (∃ r, 0 < r ∧ ¬(a (div p + -r))).
Notation "⊘ a" := (real_div_base a) : real_scope.

Lemma real_div_dedekind : ∀ a : real, 0 < a → dedekind_cut (⊘ [a|]).
Proof.
    intros [a a_cut] a_pos; cbn.
    pose proof (gt_rat_to_real_in _ _ a_pos) as a0; cbn in a0.
    split.
    2: split.
    3: split.
    -   intro contr.
        pose proof (rand (rand (rand a_cut)) _ a0) as [u [au u_pos]].
        assert (all (div u)) as u_in by exact true.
        rewrite <- contr in u_in.
        unfold real_div_base in u_in.
        destruct u_in as [u_neg|u_in].
        +   apply div_pos in u_pos.
            pose proof (lt_le_trans u_pos u_neg) as [C0 C1]; contradiction.
        +   destruct u_in as [r [r_pos na]].
            rewrite div_div in na by apply u_pos.
            pose proof (dedekind_lt a a_cut _ _ au na) as ltq.
            apply lt_plus_0_a_b_ba in ltq.
            apply pos_neg2 in r_pos.
            destruct (trans r_pos ltq); contradiction.
    -   apply empty_neq.
        exists (-(1)).
        left.
        rewrite <- pos_neg.
        apply one_pos.
    -   intros l u nau lu.
        classic_case (l ≤ 0) as [l_neg|l_pos].
        +   left; exact l_neg.
        +   rewrite nle_lt in l_pos.
            right.
            destruct nau as [u_neg|nau].
            *   destruct (trans l_pos (lt_le_trans lu u_neg)); contradiction.
            *   destruct nau as [r [r_pos nau]].
                exists r.
                split; try exact r_pos.
                intros contr.
                pose proof (dedekind_lt a a_cut _ _ contr nau) as ltq.
                apply lt_plus_rcancel in ltq.
                apply lt_div_pos in lu; try assumption.
                pose proof (trans ltq lu) as [C0 C1]; contradiction.
    -   intros l al.
        classic_case (l ≤ 0) as [l_neg|l_pos].
        +   pose proof (land a_cut) as u_ex.
            apply all_neq in u_ex.
            destruct u_ex as [u nau].
            assert (0 < u + 1) as u1_pos.
            {
                pose proof (dedekind_lt a a_cut _ _ a0 nau) as u_pos.
                apply (lt_lrplus one_pos) in u_pos.
                rewrite plus_lid, plus_comm in u_pos.
                exact u_pos.
            }
            exists (div (u + 1)).
            split.
            *   right.
                exists 1.
                split; try exact one_pos.
                rewrite div_div.
                2: apply u1_pos.
                rewrite plus_rrinv.
                exact nau.
            *   apply div_pos in u1_pos.
                exact (le_lt_trans l_neg u1_pos).
        +   destruct al as [l_neg|al]; try contradiction.
            rewrite nle_lt in l_pos.
            destruct al as [r [r_pos na]].
            unfold real_div_base.
            assert (¬(div l + -(r * div 2) < div l + -r)) as make_contr.
            {
                intros ltq.
                apply lt_plus_lcancel in ltq.
                apply lt_neg in ltq.
                apply lt_rmult_pos with 2 in ltq.
                2: exact two_pos.
                rewrite mult_rlinv in ltq by apply two_pos.
                rewrite ldist, mult_rid in ltq.
                apply lt_plus_a_0_ba_b in ltq.
                pose proof (trans ltq r_pos) as [C0 C1]; contradiction.
            }
            exists (/ (/ l + - (r / 2))).
            split.
            *   right.
                exists (r / 2).
                split.
                --  apply lt_mult_rcancel_pos with 2.
                    1: exact two_pos.
                    rewrite mult_rlinv by apply two_pos.
                    rewrite mult_lanni.
                    exact r_pos.
                --  rewrite div_div.
                    ++  rewrite <- plus_assoc, <- neg_plus.
                        rewrite plus_half.
                        exact na.
                    ++  intro contr.
                        rewrite contr in a0.
                        pose proof (dedekind_lt a a_cut _ _ a0 na) as ltq.
                        exact (make_contr ltq).
            *   rewrite <- (div_div l) at 1.
                2: apply l_pos.
                apply lt_div_pos.
                --  apply (dedekind_lt a a_cut _ _); try exact a0.
                    intro contr.
                    pose proof (dedekind_lt a a_cut _ _ contr na) as ltq.
                    exact (make_contr ltq).
                --  rewrite <- (plus_rid (div l)) at 2.
                    apply lt_lplus.
                    apply pos_neg2.
                    apply half_pos.
                    exact r_pos.
Qed.

Global Instance real_div : Div real := {
    div a :=
    match (trichotomy 0 a) with
    | semi_or_left comps =>
        match comps with
        | strong_or_left comp => [_|real_div_dedekind a comp]
        | strong_or_right comp => 0
        end
    | semi_or_right comp => -[_|real_div_dedekind (-a) (land (neg_pos2 _) comp)]
    end
}.

Lemma real_div_pos : ∀ a, 0 < a → 0 < div a.
Proof.
    intros a a_pos.
    unfold div; cbn.
    destruct (trichotomy 0 a) as [[a_pos'|a_z]|a_neg].
    -   split.
        +   intros x x_neg.
            left.
            apply x_neg.
        +   destruct a as [a a_cut]; cbn.
            intros contr.
            unfold zero in contr; cbn in contr.
            unfold rat_to_real in contr.
            inversion contr as [eq].
            clear contr.
            unfold rat_to_real_base in eq.
            assert ((⊘ a) 0) as a0.
            {
                left.
                apply refl.
            }
            rewrite <- eq in a0.
            destruct a0; contradiction.
    -   subst.
        destruct a_pos; contradiction.
    -   destruct (trans a_pos a_neg); contradiction.
Qed.
Lemma real_div_neg : ∀ a, 0 < a → -(div a) = div (-a).
Proof.
    intros a a_pos.
    unfold div; cbn.
    destruct (trichotomy 0 a) as [[a_pos'|a_z]|a_neg]; cbn.
    1: apply pos_neg2 in a_pos.
    1: destruct (trichotomy 0 (-a)) as [[na_pos|na_z]|na_neg]; cbn.
    -   pose proof (trans a_pos na_pos) as [C0 C1]; contradiction.
    -   rewrite na_z in a_pos; destruct a_pos; contradiction.
    -   unfold neg at 1 2; cbn.
        apply set_type_eq; cbn.
        rewrite neg_neg.
        reflexivity.
    -   rewrite <- a_z in a_pos; destruct a_pos; contradiction.
    -   pose proof (trans a_pos a_neg) as [C0 C1]; contradiction.
Qed.
Lemma real_mult_linv1 : ∀ a, 0 < a → div a * a = 1.
Proof.
    intros a a_pos.
    pose proof [|div a] as a'_cut.
    unfold div in a'_cut; cbn in a'_cut.
    pose proof (real_div_pos a a_pos) as a'_pos.
    pose proof (gt_rat_to_real_in _ _ a'_pos) as H.
    unfold div in H; cbn in H.
    apply set_type_eq.
    rewrite real_mult_pos_pos.
    2: apply a'_pos.
    2: apply a_pos.
    unfold div; cbn.
    destruct (trichotomy 0 a) as [[a_pos'|a_z]|a_neg]; cbn in *.
    -   destruct a as [a a_cut]; cbn in *.
        apply predicate_ext; intros x; split.
        +   intros [x_neg|x_in].
            {
                exact (trans x_neg one_pos).
            }
            destruct x_in as [r [s [nar [as_ [r_pos [s_pos eq]]]]]].
            subst x.
            classic_case (0 = s) as [s_z|s_nz].
            {
                subst.
                rewrite mult_ranni.
                exact one_pos.
            }
            assert (¬(⊘ a) (div s)) as ns.
            {
                intros [s_neg|nas].
                -   pose proof (div_pos (make_and s_pos s_nz)) as ltq.
                    destruct (le_lt_trans s_neg ltq); contradiction.
                -   destruct nas as [ε [ε_pos nas]].
                    rewrite div_div in nas by exact s_nz.
                    pose proof (dedekind_lt _ a_cut _ _ as_ nas) as ltq.
                    apply lt_plus_0_a_b_ba in ltq.
                    apply pos_neg2 in ε_pos.
                    destruct (trans ltq ε_pos); contradiction.
            }
            pose proof (dedekind_lt _ a'_cut _ _ nar ns) as ltq.
            apply lt_rmult_pos with s in ltq.
            2: split; assumption.
            rewrite mult_linv in ltq by exact s_nz.
            exact ltq.
        +   intros x_lt.
            destruct (trichotomy x 0) as [[x_neg|x_z]|x_pos].
            {
                left; exact x_neg.
            }
            {
                subst.
                right; exists 0, 0.
                repeat split.
                -   exact H.
                -   apply (gt_rat_to_real_in _ _ a_pos).
                -   apply refl.
                -   apply refl.
                -   rewrite mult_ranni.
                    reflexivity.
            }
            assert (∃ n, 0 ≠ n ∧ x < from_nat n * div (from_nat n + 1)) as
                [n [n_nz n_eq]].
            {
                unfold one in x_lt; cbn in x_lt.
                unfold rat_to_real_base in x_lt.
                pose proof x_lt as ε_pos.
                apply lt_plus_0_anb_b_a in ε_pos.
                pose proof (archimedean2 _ ε_pos) as [m eq].
                (*rewrite from_nat_rat in eq.*)
                assert ((0 : rat) < from_nat (nat_suc m)) as n_pos.
                {
                    apply from_nat_pos.
                }
                remember (from_nat (nat_suc m) : rat) as n.
                apply lt_lmult_pos with n in eq.
                2: exact n_pos.
                rewrite mult_rinv in eq by apply n_pos.
                apply (trans x_lt) in eq.
                rewrite <- (plus_lid x) in eq at 1.
                rewrite <- (plus_rinv 1) in eq.
                rewrite <- (neg_neg x) in eq at 1.
                rewrite <- plus_assoc, <- neg_plus in eq.
                apply lt_rplus with (1 + -x) in eq.
                rewrite plus_rlinv in eq.
                rewrite <- (mult_lid (1 + -x)) in eq at 2.
                rewrite <- rdist in eq.
                apply (lt_lrplus one_pos) in n_pos.
                rewrite plus_lid, plus_comm in n_pos.
                apply lt_mult_rlmove_pos in eq.
                2: exact n_pos.
                rewrite mult_rid in eq.
                apply lt_plus_rrmove in eq.
                rewrite neg_neg in eq.
                apply lt_plus_llmove in eq.
                rewrite <- (mult_rinv (n + 1)) in eq at 2 by apply n_pos.
                rewrite <- (mult_lid (div (n + 1))) in eq at 1.
                rewrite <- mult_lneg in eq.
                rewrite <- rdist in eq.
                rewrite (plus_comm n 1) in eq at 1.
                rewrite plus_llinv in eq.
                exists (nat_suc m).
                rewrite <- Heqn.
                split.
                -   intros contr; inversion contr.
                -   exact eq.
            }
            rename n into n'; remember (from_nat n') as n.
            pose proof (gt_rat_to_real_in _ _ a_pos) as a0; cbn in a0.
            apply (rand (rand (rand a_cut))) in a0 as [u [au u_pos]].
            assert (∃ q, 0 < q ∧ q < u / n) as [q [q_pos q_lt]].
            {
                apply dense.
                apply lt_mult; try assumption.
                apply div_pos.
                rewrite Heqn.
                split.
                -   apply from_nat_pos2.
                -   apply (inj_zero from_nat).
                    exact n_nz.
            }
            pose (S m := ¬a (m × q)).
            assert (∃ m, S m) as S_ex.
            {
                clear - a_cut q_pos a_pos.
                pose proof (land a_cut) as u_ex.
                apply all_neq in u_ex as [u nau].
                pose proof (gt_rat_to_real_in _ _ a_pos) as a0; cbn in a0.
                pose proof (dedekind_lt a a_cut _ _ a0 nau) as u_pos.
                pose proof (archimedean u q u_pos q_pos) as [m eq].
                exists m.
                unfold S.
                intros contr.
                pose proof (dedekind_lt a a_cut _ _ contr nau) as ltq.
                destruct (trans eq ltq); contradiction.
            }
            pose proof (well_ordered S S_ex) as [m [nam m_least]].
            unfold S in *; clear S S_ex.
            nat_destruct m.
            {
                unfold zero in nam; cbn in nam.
                pose proof (gt_rat_to_real_in _ _ a_pos) as a0; cbn in a0.
                contradiction.
            }
            assert (a (m × q)) as am.
            {
                classic_contradiction contr.
                specialize (m_least _ contr).
                destruct (le_lt_trans m_least (nat_lt_suc m)); contradiction.
            }
            clear m_least.
            rewrite nat_mult_from in am.
            rename m into m'; remember (from_nat m') as m.
            assert (x < m / (m + 1)) as m_eq.
            {
                assert (0 < m + 1) as m1_pos.
                {
                    rewrite Heqm.
                    rewrite <- (homo_zero (f := from_nat)).
                    rewrite <- (homo_one (f := from_nat)).
                    rewrite <- homo_plus.
                    rewrite <- homo_lt2.
                    rewrite plus_comm.
                    apply nat_pos2.
                }
                assert (0 < n) as n_pos.
                {
                    rewrite Heqn.
                    rewrite <- (homo_zero (f := from_nat)).
                    rewrite <- homo_lt2.
                    split; try exact n_nz.
                    apply nat_pos.
                }
                assert (0 < n + 1) as n1_pos.
                {
                    apply (lt_lrplus one_pos) in n_pos.
                    rewrite plus_lid, plus_comm in n_pos.
                    exact n_pos.
                }
                assert (n ≤ m) as mn.
                {
                    classic_contradiction contr.
                    rewrite nle_lt in contr.
                    apply lt_rmult_pos with (m + 1) in q_lt.
                    2: exact m1_pos.
                    rewrite Heqm, Heqn in contr.
                    rewrite <- homo_lt2 in contr.
                    rewrite <- nat_sucs_lt in contr.
                    rewrite nat_lt_suc_le in contr.
                    rewrite homo_le2 in contr.
                    replace (nat_suc m') with (1 + m') in contr by reflexivity.
                    rewrite plus_comm in contr.
                    rewrite (homo_plus (f := from_nat)) in contr.
                    rewrite (homo_one (f := from_nat)) in contr.
                    rewrite <- Heqm, <- Heqn in contr.
                    apply le_mult_adb_1_a_b_pos in contr.
                    2: exact n_pos.
                    rewrite mult_comm in contr.
                    apply le_lmult_pos with u in contr.
                    2: apply u_pos.
                    rewrite mult_assoc, mult_rid in contr.
                    pose proof (lt_le_trans q_lt contr) as ltq.
                    pose proof (land (rand (rand a_cut)) _ _ au ltq).
                    rewrite nat_mult_from in nam.
                    change (nat_suc m') with (1 + m') in nam.
                    rewrite plus_comm in nam.
                    rewrite homo_plus in nam.
                    rewrite <- Heqm in nam.
                    rewrite homo_one in nam.
                    rewrite mult_comm in nam.
                    contradiction.
                }
                apply (lt_le_trans n_eq).
                rewrite <- le_mult_rrmove_pos by exact n1_pos.
                rewrite mult_comm, mult_assoc.
                apply le_mult_lrmove_pos.
                1: exact m1_pos.
                rewrite ldist, rdist.
                rewrite mult_lid, mult_rid.
                apply le_lplus.
                exact mn.
            }
            nat_destruct m'.
            {
                rewrite nat_mult_lid in nam.
                pose proof (dedekind_lt a a_cut _ _ au nam) as ltq1.
                pose proof (trans ltq1 q_lt) as ltq.
                exfalso.
                clear - u_pos ltq Heqn n_nz.
                apply lt_plus_0_anb_b_a in ltq.
                rewrite <- (mult_rid u) in ltq at 2.
                rewrite <- mult_rneg in ltq.
                rewrite <- ldist in ltq.
                apply lt_mult_rlmove_pos in ltq.
                2: exact u_pos.
                rewrite mult_ranni in ltq.
                apply lt_lplus with 1 in ltq.
                rewrite plus_rid in ltq.
                rewrite plus_comm in ltq.
                rewrite plus_rlinv in ltq.
                apply inv_gt_one in ltq.
                subst n.
                rewrite div_div in ltq.
                2: {
                    intro contr.
                    rewrite <- (homo_zero (f := from_nat)) in contr.
                    apply inj in contr.
                    contradiction.
                }
                rewrite <- (homo_one (f := from_nat)) in ltq.
                rewrite <- homo_lt2 in ltq.
                apply n_nz.
                apply antisym.
                -   apply nat_pos.
                -   rewrite <- nat_lt_suc_le.
                    exact ltq.
            }
            assert (0 < m) as m_pos.
            {
                rewrite Heqm.
                rewrite <- (homo_zero (f := from_nat)).
                rewrite <- homo_lt2.
                apply nat_pos2.
            }
            pose proof (lt_lrplus m_pos one_pos) as m1_pos.
            rewrite plus_lid in m1_pos.
            pose proof (lt_mult m_pos q_pos) as mq_pos.
            right.
            exists (x / (m * q)), (m * q).
            repeat split.
            *   right.
                rewrite nat_mult_from in nam.
                change (nat_suc (nat_suc m')) with (1 + nat_suc m') in nam.
                rewrite homo_plus in nam.
                rewrite <- Heqm in nam.
                rewrite homo_one in nam.
                rewrite plus_comm in nam.
                apply lt_rmult_pos with (m + 1) in m_eq.
                2: exact m1_pos.
                rewrite mult_rlinv in m_eq by apply m1_pos.
                apply lt_mult_llmove_pos in m_eq.
                2: apply x_pos.
                apply lt_rmult_pos with q in m_eq.
                2: exact q_pos.
                rewrite <- mult_assoc in m_eq.
                apply lt_plus_0_anb_b_a in m_eq.
                exists (/ x * (m * q) - (m + 1) * q).
                split.
                1: exact m_eq.
                rewrite div_mult.
                2: apply x_pos.
                2: apply div_nz; apply mq_pos.
                rewrite div_div by apply mq_pos.
                rewrite neg_plus, neg_neg.
                rewrite plus_lrinv.
                exact nam.
            *   exact am.
            *   apply le_mult.
                --  apply x_pos.
                --  apply div_pos.
                    apply mq_pos.
            *   apply mq_pos.
            *   rewrite mult_rlinv by apply mq_pos.
                reflexivity.
    -   rewrite <- a_z in a_pos; destruct a_pos; contradiction.
    -   pose proof (trans a_pos a_neg) as [C0 C1]; contradiction.
Qed.
Lemma real_mult_linv_ : ∀ a, 0 ≠ a → div a * a = 1.
Proof.
    intros a a_neq.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply real_mult_linv1.
        split; assumption.
    -   rewrite neq_sym in a_neq.
        assert (a < 0) as a_neg' by (split; assumption).
        apply neg_pos2 in a_neg'.
        rewrite <- (neg_neg a).
        rewrite <- real_div_neg by exact a_neg'.
        rewrite mult_rneg, mult_lneg.
        rewrite neg_neg.
        apply real_mult_linv1.
        exact a_neg'.
Qed.
Global Instance real_mult_linv : MultLinv real := {
    mult_linv := real_mult_linv_
}.

Lemma real_not_trivial_ : 0 ≠ 1.
Proof.
    intro contr.
    assert ([(one (U := real))|] (zero (U := rat))) by exact one_pos.
    rewrite <- contr in H.
    destruct H; contradiction.
Qed.
Global Instance real_not_trivial : NotTrivial real := {
    not_trivial := real_not_trivial_;
}.

(* begin hide *)
Close Scope real_scope.
(* end hide *)
