Require Import init.

Require Import set.
Require Import card.
Require Import real.
Require Import real_sqrt.
Require Import card_types.

(* begin hide *)
Open Scope card_scope.

(* end hide *)
Theorem real_interval_size_base : |set_type (open_interval (-(1)) 1)| = |real|.
Proof.
    assert (∀ x, open_interval (-(1)) 1 x → 0 ≠ 1 - x*x) as lem.
    {
        intros x [x_gt x_lt].
        intros contr.
        rewrite plus_0_anb_b_a in contr.
        apply square_one_one in contr.
        destruct contr; subst.
        -   destruct x_lt; contradiction.
        -   destruct x_gt; contradiction.
    }
    equiv_simpl.
    exists (λ x, [x|] / (1 - [x|]*[x|])).
    split; split.
    -   intros a b eq.
        destruct a as [a [a_gt a_lt]], b as [b [b_gt b_lt]].
        apply set_type_eq.
        cbn in *.
        assert (0 ≠ 1 - a*a) as aa_nz by (apply lem; split; assumption).
        assert (0 ≠ 1 - b*b) as bb_nz by (apply lem; split; assumption).
        apply rmult with (1 - a*a) in eq.
        rewrite mult_rlinv in eq by exact aa_nz.
        rewrite <- mult_assoc, mult_comm in eq.
        apply lmult with (1 - b*b) in eq.
        rewrite mult_assoc in eq.
        rewrite mult_lrinv in eq by exact bb_nz.
        do 2 rewrite rdist in eq.
        do 2 rewrite mult_lid in eq.
        do 2 rewrite mult_lneg in eq.
        apply plus_rlmove in eq.
        rewrite plus_assoc in eq.
        apply plus_lrmove in eq.
        rewrite neg_neg in eq.
        rewrite plus_comm in eq.
        rewrite <- mult_assoc in eq.
        rewrite (mult_comm a b) in eq.
        rewrite <- mult_lneg in eq.
        rewrite <- mult_assoc in eq.
        rewrite <- rdist in eq.
        rewrite <- (neg_neg b) in eq at 2.
        rewrite <- neg_plus in eq.
        rewrite mult_lrneg in eq.
        classic_contradiction contr.
        apply mult_1_a_b_ba in eq.
        2: {
            intros contr2.
            rewrite plus_0_anb_a_b in contr2.
            contradiction.
        }
        assert (0 ≠ a) as a_nz.
        {
            intro; subst a.
            rewrite mult_ranni, neg_zero in eq.
            symmetry in eq.
            apply (not_trivial_one eq).
        }
        rewrite <- mult_lneg in eq.
        apply mult_1_ab_db_a in eq.
        2: exact a_nz.
        apply (f_equal neg) in eq.
        rewrite neg_neg in eq.
        destruct (connex 0 a) as [a_pos|a_neg].
        +   rewrite <- eq in b_gt.
            apply lt_neg in b_gt.
            apply inv_lt_one in a_lt.
            2: split; assumption.
            destruct (trans a_lt b_gt); contradiction.
        +   rewrite <- eq in b_lt.
            apply inv_lt_one in b_lt.
            2: {
                apply neg_pos2.
                apply div_neg.
                rewrite neq_sym in a_nz.
                split; assumption.
            }
            rewrite neg_div in b_lt.
            2: {
                apply div_nz.
                exact a_nz.
            }
            rewrite div_div in b_lt by exact a_nz.
            apply lt_neg in b_lt.
            rewrite neg_neg in b_lt.
            destruct (trans a_gt b_lt); contradiction.
    -   intros y.
        classic_case (0 = y) as [y_z|y_nz].
        1: {
            subst.
            assert (-(1) < 0) as one_neg.
            {
                apply pos_neg2.
                exact one_pos.
            }
            exists [0|make_and one_neg one_pos].
            cbn.
            apply mult_lanni.
        }
        assert (0 ≤ 1 + 4*y*y) as yy_pos.
        {
            rewrite <- (plus_lid 0).
            apply le_lrplus.
            -   apply one_pos.
            -   rewrite <- mult_assoc.
                apply le_mult.
                +   rewrite <- (plus_lid 0).
                    rewrite plus_assoc.
                    apply le_lrplus; apply two_pos.
                +   apply square_pos.
        }
        pose (x := (-(1) + sqrt([1 + 4*y*y|yy_pos])) / (2*y)).
        assert (-(1) < x) as x_gt.
        {
            unfold x.
            destruct (connex 0 y) as [y_pos|y_neg].
            -   apply lt_mult_rcancel_pos with (2*y).
                1: apply double_pos; split; assumption.
                rewrite mult_rlinv.
                2: apply double_pos; split; assumption.
                rewrite mult_lneg, mult_lid.
                apply lt_plus_llmove.
                classic_case (1 - 2*y < 0) as [yyy_neg|yyy_pos].
                +   apply (lt_le_trans yyy_neg).
                    apply sqrt_pos.
                +   rewrite nlt_le in yyy_pos.
                    apply lt_square.
                    1: exact yyy_pos.
                    1: apply sqrt_pos.
                    rewrite sqrt_squares; cbn.
                    rewrite rdist.
                    rewrite mult_lid.
                    rewrite ldist.
                    rewrite mult_rid.
                    rewrite mult_rneg, mult_lneg.
                    rewrite neg_neg.
                    rewrite <- plus_assoc.
                    apply lt_lplus.
                    rewrite <- mult_assoc.
                    rewrite (mult_assoc y).
                    rewrite (mult_comm y 2).
                    do 2 rewrite mult_assoc.
                    rewrite two_times_two.
                    rewrite plus_assoc.
                    rewrite <- (plus_lid (4*y*y)) at 2.
                    apply lt_rplus.
                    rewrite <- neg_plus.
                    apply pos_neg2.
                    rewrite <- rdist.
                    rewrite two_plus_two.
                    apply lt_mult_lcancel_pos with (/4).
                    1: apply div_pos; apply four_pos.
                    rewrite mult_llinv by apply four_pos.
                    rewrite mult_ranni.
                    split; assumption.
            -   rewrite neq_sym in y_nz.
                apply lt_mult_rcancel_neg with (2*y).
                1: apply double_neg; split; assumption.
                rewrite mult_rlinv.
                2: rewrite neq_sym; apply double_neg; split; assumption.
                rewrite mult_lneg, mult_lid.
                apply lt_plus_rlmove.
                apply lt_square.
                1: apply sqrt_pos.
                1: {
                    rewrite <- (plus_rid 0).
                    apply le_lrplus.
                    -   apply one_pos.
                    -   apply neg_pos.
                        apply le_mult_lcancel_pos with (/2).
                        1: apply div_pos; exact two_pos.
                        rewrite mult_llinv by apply two_pos.
                        rewrite mult_ranni.
                        exact y_neg.
                }
                rewrite sqrt_squares; cbn.
                rewrite (rdist _ _ (1 - 2*y)).
                rewrite mult_lid.
                rewrite ldist.
                rewrite mult_rid.
                rewrite mult_rneg, mult_lneg.
                rewrite neg_neg.
                rewrite <- plus_assoc.
                apply lt_lplus.
                rewrite <- (mult_assoc 2).
                rewrite (mult_assoc y).
                rewrite (mult_comm y 2).
                do 2 rewrite mult_assoc.
                rewrite two_times_two.
                rewrite (plus_assoc (-(2*y))).
                rewrite <- (plus_lid (4*y*y)) at 1.
                apply lt_rplus.
                rewrite <- neg_plus.
                apply neg_pos2.
                rewrite <- rdist.
                rewrite two_plus_two.
                apply lt_mult_lcancel_pos with (/4).
                1: apply div_pos; apply four_pos.
                rewrite mult_llinv by apply four_pos.
                rewrite mult_ranni.
                split; assumption.
        }
        assert (x < 1) as x_lt.
        {
            unfold x.
            destruct (connex 0 y) as [y_pos|y_neg].
            -   apply lt_mult_rcancel_pos with (2*y).
                1: apply double_pos; split; assumption.
                rewrite mult_rlinv.
                2: apply double_pos; split; assumption.
                rewrite mult_lid.
                apply lt_plus_rlmove.
                apply lt_square.
                1: apply sqrt_pos.
                1: {
                    rewrite <- (plus_rid 0).
                    apply le_lrplus.
                    -   apply one_pos.
                    -   apply le_mult_lcancel_pos with (/2).
                        1: apply div_pos; exact two_pos.
                        rewrite mult_llinv by apply two_pos.
                        rewrite mult_ranni.
                        exact y_pos.
                }
                rewrite sqrt_squares; cbn.
                rewrite (rdist _ _ (1 + 2*y)).
                rewrite mult_lid.
                rewrite ldist.
                rewrite mult_rid.
                rewrite <- plus_assoc.
                apply lt_lplus.
                rewrite <- (mult_assoc 2).
                rewrite (mult_assoc y).
                rewrite (mult_comm y 2).
                do 2 rewrite mult_assoc.
                rewrite two_times_two.
                rewrite (plus_assoc (2*y)).
                rewrite <- (plus_lid (4*y*y)) at 1.
                apply lt_rplus.
                rewrite <- rdist.
                rewrite two_plus_two.
                apply lt_mult_lcancel_pos with (/4).
                1: apply div_pos; apply four_pos.
                rewrite mult_llinv by apply four_pos.
                rewrite mult_ranni.
                split; assumption.
            -   rewrite neq_sym in y_nz.
                apply lt_mult_rcancel_neg with (2*y).
                1: apply double_neg; split; assumption.
                rewrite mult_rlinv.
                2: rewrite neq_sym; apply double_neg; split; assumption.
                rewrite mult_lid.
                apply lt_plus_llmove.
                classic_case (1 + 2*y < 0) as [yyy_neg|yyy_pos].
                +   apply (lt_le_trans yyy_neg).
                    apply sqrt_pos.
                +   rewrite nlt_le in yyy_pos.
                    apply lt_square.
                    1: exact yyy_pos.
                    1: apply sqrt_pos.
                    rewrite sqrt_squares; cbn.
                    rewrite rdist.
                    rewrite mult_lid.
                    rewrite ldist.
                    rewrite mult_rid.
                    rewrite <- plus_assoc.
                    apply lt_lplus.
                    rewrite <- mult_assoc.
                    rewrite (mult_assoc y).
                    rewrite (mult_comm y 2).
                    do 2 rewrite mult_assoc.
                    rewrite two_times_two.
                    rewrite plus_assoc.
                    rewrite <- (plus_lid (4*y*y)) at 2.
                    apply lt_rplus.
                    rewrite <- rdist.
                    rewrite two_plus_two.
                    apply lt_mult_lcancel_pos with (/4).
                    1: apply div_pos; apply four_pos.
                    rewrite mult_llinv by apply four_pos.
                    rewrite mult_ranni.
                    split; assumption.
        }
        exists [x|make_and x_gt x_lt].
        cbn.
        apply mult_rrmove.
        1: apply lem; split; assumption.
        rewrite ldist, mult_rid.
        unfold x.
        rewrite rdist.
        rewrite ldist.
        rewrite (rdist _ _ (-(1) / (2*y))).
        rewrite (rdist _ _ ((sqrt _) / _)).
        rewrite (mult_comm (sqrt _)) at 4.
        rewrite <- (mult_assoc (/(2*y))).
        rewrite (mult_assoc (sqrt _) _ (/(2*y))).
        rewrite sqrt_squares; cbn.
        rewrite mult_rneg.
        rewrite (mult_comm (sqrt _ / _)).
        rewrite <- plus_assoc.
        rewrite (plus_assoc _ _ (/(2 * y) * _)).
        rewrite (plus_two (_ * (sqrt _ / _))).
        rewrite (rdist 1 (4*y*y)).
        rewrite (ldist (/(2*y))).
        rewrite mult_lneg.
        rewrite mult_rneg.
        rewrite mult_lneg.
        rewrite neg_neg.
        rewrite mult_lid.
        rewrite (plus_assoc (/(2*y) / _)).
        rewrite (plus_comm (/(2*y) / _)).
        rewrite <- (plus_assoc _ (/(2*y) / _)).
        rewrite (plus_assoc (/(2*y) / _)).
        rewrite (plus_two (/(2*y) / _)).
        rewrite ldist.
        rewrite ldist.
        rewrite <- two_times_two at 3.
        rewrite <- (mult_assoc 2 2).
        rewrite (mult_comm 2 (2*y)).
        rewrite <- (mult_assoc (2 * y)).
        assert (0 ≠ 2*y) as y2_nz.
        {
            intros contr.
            apply mult_rlmove in contr.
            2: apply two_pos.
            rewrite mult_ranni in contr.
            contradiction.
        }
        rewrite mult_rrinv by exact y2_nz.
        rewrite mult_linv, mult_rid by exact y2_nz.
        do 2 rewrite (mult_assoc y 2).
        rewrite (mult_comm y 2).
        rewrite mult_lrinv by exact y2_nz.
        rewrite mult_lneg.
        rewrite mult_rneg.
        rewrite mult_lrinv by exact y2_nz.
        rewrite neg_plus, neg_plus, neg_neg.
        rewrite (plus_comm (sqrt _ / _)).
        rewrite plus_assoc.
        apply rplus.
        rewrite (plus_comm y).
        rewrite plus_rlinv.
        reflexivity.
Qed.

Theorem real_open_interval_size : ∀ a b, a < b →
    |set_type (open_interval a b)| = |real|.
Proof.
    intros a b ab.
    rewrite <- real_interval_size_base.
    equiv_simpl.
    pose (f (x : set_type (open_interval a b)) := 2 * ([x|] - a) / (b - a) - 1).
    apply lt_plus_0_anb_b_a in ab.
    assert (∀ x, open_interval (-(1)) 1 (f x)) as f_in.
    {
        intros [x [x_gt x_lt]].
        unfold f; cbn.
        split.
        -   rewrite <- (plus_lid (-(1))) at 1.
            apply lt_rplus.
            apply lt_mult_rcancel_pos with (b - a).
            1: exact ab.
            rewrite mult_lanni.
            rewrite mult_rlinv by apply ab.
            apply lt_mult_lcancel_pos with (/2).
            1: apply div_pos; exact two_pos.
            rewrite mult_ranni.
            rewrite mult_llinv by apply two_pos.
            apply lt_plus_0_anb_b_a.
            exact x_gt.
        -   apply lt_plus_rrmove.
            apply lt_mult_rrmove_pos.
            1: exact ab.
            do 2 rewrite ldist.
            apply lt_rplus.
            apply lt_lmult_pos.
            1: exact two_pos.
            exact x_lt.
    }
    exists (λ x, [f x|f_in x]).
    split; split.
    -   intros [x [x_gt x_lt]] [y [y_gt y_lt]] eq.
        apply set_type_eq in eq; cbn in eq.
        unfold f in eq; cbn in eq.
        apply set_type_eq; cbn.
        apply plus_rcancel in eq.
        apply mult_rcancel in eq.
        2: apply div_pos; exact ab.
        apply mult_lcancel in eq.
        2: apply two_pos.
        apply plus_rcancel in eq.
        exact eq.
    -   intros [y [y_gt y_lt]].
        pose (x := (y + 1) * (b - a) / 2 + a).
        assert (open_interval a b x) as x_in.
        {
            unfold x.
            split.
            -   rewrite <- (plus_lid a) at 1.
                apply lt_rplus.
                apply lt_mult_rcancel_pos with 2.
                1: exact two_pos.
                rewrite mult_rlinv by apply two_pos.
                rewrite mult_lanni.
                apply lt_mult_rcancel_pos with (/(b - a)).
                1: apply div_pos; exact ab.
                rewrite mult_lanni.
                rewrite mult_rrinv by apply ab.
                apply lt_plus_0_ab_nb_a in y_gt.
                exact y_gt.
            -   apply lt_plus_rcancel with (-a).
                rewrite plus_rrinv.
                rewrite mult_comm.
                rewrite mult_assoc.
                rewrite <- (mult_lid (b - a)) at 2.
                apply lt_rmult_pos.
                1: exact ab.
                apply lt_mult_lcancel_pos with 2.
                1: exact two_pos.
                rewrite mult_lrinv by apply two_pos.
                rewrite mult_rid.
                apply lt_plus_rcancel with (-(1)).
                do 2 rewrite plus_rrinv.
                exact y_lt.
        }
        exists [x|x_in].
        unfold f, x; cbn.
        apply set_type_eq; cbn.
        rewrite plus_rrinv.
        rewrite <- (mult_assoc _ _ (/2)).
        rewrite (mult_comm _ (/2)).
        do 2 rewrite <- mult_assoc.
        rewrite mult_rrinv by apply ab.
        rewrite mult_comm.
        rewrite mult_rlinv by apply two_pos.
        rewrite plus_rrinv.
        reflexivity.
Qed.

Theorem real_closed_interval_size : ∀ a b, a < b →
    |set_type (closed_interval a b)| = |real|.
Proof.
    intros a b ab.
    rewrite <- (real_open_interval_size a b ab).
    assert (|set_type (closed_interval a b)|
        = |set_type (open_interval a b)| + 2) as eq.
    {
        symmetry.
        rewrite <- (homo_one (f := from_nat)).
        rewrite <- homo_plus.
        rewrite from_nat_card.
        unfold plus; equiv_simpl.
        assert (∀ x : set_type (open_interval a b), closed_interval a b [x|])
            as x_in.
        {
            intros [x [x_gt x_lt]].
            split.
            -   apply x_gt.
            -   apply x_lt.
        }
        assert (closed_interval a b a) as a_in.
        {
            split.
            -   apply refl.
            -   apply ab.
        }
        assert (closed_interval a b b) as b_in.
        {
            split.
            -   apply ab.
            -   apply refl.
        }
        exists (λ x, match x with
        | inl x' => [[x'|]|x_in x']
        | inr n => match [n|] with
            | nat_zero => [a|a_in]
            | _ => [b|b_in]
            end
        end).
        split; split.
        -   intros [x|x] [y|y] eq.
            +   apply set_type_eq in eq; cbn in eq.
                apply set_type_eq in eq.
                rewrite eq.
                reflexivity.
            +   nat_destruct [y|].
                *   apply set_type_eq in eq; cbn in eq.
                    destruct x as [x [x_gt x_lt]]; cbn in *.
                    exfalso; rewrite <- eq in x_gt.
                    destruct x_gt; contradiction.
                *   apply set_type_eq in eq; cbn in eq.
                    destruct x as [x [x_gt x_lt]]; cbn in *.
                    exfalso; rewrite <- eq in x_lt.
                    destruct x_lt; contradiction.
            +   nat_destruct [x|].
                *   apply set_type_eq in eq; cbn in eq.
                    destruct y as [y [y_gt y_lt]]; cbn in *.
                    exfalso; rewrite <- eq in y_gt.
                    destruct y_gt; contradiction.
                *   apply set_type_eq in eq; cbn in eq.
                    destruct y as [y [y_gt y_lt]]; cbn in *.
                    exfalso; rewrite <- eq in y_lt.
                    destruct y_lt; contradiction.
            +   destruct x as [x x_lt], y as [y y_lt]; cbn in *.
                apply f_equal.
                apply set_type_eq; cbn.
                nat_destruct x; nat_destruct y.
                all: apply set_type_eq in eq; cbn in eq.
                *   reflexivity.
                *   subst.
                    destruct ab; contradiction.
                *   subst.
                    destruct ab; contradiction.
                *   apply f_equal.
                    unfold initial_segment in x_lt, y_lt.
                    rewrite nat_sucs_lt in x_lt, y_lt.
                    apply nat_lt_one_eq in x_lt, y_lt.
                    subst.
                    reflexivity.
        -   intros [y [y_gt y_lt]].
            classic_case (a = y) as [ay|ay].
            2: classic_case (y = b) as [yb|yb].
            +   assert (0 < nat_suc 1) as zero_two.
                {
                    split.
                    -   exact true.
                    -   intro contr; inversion contr.
                }
                exists (inr [0|zero_two]).
                unfold zero; cbn.
                apply set_type_eq; cbn.
                exact ay.
            +   assert (1 < nat_suc 1) as one_two.
                {
                    split.
                    -   exact true.
                    -   intro contr; inversion contr.
                }
                exists (inr [1|one_two]).
                unfold one; cbn.
                apply set_type_eq; cbn.
                symmetry; exact yb.
            +   exists (inl [y|make_and (make_and y_gt ay) (make_and y_lt yb)]).
                apply set_type_eq; cbn.
                reflexivity.
    }
    rewrite eq.
    rewrite card_plus_lmax.
    -   reflexivity.
    -   apply (dense_open_infinite _ _ ab).
    -   rewrite <- (homo_one (f := from_nat)).
        rewrite <- homo_plus.
        rewrite real_open_interval_size by exact ab.
        apply (lt_le_trans (nat_is_finite 2)).
        unfold le; equiv_simpl.
        exists from_nat.
        exact from_nat_inj.
Qed.

(* begin hide *)
Close Scope card_scope.

(* end hide *)
