Require Import init.

Require Import rat.
Require Import set.

Require Export dedekind_real_base.
Require Import dedekind_real_order.
Require Import dedekind_real_plus.
Require Import dedekind_real_mult1.

(** This file contains the proofs up to showing that the real numbers form a
ring.
*)
(* begin hide *)
Open Scope real_scope.
(* end hide *)
Lemma real_mult_assoc0 : ∀ a b c, 0 <= a → 0 <= b → 0 <= c →
    ([a|] ⊗ ([b|] ⊗ [c|]) ⊆ ([a|] ⊗ [b|]) ⊗ [c|])%set.
Proof.
    intros [a a_cut] [b b_cut] [c c_cut] a_pos b_pos c_pos; cbn.
    intros x.
    intros [x_lt|[r [s [ar [eq1 eq2]]]]]; try (left; exact x_lt).
    destruct eq2 as [r_pos [s_pos eq2]].
    destruct eq1 as [s_neg|[r' [s' [br' [cs' [r'_pos [s'_pos eq1]]]]]]].
    1: pose proof (lt_le_trans s_neg s_pos) as [C0 C1]; contradiction.
    right.
    exists (r * r'), s'.
    repeat split; try assumption.
    +   right.
        exists r, r'.
        repeat split; trivial.
    +   apply le_mult; assumption.
    +   rewrite eq1 in eq2.
        rewrite mult_assoc in eq2.
        exact eq2.
Qed.
Lemma real_mult_assoc1 : ∀ a b c, 0 <= a → 0 <= b → 0 <= c →
    a * (b * c) = (a * b) * c.
Proof.
    intros a b c a_pos b_pos c_pos.
    apply set_type_eq.
    pose proof (le_mult _ _ a_pos b_pos).
    pose proof (le_mult _ _ b_pos c_pos).
    apply antisym.
    -   do 4 rewrite real_mult_pos_pos by assumption.
        apply real_mult_assoc0; assumption.
    -   rewrite (mult_comm a b).
        rewrite (mult_comm _ c).
        rewrite (mult_comm a _).
        rewrite (mult_comm b c).
        rewrite mult_comm in H, H0.
        do 4 rewrite real_mult_pos_pos by assumption.
        apply real_mult_assoc0; assumption.
Qed.
Lemma real_mult_assoc2 : ∀ a b c, 0 <= a → 0 <= b → a * (b * c) = (a * b) * c.
Proof.
    intros a b c a_pos b_pos.
    destruct (connex 0 c) as [c_pos|c_neg].
    -   apply real_mult_assoc1; assumption.
    -   rewrite (real_mult_pos_neg _ c) by assumption.
        rewrite (real_mult_pos_neg _ c) by (try apply le_mult; assumption).
        apply neg_pos in c_neg.
        rewrite (real_mult_pos_neg a _); try assumption.
        2: apply pos_neg; apply le_mult; assumption.
        rewrite neg_neg.
        apply f_equal.
        apply real_mult_assoc1; assumption.
Qed.
Lemma real_mult_assoc3 : ∀ a b c, 0 <= a → a * (b * c) = (a * b) * c.
Proof.
    intros a b c a_pos.
    destruct (connex 0 b) as [b_pos|b_neg].
    -   apply real_mult_assoc2; assumption.
    -   rewrite (real_mult_neg_any b c) by exact b_neg.
        rewrite (real_mult_any_neg a b) by exact b_neg.
        rewrite real_mult_rneg.
        rewrite (real_mult_lneg (a * -b) c).
        apply f_equal.
        apply neg_pos in b_neg.
        apply real_mult_assoc2; assumption.
Qed.
Lemma real_mult_assoc_ : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
    intros a b c.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply real_mult_assoc3; assumption.
    -   rewrite (real_mult_neg_any a) by exact a_neg.
        rewrite (real_mult_neg_any a) by exact a_neg.
        rewrite (real_mult_lneg _ c).
        apply f_equal.
        apply neg_pos in a_neg.
        apply real_mult_assoc3; assumption.
Qed.
Global Instance real_mult_assoc : MultAssoc real := {
    mult_assoc := real_mult_assoc_;
}.

Lemma real_ldist1 : ∀ a b c, 0 <= a → 0 <= b → 0 <= c →
    a * (b + c) = a * b + a * c.
Proof.
    intros a b c a_pos b_pos c_pos.
    classic_case (0 = a) as [a_z|a_nz].
    {
        subst.
        do 3 rewrite real_mult_lanni.
        rewrite plus_rid.
        reflexivity.
    }
    classic_case (0 = b) as [b_z|b_nz].
    {
        subst.
        rewrite real_mult_ranni.
        do 2 rewrite plus_lid.
        reflexivity.
    }
    classic_case (0 = c) as [c_z|c_nz].
    {
        subst.
        rewrite real_mult_ranni.
        do 2 rewrite plus_rid.
        reflexivity.
    }
    pose proof (le_lrplus b_pos c_pos) as bc_pos.
    rewrite plus_lid in bc_pos.
    apply set_type_eq.
    unfold plus; cbn.
    do 3 rewrite real_mult_pos_pos by assumption.
    cbn.
    apply predicate_ext; intros x; split.
    -   intros [x_neg|[r [s[ar[[r'[s'[br'[cs' eq1]]]] [r_pos [s_pos eq2]]]]]]].
        +   exists x, 0.
            repeat split.
            *   left; exact x_neg.
            *   right.
                exists 0, 0.
                repeat split.
                1, 2: apply gt_rat_to_real_in; split; assumption.
                1, 2: apply refl.
                rewrite mult_lanni; reflexivity.
            *   rewrite plus_rid.
                reflexivity.
        +   classic_case (0 = r) as [r_z|r_nz].
            {
                subst.
                exists 0, 0.
                repeat split.
                -   right.
                    exists 0, 0.
                    repeat split.
                    1, 2: apply gt_rat_to_real_in; split; assumption.
                    1, 2: apply refl.
                    rewrite mult_lanni; reflexivity.
                -   right.
                    exists 0, 0.
                    repeat split.
                    1, 2: apply gt_rat_to_real_in; split; assumption.
                    1, 2: apply refl.
                    rewrite mult_lanni; reflexivity.
                -   rewrite mult_lanni, plus_rid.
                    reflexivity.
            }
            exists (r * r'), (r * s').
            repeat split.
            *   classic_case (0 <= r') as [r'_pos|r'_neg].
                --  right.
                    exists r, r'.
                    repeat split; assumption.
                --  left.
                    rewrite nle_lt in r'_neg.
                    apply lt_lmult_pos with r in r'_neg.
                    2: split; assumption.
                    rewrite mult_ranni in r'_neg.
                    exact r'_neg.
            *   classic_case (0 <= s') as [s'_pos|s'_neg].
                --  right.
                    exists r, s'.
                    repeat split; assumption.
                --  left.
                    rewrite nle_lt in s'_neg.
                    apply lt_lmult_pos with r in s'_neg.
                    2: split; assumption.
                    rewrite mult_ranni in s'_neg.
                    exact s'_neg.
            *   rewrite eq1 in eq2.
                rewrite ldist in eq2.
                exact eq2.
    -   intros [r1 [s1 [[r1_neg|[r2 [s2 [ar2 [bs2 [r2_pos [s2_pos eq1]]]]]]]
            [[s1_neg|[r3 [s3 [ar3 [cs3 [r3_pos [s3_pos eq2]]]]]]] eq3]]]].
        +   left.
            rewrite eq3.
            rewrite <- (plus_rid 0).
            apply lt_lrplus; assumption.
        +   classic_case (x < 0) as [x_neg|x_pos]; try (left; exact x_neg).
            right.
            rewrite nlt_le in x_pos.
            assert (0 ≠ r3) as r3_nz.
            {
                intros contr; subst.
                rewrite mult_lanni, plus_rid in x_pos.
                destruct (lt_le_trans r1_neg x_pos); contradiction.
            }
            pose proof (div_pos _ (make_and r3_pos r3_nz)) as r3'_pos.
            exists r3, (r1 * div r3 + s3).
            repeat split; try assumption.
            *   exists (r1 * div r3), s3.
                repeat split; trivial.
                apply neg_pos2 in r1_neg.
                pose proof (lt_mult _ _ r1_neg r3'_pos) as ltq.
                rewrite mult_lneg in ltq.
                apply pos_neg2 in ltq.
                rewrite neg_neg in ltq.
                assert ([b|] 0) as b0
                    by (apply gt_rat_to_real_in; split; assumption).
                exact (land (rand (rand [|b])) _ _ b0 ltq).
            *   rewrite eq3 in x_pos.
                rewrite eq2 in x_pos.
                apply le_lmult_pos with (div r3) in x_pos; try apply r3'_pos.
                rewrite mult_ranni, ldist in x_pos.
                rewrite mult_llinv in x_pos by exact r3_nz.
                rewrite mult_comm in x_pos.
                exact x_pos.
            *   rewrite ldist.
                rewrite mult_comm.
                rewrite mult_rlinv by exact r3_nz.
                rewrite eq2 in eq3.
                exact eq3.
        +   classic_case (x < 0) as [x_neg|x_pos]; try (left; exact x_neg).
            right.
            rewrite nlt_le in x_pos.
            assert (0 ≠ r2) as r2_nz.
            {
                intros contr; subst.
                rewrite mult_lanni, plus_lid in x_pos.
                pose proof (lt_le_trans s1_neg x_pos) as [C0 C1]; contradiction.
            }
            pose proof (div_pos _ (make_and r2_pos r2_nz)) as r2'_pos.
            exists r2, (s1 * div r2 + s2).
            repeat split; try assumption.
            *   exists s2, (s1 * div r2).
                repeat split; trivial.
                2: apply plus_comm.
                apply neg_pos2 in s1_neg.
                pose proof (lt_mult _ _ s1_neg r2'_pos) as ltq.
                rewrite mult_lneg in ltq.
                apply pos_neg2 in ltq.
                rewrite neg_neg in ltq.
                assert ([c|] 0) as c0
                    by (apply gt_rat_to_real_in; split; assumption).
                exact (land (rand (rand [|c])) _ _ c0 ltq).
            *   rewrite eq3 in x_pos.
                rewrite eq1 in x_pos.
                apply le_lmult_pos with (div r2) in x_pos; try apply r2'_pos.
                rewrite mult_ranni, ldist in x_pos.
                rewrite mult_llinv in x_pos by exact r2_nz.
                rewrite mult_comm in x_pos.
                rewrite plus_comm.
                exact x_pos.
            *   rewrite ldist.
                rewrite mult_comm.
                rewrite mult_rlinv by exact r2_nz.
                rewrite eq1 in eq3.
                rewrite plus_comm.
                exact eq3.
        +   right.
            classic_case (0 = r2) as [r2_z|r2_nz].
            {
                subst.
                exists r3, s3.
                repeat split; trivial.
                2: rewrite mult_lanni, plus_lid; reflexivity.
                exists 0, s3.
                repeat split; trivial.
                apply gt_rat_to_real_in; split; assumption.
                rewrite plus_lid; reflexivity.
            }
            classic_case (0 = r3) as [r3_z|r3_nz].
            {
                subst.
                exists r2, s2.
                repeat split; trivial.
                2: rewrite mult_lanni, plus_rid; reflexivity.
                exists s2, 0.
                repeat split; trivial.
                apply gt_rat_to_real_in; split; assumption.
                rewrite plus_rid; reflexivity.
            }
            classic_case (0 = r1) as [r1_z|r1_nz].
            {
                subst.
                apply mult_0 in r1_z as [C0|s2_z]; try contradiction.
                subst.
                exists r3, s3.
                repeat split; trivial.
                2: rewrite mult_ranni, plus_lid; reflexivity.
                exists 0, s3.
                repeat split; trivial.
                rewrite plus_lid; reflexivity.
            }
            classic_case (0 = s1) as [s1_z|s1_nz].
            {
                subst.
                apply mult_0 in s1_z as [C0|s3_z]; try contradiction.
                subst.
                exists r2, s2.
                repeat split; trivial.
                2: rewrite mult_ranni, plus_rid; reflexivity.
                exists s2, 0.
                repeat split; trivial.
                rewrite plus_rid; reflexivity.
            }
            pose proof (le_mult _ _ r2_pos s2_pos) as r1_pos.
            rewrite <- eq1 in r1_pos.
            pose proof (le_mult _ _ r3_pos s3_pos) as s1_pos.
            rewrite <- eq2 in s1_pos.
            destruct (connex r2 r3) as [leq|leq].
            *   exists r3, (s3 + r1 / r3).
                repeat split; trivial.
                --  exists (r1 / r3), s3.
                    repeat split; trivial.
                    2: apply plus_comm.
                    apply mult_rlmove in eq1.
                    2: exact r2_nz.
                    rewrite <- eq1 in bs2.
                    rewrite mult_comm.
                    apply (dedekind_le _ [|b] _ _ bs2).
                    apply le_rmult_pos.
                    1: exact r1_pos.
                    apply le_div_pos; try assumption; split; try assumption.
                --  rewrite <- (plus_rid 0).
                    apply le_lrplus; try assumption.
                    apply le_mult; try assumption.
                    apply div_pos.
                    split; assumption.
                --  rewrite ldist.
                    rewrite (mult_comm r1).
                    rewrite mult_lrinv by exact r3_nz.
                    rewrite plus_comm.
                    rewrite <- eq2.
                    exact eq3.
            *   exists r2, (s2 + s1 * div r2).
                repeat split; trivial.
                --  exists s2, (s1 * div r2).
                    repeat split; trivial.
                    apply mult_rlmove in eq2.
                    2: exact r3_nz.
                    rewrite <- eq2 in cs3.
                    rewrite mult_comm.
                    apply (dedekind_le _ [|c] _ _ cs3).
                    apply le_rmult_pos.
                    1: assumption.
                    apply le_div_pos; try assumption; split; assumption.
                --  rewrite <- (plus_rid 0).
                    apply le_lrplus; try assumption.
                    apply le_mult; try assumption.
                    apply div_pos.
                    split; assumption.
                --  rewrite ldist.
                    rewrite (mult_comm s1).
                    rewrite mult_lrinv by exact r2_nz.
                    rewrite <- eq1.
                    exact eq3.
Qed.
Lemma real_ldist2 : ∀ a b c, 0 <= a → b <= 0 → c <= 0 →
    a * (b + c) = a * b + a * c.
Proof.
    intros a b c a_pos b_neg c_neg.
    rewrite <- (neg_neg (b + c)).
    rewrite (neg_plus b c).
    rewrite real_mult_rneg.
    rewrite <- (neg_neg b) at 2.
    rewrite <- (neg_neg c) at 2.
    rewrite real_mult_rneg.
    rewrite (real_mult_rneg a (-c)).
    rewrite <- (neg_plus (a * -b)).
    apply f_equal.
    apply neg_pos in b_neg, c_neg.
    apply real_ldist1; assumption.
Qed.
Lemma real_ldist3 : ∀ a b c, 0 <= a → 0 <= b → c <= 0 → 0 <= b + c →
    a * (b + c) = a * b + a * c.
Proof.
    intros a b c a_pos b_pos c_neg bc_pos.
    rewrite <- (neg_neg (a * c)).
    apply plus_lrmove.
    rewrite <- real_mult_rneg.
    apply neg_pos in c_neg.
    rewrite <- real_ldist1 by assumption.
    rewrite plus_rrinv.
    reflexivity.
Qed.
Lemma real_ldist4 : ∀ a b c, 0 <= a → 0 <= b → c <= 0 → b + c <= 0 →
    a * (b + c) = a * b + a * c.
Proof.
    intros a b c a_pos b_pos c_neg bc_neg.
    rewrite <- (neg_neg (a * b)).
    apply plus_llmove.
    rewrite <- (neg_neg (a * (b + c))).
    rewrite <- (real_mult_rneg a (b + c)).
    rewrite <- neg_plus.
    apply neg_pos in bc_neg.
    rewrite <- real_ldist1 by assumption.
    rewrite neg_plus.
    rewrite plus_lrinv.
    rewrite real_mult_rneg.
    rewrite neg_neg.
    reflexivity.
Qed.
Lemma real_ldist5 : ∀ a b c, 0 <= a → 0 <= b → c <= 0 →
    a * (b + c) = a * b + a * c.
Proof.
    intros a b c a_pos b_pos c_neg.
    destruct (connex 0 (b + c)) as [bc_pos|bc_neg].
    -   apply real_ldist3; assumption.
    -   apply real_ldist4; assumption.
Qed.
Lemma real_ldist6 : ∀ a b c, 0 <= a → 0 <= b → a * (b + c) = a * b + a * c.
Proof.
    intros a b c a_pos b_pos.
    destruct (connex 0 c) as [c_pos|c_neg].
    -   apply real_ldist1; assumption.
    -   apply real_ldist5; assumption.
Qed.
Lemma real_ldist7 : ∀ a b c, 0 <= a → b <= 0 → a * (b + c) = a * b + a * c.
Proof.
    intros a b c a_pos b_neg.
    destruct (connex 0 c) as [c_pos|c_neg].
    -   rewrite (plus_comm b c).
        rewrite (plus_comm (a * b) (a * c)).
        apply real_ldist5; assumption.
    -   apply real_ldist2; assumption.
Qed.
Lemma real_ldist8 : ∀ a b c, 0 <= a → a * (b + c) = a * b + a * c.
Proof.
    intros a b c a_pos.
    destruct (connex 0 b) as [b_pos|b_neg].
    -   apply real_ldist6; assumption.
    -   apply real_ldist7; assumption.
Qed.
Lemma real_ldist_ : ∀ a b c, a * (b + c) = a * b + a * c.
Proof.
    intros a b c.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply real_ldist8; exact a_pos.
    -   do 3 rewrite (real_mult_neg_any a) by exact a_neg.
        rewrite <- neg_plus.
        apply f_equal.
        apply neg_pos in a_neg.
        apply real_ldist8; exact a_neg.
Qed.
Global Instance real_ldist : Ldist real := {
    ldist := real_ldist_;
}.

Global Instance real_one : One real := {
    one := rat_to_real 1
}.

Lemma real_one_pos : 0 <= 1.
Proof.
    unfold zero, one; cbn.
    rewrite rat_to_real_le.
    apply one_pos.
Qed.
Lemma real_mult_lid1 : ∀ a, 0 <= a → 1 * a = a.
Proof.
    intros a a_pos.
    pose proof real_one_pos as op.
    apply set_type_eq.
    rewrite real_mult_pos_pos by assumption.
    unfold one; cbn.
    unfold rat_to_real_base; cbn.
    destruct a as [a a_cut]; cbn.
    apply predicate_ext; intros x; split.
    -   intros [x_neg|x_in].
        +   apply a_pos.
            exact x_neg.
        +   destruct x_in as [r [s [r_lt [as_ [r_pos [s_pos eq]]]]]].
            subst x.
            classic_case (0 = s) as [s_z|s_nz].
            *   subst.
                rewrite mult_ranni.
                exact as_.
            *   apply lt_rmult_pos with s in r_lt.
                2: split; assumption.
                rewrite mult_lid in r_lt.
                exact (land (rand (rand a_cut)) _ _ as_ r_lt).
    -   intros ax.
        classic_case (x < 0) as [x_neg|x_pos].
        +   left; exact x_neg.
        +   right.
            rewrite nlt_le in x_pos.
            pose proof (rand (rand (rand a_cut)) _ ax) as [y [ay xy]].
            pose proof (le_lt_trans x_pos xy) as y_pos.
            exists (x * div y), y.
            split.
            2: repeat split.
            *   apply lt_mult_rrmove_pos.
                1: exact y_pos.
                rewrite mult_lid.
                exact xy.
            *   exact ay.
            *   apply le_mult.
                --  exact x_pos.
                --  apply div_pos.
                    exact y_pos.
            *   apply y_pos.
            *   rewrite mult_rlinv by apply y_pos.
                reflexivity.
Qed.
Theorem real_mult_lid_ : ∀ a, 1 * a = a.
Proof.
    intros a.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply real_mult_lid1.
        exact a_pos.
    -   rewrite real_mult_any_neg by exact a_neg.
        rewrite <- (neg_neg a) at 2.
        apply f_equal.
        apply neg_pos in a_neg.
        apply real_mult_lid1.
        exact a_neg.
Qed.
Global Instance real_mult_lid : MultLid real := {
    mult_lid := real_mult_lid_;
}.
(* begin hide *)
Close Scope real_scope.
(* end hide *)
