Require Import init.

Require Import rat.
Require Import set.

Require Export dedekind_real_base.
Require Import dedekind_real_order.
Require Import dedekind_real_plus.

(** This file contains the definition of multiplication and several theorems
used to make the ridiculous number of cases involved more manageable
*)
(* begin hide *)
Open Scope real_scope.
(* end hide *)
Definition real_mult_base a b :=
    λ x, x < 0 ∨ ∃ r s, a r ∧ b s ∧ 0 <= r ∧ 0 <= s ∧ x = r * s.
Infix "⊗":= real_mult_base : real_scope.

Theorem real_mult_dedekind : ∀ (a b : real), 0 <= a → 0 <= b →
        dedekind_cut ([a|] ⊗ [b|]).
    intros [a a_cut] [b b_cut] a_pos b_pos; cbn.
    unfold zero, le in a_pos, b_pos; cbn in *.
    unfold rat_to_real_base in *.
    split.
    2: split.
    3: split.
    -   pose proof (land a_cut) as u_ex.
        pose proof (land b_cut) as v_ex.
        apply not_all_not_ex in u_ex as [u nau].
        apply not_all_not_ex in v_ex as [v nbv].
        intro contr.
        assert (all (u * v)) as eq by exact true.
        rewrite <- contr in eq.
        destruct eq as [ltq|eq].
        +   destruct (trichotomy 0 u) as [[u_pos|u_z]|u_neg].
            *   apply lt_mult_llmove_pos in ltq.
                2: exact u_pos.
                rewrite mult_ranni in ltq.
                apply b_pos in ltq.
                contradiction.
            *   subst.
                rewrite mult_lanni in ltq.
                destruct ltq; contradiction.
            *   apply a_pos in u_neg.
                contradiction.
        +   destruct eq as [r [s [ar [bs [r_pos [s_pos eq]]]]]].
            destruct (trichotomy u r) as [[ur|ur]|ur].
            *   pose proof (land (rand (rand a_cut)) _ _ ar ur).
                contradiction.
            *   subst.
                contradiction.
            *   classic_case (0 = s) as [s0|s_nz].
                --  subst.
                    rewrite mult_ranni in eq.
                    symmetry in eq; apply mult_0 in eq as [eq|eq].
                    ++  subst.
                        destruct (le_lt_trans r_pos ur); contradiction.
                    ++  subst.
                        contradiction.
                --  apply lt_rmult_pos with s in ur.
                    2: exact (make_and s_pos s_nz).
                    rewrite <- eq in ur.
                    classic_case (0 = u) as [uz|unz].
                    ++  subst.
                        do 2 rewrite mult_lanni in ur.
                        destruct ur; contradiction.
                    ++  assert (0 < u) as u_pos.
                        {
                            split; try exact unz.
                            classic_contradiction ltq.
                            rewrite nle_lt in ltq.
                            apply a_pos in ltq.
                            contradiction.
                        }
                        apply lt_mult_lcancel_pos in ur; try exact u_pos.
                        pose proof (land (rand (rand b_cut)) _ _ bs ur).
                        contradiction.
    -   apply ex_not_empty.
        exists (-(1)).
        left.
        apply pos_neg2.
        exact one_pos.
    -   intros l u [u_neg|[r [s [ar [bs [r_pos [s_pos eq]]]]]]] ltq.
        +   left; exact (trans ltq u_neg).
        +   subst u.
            destruct (trichotomy 0 l) as [[l_pos|l_z]|l_neg].
            *   right.
                classic_case (0 = s) as [s_z|s_nz].
                {
                    subst.
                    rewrite mult_ranni in ltq.
                    destruct (trans ltq l_pos); contradiction.
                }
                exists (l * div s), s.
                repeat split; try assumption.
                --  apply (land (rand (rand a_cut)) _ r); try exact ar.
                    apply lt_mult_rrmove_pos.
                    1: split; assumption.
                    exact ltq.
                --  apply le_mult.
                    ++  apply l_pos.
                    ++  apply div_pos.
                        split; assumption.
                --  rewrite mult_rlinv by exact s_nz.
                    reflexivity.
            *   subst.
                right.
                exists 0, 0.
                repeat split.
                3, 4: apply refl.
                3: rewrite mult_ranni; reflexivity.
                --  classic_case (0 = r) as [r_eq|r_neq].
                    ++  subst; exact ar.
                    ++  apply (land (rand (rand a_cut)) _ _ ar).
                        split; assumption.
                --  classic_case (0 = s) as [s_eq|s_neq].
                    ++  subst; exact bs.
                    ++  apply (land (rand (rand b_cut)) _ _ bs).
                        split; assumption.
            *   left; exact l_neg.
    -   intros l [l_neg|[r [s [ar [bs [r_pos [s_pos eq]]]]]]].
        +   exists (l / 2).
            split.
            *   left.
                apply lt_mult_rrmove_pos.
                1: exact two_pos.
                rewrite mult_lanni.
                exact l_neg.
            *   apply lt_mult_lrmove_pos.
                1: exact two_pos.
                rewrite ldist.
                rewrite mult_rid.
                rewrite <- (plus_rid l) at 3.
                apply lt_lplus.
                exact l_neg.
        +   pose proof (rand (rand (rand a_cut)) _ ar) as [r' [ar' r'_eq]].
            pose proof (rand (rand (rand b_cut)) _ bs) as [s' [bs' s'_eq]].
            exists (r' * s').
            split.
            *   right.
                exists r', s'.
                repeat split; try assumption.
                --  apply (le_lt_trans r_pos r'_eq).
                --  apply (le_lt_trans s_pos s'_eq).
            *   rewrite eq.
                classic_case (0 = s) as [sz|snz].
                --  subst.
                    rewrite mult_ranni.
                    apply lt_mult; try exact s'_eq.
                    exact (le_lt_trans r_pos r'_eq).
                --  apply lt_lmult_pos with r' in s'_eq.
                    2: exact (le_lt_trans r_pos r'_eq).
                    apply lt_rmult_pos with s in r'_eq.
                    2: split; assumption.
                    exact (trans r'_eq s'_eq).
Qed.

Global Instance real_mult : Mult real := {
    mult a b :=
    match (connex 0 a), (connex 0 b) with
        | strong_or_left a_pos, strong_or_left b_pos =>
            [_|real_mult_dedekind _ _ a_pos b_pos]
        | strong_or_left a_pos, strong_or_right b_neg =>
            -[_|real_mult_dedekind _ _ a_pos (neg_pos _ b_neg)]
        | strong_or_right a_neg, strong_or_left b_pos =>
            -[_|real_mult_dedekind _ _ (neg_pos _ a_neg) b_pos]
        | strong_or_right a_neg, strong_or_right b_neg =>
            [_|real_mult_dedekind _ _ (neg_pos _ a_neg) (neg_pos _ b_neg)]
    end
}.
Lemma real_mult_comm_pos : ∀ a b, 0 <= a → 0 <= b → [a|] ⊗ [b|] = [b|] ⊗ [a|].
    intros [a a_cut] [b b_cut] a_pos b_pos.
    cbn.
    apply predicate_ext; intros x; split.
    -   intros [x_neg|[r [s [ar [bs [r_pos [s_pos eq]]]]]]].
        +   left; exact x_neg.
        +   right.
            exists s, r.
            rewrite mult_comm in eq.
            repeat split; assumption.
    -   intros [x_neg|[r [s [br [as_ [r_pos [s_pos eq]]]]]]].
        +   left; exact x_neg.
        +   right.
            exists s, r.
            rewrite mult_comm in eq.
            repeat split; assumption.
Qed.
Lemma real_mult_comm_ : ∀ a b, a * b = b * a.
    intros a b.
    unfold mult; cbn.
    destruct (connex 0 a) as [a_pos|a_neg];
    destruct (connex 0 b) as [b_pos|b_neg].
    -   apply set_type_eq; cbn.
        apply real_mult_comm_pos; assumption.
    -   apply f_equal.
        apply set_type_eq; cbn.
        apply real_mult_comm_pos; try assumption.
        apply neg_pos.
        exact b_neg.
    -   apply f_equal.
        apply set_type_eq; cbn.
        apply real_mult_comm_pos; try assumption.
        apply neg_pos.
        exact a_neg.
    -   apply set_type_eq; cbn.
        apply real_mult_comm_pos; apply neg_pos; assumption.
Qed.
Global Instance real_mult_comm : MultComm real := {
    mult_comm := real_mult_comm_;
}.

Lemma real_mult_lanni_pos : ∀ a, 0 <= a → [0|] ⊗ [a|] = [0|].
    intros [a a_cut] a_pos.
    cbn.
    unfold zero; cbn.
    unfold rat_to_real_base.
    apply predicate_ext; intros x; split.
    -   intros [x_neg|[r [s [r_neg [as_ [r_pos [s_pos eq]]]]]]].
        +   exact x_neg.
        +   pose proof (lt_le_trans r_neg r_pos) as [C0 C1]; contradiction.
    -   intros x_neg.
        left.
        exact x_neg.
Qed.
Lemma real_mult_lanni : ∀ a, 0 * a = 0.
    intros a.
    unfold mult; cbn.
    destruct (connex 0 0) as [zleq|zleq];
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply set_type_eq; cbn.
        apply real_mult_lanni_pos; assumption.
    -   rewrite <- neg_zero.
        apply f_equal.
        apply set_type_eq; cbn.
        apply real_mult_lanni_pos.
        apply neg_pos.
        exact a_neg.
    -   rewrite <- neg_zero.
        apply f_equal.
        apply set_type_eq; cbn.
        rewrite neg_zero.
        apply real_mult_lanni_pos.
        exact a_pos.
    -   apply set_type_eq; cbn.
        rewrite neg_zero.
        apply real_mult_lanni_pos.
        apply neg_pos.
        exact a_neg.
Qed.
Lemma real_mult_ranni : ∀ a, a * 0 = 0.
    intros a.
    rewrite mult_comm.
    apply real_mult_lanni.
Qed.

Lemma real_mult_pos_pos : ∀ a b, 0 <= a → 0 <= b → [a * b|] = [a|] ⊗ [b|].
    intros a b a_pos b_pos.
    classic_case (a <= 0) as [a_neg|a_nneg].
    {
        pose proof (antisym a_pos a_neg).
        subst.
        rewrite real_mult_lanni.
        rewrite real_mult_lanni_pos by exact b_pos.
        reflexivity.
    }
    classic_case (b <= 0) as [b_neg|b_nneg].
    {
        pose proof (antisym b_pos b_neg).
        subst.
        rewrite real_mult_ranni.
        rewrite real_mult_comm_pos by assumption.
        rewrite real_mult_lanni_pos by exact a_pos.
        reflexivity.
    }
    unfold mult; cbn.
    unfold rat, rat_le_connex.
    destruct (connex 0 a) as [a_pos'|a_neg]; try contradiction;
    destruct (connex 0 b) as [b_pos'|b_neg]; try contradiction.
    reflexivity.
Qed.

Lemma real_mult_pos_neg : ∀ a b, 0 <= a → b <= 0 → a * b = -(a * -b).
    intros a b a_pos b_neg.
    classic_case (a <= 0) as [a_neg|a_nneg].
    {
        pose proof (antisym a_pos a_neg).
        subst.
        do 2 rewrite real_mult_lanni.
        rewrite neg_zero.
        reflexivity.
    }
    classic_case (0 <= b) as [b_pos|b_npos].
    {
        pose proof (antisym b_pos b_neg).
        subst.
        rewrite neg_zero.
        rewrite real_mult_ranni.
        rewrite neg_zero.
        reflexivity.
    }
    unfold neg at 1; cbn.
    apply set_type_eq; cbn.
    apply neg_pos in b_neg.
    rewrite (real_mult_pos_pos a (-b)) by assumption.
    unfold mult; cbn.
    destruct (connex 0 a) as [a_pos'|a_neg]; try contradiction;
    destruct (connex 0 b) as [b_neg'|b_pos]; try contradiction.
    reflexivity.
Qed.

Lemma real_mult_neg_pos : ∀ a b, a <= 0 → 0 <= b → a * b = -(-a * b).
    intros a b a_neg b_pos.
    classic_case (0 <= a) as [a_pos|a_npos].
    {
        pose proof (antisym a_pos a_neg).
        subst.
        rewrite neg_zero.
        rewrite real_mult_lanni.
        rewrite neg_zero.
        reflexivity.
    }
    classic_case (b <= 0) as [b_neg|b_nneg].
    {
        pose proof (antisym b_pos b_neg).
        subst.
        do 2 rewrite real_mult_ranni.
        rewrite neg_zero.
        reflexivity.
    }
    unfold neg at 1; cbn.
    apply set_type_eq; cbn.
    apply neg_pos in a_neg.
    rewrite (real_mult_pos_pos (-a) b) by assumption.
    unfold mult; cbn.
    destruct (connex 0 a) as [a_neg'|a_pos]; try contradiction;
    destruct (connex 0 b) as [b_pos'|b_neg]; try contradiction.
    reflexivity.
Qed.

Lemma real_mult_neg_neg : ∀ a b, a <= 0 → b <= 0 → a * b = -a * -b.
    intros a b a_neg b_neg.
    classic_case (0 <= a) as [a_pos|a_npos].
    {
        pose proof (antisym a_pos a_neg).
        subst.
        rewrite neg_zero.
        do 2 rewrite real_mult_lanni.
        reflexivity.
    }
    classic_case (0 <= b) as [b_pos|b_npos].
    {
        pose proof (antisym b_pos b_neg).
        subst.
        rewrite neg_zero.
        do 2 rewrite real_mult_ranni.
        reflexivity.
    }
    apply set_type_eq; cbn.
    apply neg_pos in a_neg.
    apply neg_pos in b_neg.
    rewrite (real_mult_pos_pos (-a) (-b)) by assumption.
    unfold mult; cbn.
    destruct (connex 0 a) as [a_neg'|a_pos]; try contradiction;
    destruct (connex 0 b) as [b_neg'|b_pos]; try contradiction.
    reflexivity.
Qed.

Lemma real_mult_neg_any : ∀ a b, a <= 0 → a * b = -(-a * b).
    intros a b a_neg.
    destruct (connex 0 b) as [b_pos|b_neg].
    -   apply real_mult_neg_pos; assumption.
    -   pose proof (neg_pos _ a_neg).
        rewrite (real_mult_pos_neg (-a) b) by assumption.
        rewrite neg_neg.
        apply real_mult_neg_neg; assumption.
Qed.

Lemma real_mult_any_neg : ∀ a b, b <= 0 → a * b = -(a * -b).
    intros a b b_neg.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply real_mult_pos_neg; assumption.
    -   pose proof (neg_pos _ b_neg).
        rewrite (real_mult_neg_pos a (-b)) by assumption.
        rewrite neg_neg.
        apply real_mult_neg_neg; assumption.
Qed.

Lemma real_mult_lneg : ∀ a b, -a * b = -(a * b).
    intros a b.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply pos_neg in a_pos.
        rewrite real_mult_neg_any by assumption.
        rewrite neg_neg.
        reflexivity.
    -   rewrite (real_mult_neg_any a b) by assumption.
        rewrite neg_neg.
        reflexivity.
Qed.

Lemma real_mult_rneg : ∀ a b, a * -b = -(a * b).
    intros a b.
    do 2 rewrite (mult_comm a).
    apply real_mult_lneg.
Qed.

Lemma real_le_mult_ : ∀ a b, 0 <= a → 0 <= b → 0 <= a * b.
    intros a b a_pos b_pos.
    unfold le; cbn.
    rewrite real_mult_pos_pos by assumption.
    intros x x_lt.
    left.
    exact x_lt.
Qed.

Global Instance real_le_mult : OrderMult real := {
    le_mult := real_le_mult_;
}.
(* begin hide *)
Close Scope real_scope.
(* end hide *)
