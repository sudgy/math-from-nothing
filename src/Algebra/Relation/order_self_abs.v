Require Import init.

Require Export order_mult.

(* begin hide *)
Section Abs.

Context {U} `{OrderedField U}.
(* end hide *)

Definition abs (a : U) := If 0 <= a then a else -a.
Notation "| a |" := (abs a) (at level 30).

Theorem abs_zero : 0 = |0|.
    unfold abs; case_if.
    -   reflexivity.
    -   rewrite neg_zero.
        reflexivity.
Qed.

Theorem abs_one : |1| = 1.
    unfold abs; case_if.
    -   reflexivity.
    -   pose proof one_pos as [leq neq].
        contradiction.
Qed.

Theorem abs_def : ∀ x, 0 = |x| ↔ 0 = x.
    intros x.
    split.
    -   intros eq.
        unfold abs in eq; case_if.
        +   exact eq.
        +   apply (f_equal neg) in eq.
            rewrite neg_neg, neg_zero in eq.
            exact eq.
    -   intros eq; subst x.
        exact abs_zero.
Qed.

Theorem abs_nz : ∀ x, 0 ≠ |x| ↔ 0 ≠ x.
    intros x.
    split; intros eq contr.
    -   rewrite <- abs_def in contr.
        contradiction.
    -   rewrite abs_def in contr.
        contradiction.
Qed.

Theorem abs_pos : ∀ x, 0 <= |x|.
    intros x.
    unfold abs; case_if.
    -   exact l.
    -   rewrite nle_lt in n.
        apply neg_pos2 in n.
        apply n.
Qed.

Theorem abs_pos_eq : ∀ x, 0 <= x → |x| = x.
    intros x x_pos.
    unfold abs; case_if.
    -   reflexivity.
    -   contradiction.
Qed.

Theorem abs_neg : ∀ a, | -a| = |a|.
    intros a.
    unfold abs; do 2 case_if.
    -   apply pos_neg in l.
        rewrite neg_neg in l.
        pose proof (antisym l l0) as eq; subst a.
        rewrite neg_zero.
        reflexivity.
    -   reflexivity.
    -   rewrite neg_neg.
        reflexivity.
    -   rewrite nle_lt in n, n0.
        apply neg_pos2 in n.
        rewrite neg_neg in n.
        destruct (trans n n0); contradiction.
Qed.

Theorem abs_neg_eq : ∀ x, x <= 0 → |x| = -x.
    intros x x_neg.
    rewrite <- abs_neg.
    apply neg_pos in x_neg.
    exact (abs_pos_eq _ x_neg).
Qed.

Theorem abs_minus : ∀ a b, |a - b| = |b - a|.
    intros a b.
    rewrite <- abs_neg.
    rewrite neg_plus, neg_neg.
    rewrite plus_comm.
    reflexivity.
Qed.

Theorem abs_mult : ∀ a b, |a * b| = |a| * |b|.
    assert (∀ a b, 0 <= a → |a * b| = a * |b|) as lem.
    {
        intros a b a_pos.
        unfold abs at 2; case_if.
        -   apply abs_pos_eq.
            apply le_mult; assumption.
        -   rewrite <- abs_neg.
            rewrite mult_rneg.
            apply abs_pos_eq.
            rewrite nle_lt in n.
            apply neg_pos2 in n as [leq neq].
            pose proof (le_mult _ _ a_pos leq) as eq.
            rewrite mult_rneg in eq.
            exact eq.
    }
    intros a b.
    unfold abs at 2; case_if.
    -   apply lem; exact l.
    -   rewrite nle_lt in n.
        rewrite <- abs_neg.
        rewrite <- mult_lneg.
        apply lem.
        apply neg_pos.
        apply n.
Qed.

Theorem abs_le : ∀ a b, |a| <= b ↔ -b <= a ∧ a <= b.
    intros a b.
    split.
    -   intros leq.
        unfold abs in leq; case_if.
        +   split; [>|exact leq].
            pose proof (trans l leq) as leq2.
            apply pos_neg in leq2.
            exact (trans leq2 l).
        +   split.
            *   apply le_neg in leq.
                rewrite neg_neg in leq.
                exact leq.
            *   rewrite nle_lt in n.
                pose proof (neg_pos2 _ n) as a_pos.
                apply (trans n (lt_le_trans a_pos leq)).
    -   intros [ba ab].
        unfold abs; case_if.
        +   exact ab.
        +   apply le_neg in ba.
            rewrite neg_neg in ba.
            exact ba.
Qed.

Theorem abs_lt : ∀ a b, |a| < b ↔ -b < a ∧ a < b.
    intros a b.
    split.
    -   intros leq.
        unfold abs in leq; case_if.
        +   split; [>|exact leq].
            pose proof (le_lt_trans l leq) as leq2.
            apply pos_neg2 in leq2.
            exact (lt_le_trans leq2 l).
        +   split.
            *   apply lt_neg in leq.
                rewrite neg_neg in leq.
                exact leq.
            *   rewrite nle_lt in n.
                pose proof (neg_pos2 _ n) as a_pos.
                apply (trans n (trans a_pos leq)).
    -   intros [ba ab].
        unfold abs; case_if.
        +   exact ab.
        +   apply lt_neg in ba.
            rewrite neg_neg in ba.
            exact ba.
Qed.

Theorem abs_le_pos : ∀ x, x <= |x|.
    intros x.
    unfold abs; case_if.
    -   apply refl.
    -   rewrite nle_lt in n.
        pose proof (neg_pos2 _ n) as ltq.
        apply (trans n ltq).
Qed.

Theorem abs_le_neg : ∀ x, -x <= |x|.
    intros x.
    rewrite <- abs_neg.
    apply abs_le_pos.
Qed.

Theorem abs_tri : ∀ a b, |a + b| <= |a| + |b|.
    intros a b.
    apply abs_le; split.
    -   apply le_neg.
        rewrite neg_neg.
        rewrite neg_plus.
        apply le_lrplus; apply abs_le_neg.
    -   apply le_lrplus; apply abs_le_pos.
Qed.

Theorem abs_reverse_tri : ∀ a b, | |a| - |b| | <= |a - b|.
    intros a b.
    apply abs_le; split.
    -   pose proof (abs_tri (b - a) a) as leq.
        rewrite plus_rlinv in leq.
        rewrite abs_minus in leq.
        rewrite le_plus_rlmove in leq.
        rewrite le_plus_lrmove in leq.
        exact leq.
    -   pose proof (abs_tri (a - b) b) as leq.
        rewrite plus_rlinv in leq.
        rewrite le_plus_rrmove in leq.
        exact leq.
Qed.

Theorem abs_div : ∀ a, 0 ≠ a → /|a| = |/a|.
    intros a a_nz.
    pose proof a_nz as a_nz'.
    apply abs_nz in a_nz'.
    apply (mult_lcancel (|a|) a_nz').
    rewrite <- abs_mult.
    do 2 rewrite mult_rinv by assumption.
    rewrite abs_one.
    reflexivity.
Qed.

Theorem abs_abs : ∀ a, | |a| | = |a|.
    intros a.
    unfold abs at 2; case_if.
    -   reflexivity.
    -   apply abs_neg.
Qed.

(* begin hide *)
End Abs.
(* end hide *)
