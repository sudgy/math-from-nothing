Require Import init.

Require Export order_mult.

(* begin hide *)
Section Abs.

Context {U} `{OrderedField U}.
(* end hide *)

Definition abs (a : U) := If 0 <= a then a else -a.
Notation "| a |" := (abs a) (at level 30).

Theorem abs_zero : 0 = |0|.
Proof.
    unfold abs; case_if [leq|leq].
    -   reflexivity.
    -   rewrite neg_zero.
        reflexivity.
Qed.

Theorem abs_def : ∀ x, 0 = |x| ↔ 0 = x.
Proof.
    intros x.
    split.
    -   intros eq.
        unfold abs in eq; case_if [leq|leq].
        +   exact eq.
        +   apply zero_eq_neg.
            exact eq.
    -   intros eq; subst x.
        exact abs_zero.
Qed.

Theorem abs_nz : ∀ x, 0 ≠ |x| ↔ 0 ≠ x.
Proof.
    intros x.
    split; intros eq contr.
    -   rewrite <- abs_def in contr.
        contradiction.
    -   rewrite abs_def in contr.
        contradiction.
Qed.

Theorem abs_pos : ∀ x, 0 <= |x|.
Proof.
    intros x.
    unfold abs; case_if [leq|leq].
    -   exact leq.
    -   rewrite nle_lt in leq.
        apply neg_pos2 in leq.
        apply leq.
Qed.

Theorem abs_pos_eq : ∀ x, 0 <= x → |x| = x.
Proof.
    intros x x_pos.
    unfold abs; case_if [leq|leq].
    -   reflexivity.
    -   contradiction.
Qed.

Theorem abs_one : |1| = 1.
Proof.
    apply abs_pos_eq.
    apply one_pos.
Qed.

Theorem abs_neg : ∀ a, | -a| = |a|.
Proof.
    intros a.
    unfold abs; case_if [leq1|leq1]; case_if [leq2|leq2].
    -   rewrite <- neg_pos in leq1.
        pose proof (antisym leq1 leq2) as eq; subst a.
        apply neg_zero.
    -   reflexivity.
    -   apply neg_neg.
    -   rewrite nle_lt in leq1, leq2.
        rewrite <- pos_neg2 in leq1.
        destruct (trans leq1 leq2); contradiction.
Qed.

Theorem abs_neg_eq : ∀ x, x <= 0 → |x| = -x.
Proof.
    intros x x_neg.
    rewrite <- abs_neg.
    apply neg_pos in x_neg.
    exact (abs_pos_eq _ x_neg).
Qed.

Theorem abs_minus : ∀ a b, |a - b| = |b - a|.
Proof.
    intros a b.
    rewrite <- abs_neg.
    rewrite neg_plus, neg_neg.
    rewrite plus_comm.
    reflexivity.
Qed.

Theorem abs_mult : ∀ a b, |a * b| = |a| * |b|.
Proof.
    assert (∀ a b, 0 <= a → |a * b| = a * |b|) as lem.
    {
        intros a b a_pos.
        unfold abs at 2; case_if [leq|leq].
        -   apply abs_pos_eq.
            apply le_mult; assumption.
        -   rewrite <- abs_neg.
            rewrite mult_rneg.
            apply abs_pos_eq.
            rewrite nle_lt in leq.
            apply neg_pos2 in leq as [leq neq].
            pose proof (le_mult a_pos leq) as eq.
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
Proof.
    intros a b.
    split.
    -   intros leq.
        unfold abs in leq; case_if [leq'|leq'].
        +   split; [>|exact leq].
            pose proof (trans leq' leq) as leq2.
            apply pos_neg in leq2.
            exact (trans leq2 leq').
        +   split.
            *   apply le_half_lneg in leq.
                exact leq.
            *   rewrite nle_lt in leq'.
                pose proof (land (neg_pos2 _) leq') as a_pos.
                apply (trans leq' (lt_le_trans a_pos leq)).
    -   intros [ba ab].
        unfold abs; case_if [leq|leq].
        +   exact ab.
        +   apply le_half_lneg in ba.
            exact ba.
Qed.

Theorem abs_lt : ∀ a b, |a| < b ↔ -b < a ∧ a < b.
Proof.
    intros a b.
    split.
    -   intros leq.
        unfold abs in leq; case_if [leq'|leq'].
        +   split; [>|exact leq].
            pose proof (le_lt_trans leq' leq) as leq2.
            apply pos_neg2 in leq2.
            exact (lt_le_trans leq2 leq').
        +   split.
            *   apply lt_half_lneg in leq.
                exact leq.
            *   rewrite nle_lt in leq'.
                pose proof (land (neg_pos2 _) leq') as a_pos.
                exact (trans leq' (trans a_pos leq)).
    -   intros [ba ab].
        unfold abs; case_if [leq|leq].
        +   exact ab.
        +   apply lt_half_lneg in ba.
            exact ba.
Qed.

Theorem abs_le_pos : ∀ x, x <= |x|.
Proof.
    intros x.
    unfold abs; case_if [leq|leq].
    -   apply refl.
    -   rewrite nle_lt in leq.
        pose proof (land (neg_pos2 _) leq) as ltq.
        apply (trans leq ltq).
Qed.

Theorem abs_le_neg : ∀ x, -x <= |x|.
Proof.
    intros x.
    rewrite <- abs_neg.
    apply abs_le_pos.
Qed.

Theorem abs_tri : ∀ a b, |a + b| <= |a| + |b|.
Proof.
    intros a b.
    apply abs_le; split.
    -   apply le_half_lneg.
        rewrite neg_plus.
        apply le_lrplus; apply abs_le_neg.
    -   apply le_lrplus; apply abs_le_pos.
Qed.

Theorem abs_reverse_tri : ∀ a b, | |a| - |b| | <= |a - b|.
Proof.
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
Proof.
    intros a a_nz.
    pose proof (rand (abs_nz _) a_nz) as a_nz'.
    apply (mult_lcancel (|a|) a_nz').
    rewrite <- abs_mult.
    do 2 rewrite mult_rinv by assumption.
    rewrite abs_one.
    reflexivity.
Qed.

Theorem abs_abs : ∀ a, | |a| | = |a|.
Proof.
    intros a.
    unfold abs at 2; case_if [leq|leq].
    -   reflexivity.
    -   apply abs_neg.
Qed.

(* begin hide *)
End Abs.
(* end hide *)
