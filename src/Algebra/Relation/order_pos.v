Require Import init.

Require Export order_mult.

Class OrderPositive U `{Zero U, Order U} := {
    all_pos : ∀ x, 0 ≤ x
}.

Section OrderPositive.

Context {U} `{OrderedFieldClass U, @OrderPositive U UZ UO}.

Theorem all_neg_eq : ∀ {x}, x ≤ 0 → 0 = x.
Proof.
    intros x leq.
    apply antisym.
    -   apply all_pos.
    -   exact leq.
Qed.

Theorem all_pos2 : ∀ {x}, 0 ≠ x → 0 < x.
Proof.
    intros x x_nz.
    split.
    -   apply all_pos.
    -   exact x_nz.
Qed.

Theorem not_neg : ∀ {x}, ¬(x < 0).
Proof.
    intros x.
    rewrite nlt_le.
    apply all_pos.
Qed.

Global Instance all_pos_le_mult : OrderMult U.
Proof.
    split.
    intros a b leq1 leq2.
    apply all_pos.
Qed.

Theorem le_lmult : ∀ {a b} c, a ≤ b → c * a ≤ c * b.
Proof.
    intros a b c.
    apply le_lmult_pos.
    apply all_pos.
Qed.

Theorem le_rmult : ∀ {a b} c, a ≤ b → a * c ≤ b * c.
Proof.
    intros a b c.
    apply le_rmult_pos.
    apply all_pos.
Qed.

Theorem lt_lmult : ∀ {a b} c, 0 ≠ c → a < b → c * a < c * b.
Proof.
    intros a b c c_nz.
    apply lt_lmult_pos.
    exact (all_pos2 c_nz).
Qed.

Theorem lt_rmult : ∀ {a b} c, 0 ≠ c → a < b → a * c < b * c.
Proof.
    intros a b c c_nz.
    apply lt_rmult_pos.
    exact (all_pos2 c_nz).
Qed.

Theorem le_mult_lcancel : ∀ {a b} c, 0 ≠ c → c * a ≤ c * b → a ≤ b.
Proof.
    intros a b c c_nz.
    apply le_mult_lcancel_pos.
    exact (all_pos2 c_nz).
Qed.

Theorem le_mult_rcancel : ∀ {a b} c, 0 ≠ c → a * c ≤ b * c → a ≤ b.
Proof.
    intros a b c c_nz.
    apply le_mult_rcancel_pos.
    exact (all_pos2 c_nz).
Qed.

Theorem lt_mult_lcancel : ∀ {a b} c, 0 ≠ c → c * a < c * b → a < b.
Proof.
    intros a b c c_nz.
    apply lt_mult_lcancel_pos.
    exact (all_pos2 c_nz).
Qed.

Theorem lt_mult_rcancel : ∀ {a b} c, 0 ≠ c → a * c < b * c → a < b.
Proof.
    intros a b c c_nz.
    apply lt_mult_rcancel_pos.
    exact (all_pos2 c_nz).
Qed.

(** OrderLmult2 → MultLcancel *)
Local Instance mult_lcancel1 : MultLcancel U.
Proof.
    split.
    intros a b c c_nz eq.
    destruct (trichotomy a b) as [[ltq|eq']|ltq].
    -   apply (lt_lmult c c_nz) in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply (lt_lmult c c_nz) in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

(** OrderMultLcancel → MultLcancel *)
Local Instance mult_lcancel2 : MultLcancel U.
Proof.
    split.
    intros a b c c_nz eq.
    assert (c * a ≤ c * b) as leq1 by (rewrite eq; apply refl).
    assert (c * b ≤ c * a) as leq2 by (rewrite eq; apply refl).
    apply (le_mult_lcancel _ c_nz) in leq1.
    apply (le_mult_lcancel _ c_nz) in leq2.
    apply antisym; assumption.
Qed.

(** OrderRmult2 → MultRcancel *)
Local Instance mult_rcancel1 : MultRcancel U.
Proof.
    split.
    intros a b c c_nz eq.
    destruct (trichotomy a b) as [[ltq|eq']|ltq].
    -   apply (lt_rmult c c_nz) in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply (lt_rmult c c_nz) in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

(** OrderMultRcancel → MultRcancel *)
Local Instance mult_rcancel2 : MultRcancel U.
Proof.
    split.
    intros a b c c_nz eq.
    assert (a * c ≤ b * c) as leq1 by (rewrite eq; apply refl).
    assert (b * c ≤ a * c) as leq2 by (rewrite eq; apply refl).
    apply (le_mult_rcancel c c_nz) in leq1.
    apply (le_mult_rcancel c c_nz) in leq2.
    apply antisym; assumption.
Qed.

Local Remove Hints mult_lcancel1 mult_lcancel2 mult_rcancel1 mult_rcancel2
    : typeclass_instances.

End OrderPositive.
