Require Import init.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.

Inductive nat : Set :=
    | nat_zero : nat
    | nat_suc : nat → nat.
Bind Scope nat_scope with nat.

Theorem nat_zero_suc : ∀ {n}, nat_zero ≠ nat_suc n.
Proof.
    intros n eq.
    inversion eq.
Qed.

Theorem nat_suc_eq : ∀ {a b}, nat_suc a = nat_suc b ↔ a = b.
Proof.
    intros a b.
    split.
    -   intros eq.
        inversion eq.
        reflexivity.
    -   intros eq.
        subst.
        reflexivity.
Qed.

Theorem nat_neq_suc : ∀ n, n ≠ nat_suc n.
Proof.
    induction n.
    -   apply nat_zero_suc.
    -   intro contr.
        rewrite nat_suc_eq in contr.
        contradiction.
Qed.
