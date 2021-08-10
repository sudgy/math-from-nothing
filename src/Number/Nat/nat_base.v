Require Import init.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.

Inductive nat : Set :=
    | nat_zero : nat
    | nat_suc : nat → nat.
Bind Scope nat_scope with nat.

Theorem nat_neq_suc : ∀ n, n ≠ nat_suc n.
    induction n.
    -   intro contr; inversion contr.
    -   intro contr.
        inversion contr.
        contradiction.
Qed.
