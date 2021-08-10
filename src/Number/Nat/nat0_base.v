Require Import init.

Declare Scope nat0_scope.
Delimit Scope nat0_scope with nat0.

Inductive nat0 : Set :=
    | nat0_zero : nat0
    | nat0_suc : nat0 → nat0.
Bind Scope nat0_scope with nat0.

Theorem nat0_neq_suc : ∀ n, n ≠ nat0_suc n.
    induction n.
    -   intro contr; inversion contr.
    -   intro contr.
        inversion contr.
        contradiction.
Qed.
