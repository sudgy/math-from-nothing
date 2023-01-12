Require Import init.

Require Export nat.
Require Export set_type.

Definition nat_to_set n := λ x, x < n.
Definition nat_to_set_type n := set_type (nat_to_set n).

Theorem nat_lt_0_false : nat_to_set_type 0 → False.
Proof.
    intros [x x_lt].
    contradiction (nat_neg2 x_lt).
Qed.
