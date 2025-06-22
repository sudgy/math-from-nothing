Require Import init.

Require Export nat_plus.
Require Export nat_mult.
Require Export nat_order.

Fixpoint binom n k :=
    match n, k with
    | _, nat_zero => 1
    | nat_zero, nat_suc k' => 0
    | nat_suc n', nat_suc k' => binom n' k' + binom n' (nat_suc k')
    end.

Fixpoint factorial n :=
    match n with
    | nat_zero => 1
    | nat_suc n' => n * factorial n'
    end.

Theorem binom_suc : ∀ n k,
    binom (nat_suc n) (nat_suc k) = binom n k + binom n (nat_suc k).
Proof.
    reflexivity.
Qed.

Theorem binom_zero : ∀ n, binom n 0 = 1.
Proof.
    intros n.
    destruct n; reflexivity.
Qed.

Theorem binom_one : ∀ n, binom n 1 = n.
Proof.
    intros n.
    nat_induction n.
    -   reflexivity.
    -   change 1 with (nat_suc 0).
        rewrite binom_suc.
        rewrite binom_zero.
        rewrite IHn.
        reflexivity.
Qed.

Theorem binom_greater : ∀ n k, n < k → binom n k = 0.
Proof.
    nat_induction n; intros k ltq.
    -   nat_destruct k.
        +   destruct ltq; contradiction.
        +   unfold zero at 1; cbn.
            reflexivity.
    -   nat_destruct k.
        +   contradiction (not_neg ltq).
        +   cbn.
            rewrite nat_sucs_lt in ltq.
            rewrite IHn by exact ltq.
            rewrite IHn by (exact (trans ltq (nat_lt_suc k))).
            apply plus_rid.
Qed.

Theorem binom_eq : ∀ n, binom n n = 1.
Proof.
    intros n.
    nat_induction n.
    -   apply binom_zero.
    -   cbn.
        rewrite IHn.
        rewrite binom_greater by apply nat_lt_suc.
        apply plus_rid.
Qed.

Theorem factorial_zero : factorial 0 = 1.
Proof.
    reflexivity.
Qed.

Theorem factorial_suc : ∀ n, factorial (nat_suc n) = nat_suc n * factorial n.
Proof.
    reflexivity.
Qed.

Theorem factorial_nz : ∀ n, 0 ≠ factorial n.
Proof.
    intros n.
    nat_induction n.
    -   apply nat_zero_suc.
    -   intros contr.
        cbn in contr.
        rewrite <- (mult_ranni (nat_suc n)) in contr.
        apply mult_lcancel in contr.
        +   contradiction.
        +   apply nat_zero_suc.
Qed.

Theorem binom_fact : ∀ m n,
    binom (n + m) n * factorial n * factorial m = factorial (n + m).
Proof.
    nat_induction m; intros n.
    -   rewrite plus_rid.
        rewrite factorial_zero.
        rewrite binom_eq.
        rewrite mult_lid, mult_rid.
        reflexivity.
    -   nat_induction n.
        +   rewrite plus_lid.
            rewrite factorial_zero.
            rewrite binom_zero.
            do 2 rewrite mult_lid.
            reflexivity.
        +   rewrite nat_plus_lsuc.
            rewrite binom_suc.
            rewrite (factorial_suc (n + nat_suc m)).
            rewrite <- nat_plus_lsuc.
            rewrite (rdist (nat_suc n)).
            rewrite <- nat_plus_lrsuc at 4.
            rewrite <- IHn, <- IHm.
            clear IHm IHn.
            do 2 rewrite rdist.
            rewrite nat_plus_lrsuc.
            apply lrplus.
            *   rewrite factorial_suc.
                do 3 rewrite mult_assoc.
                do 2 apply rmult.
                apply mult_comm.
            *   rewrite (mult_comm (nat_suc m)).
                do 3 rewrite <- mult_assoc.
                do 2 apply lmult.
                rewrite mult_comm.
                apply factorial_suc.
Qed.

Theorem binom_opposite : ∀ m n, binom (m + n) m = binom (m + n) n.
Proof.
    intros m n.
    apply mult_rcancel with (factorial m); [>apply factorial_nz|].
    apply mult_rcancel with (factorial n); [>apply factorial_nz|].
    rewrite binom_fact.
    rewrite plus_comm.
    rewrite <- mult_assoc.
    rewrite (mult_comm (factorial m)).
    rewrite mult_assoc.
    rewrite binom_fact.
    reflexivity.
Qed.

Arguments binom: simpl never.
