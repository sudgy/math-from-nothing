Require Import init.

Require Export plus_group.
Require Import nat_base.
Require Import nat_plus.
Require Import nat_order.

(* This will sum all of the terms in the range [m, m + n) *)
Fixpoint sum {U} `{Plus U, Zero U} (a : nat → U) (m n : nat) :=
    match n with
    |   nat_zero => zero
    |   nat_suc n' => sum a m n' + a (m + n')
    end.

(* begin hide *)
Section Sum.

Context {U} `{AllPlusClass U}.

(* end hide *)
Theorem sum_zero : ∀ f m, sum f m 0 = 0.
Proof.
    reflexivity.
Qed.

Theorem sum_suc : ∀ f m n, sum f m (nat_suc n) = sum f m n + f (m + n).
Proof.
    reflexivity.
Qed.

Arguments sum : simpl never.

Theorem sum_eq : ∀ f g m n, (∀ a, a < n → f (m + a) = g (m + a)) →
    sum f m n = sum g m n.
Proof.
    intros f g m n all_eq.
    nat_induction n.
    -   do 2 rewrite sum_zero.
        reflexivity.
    -   prove_parts IHn.
        {
            intros a a_ltq.
            apply all_eq.
            exact (trans a_ltq (nat_lt_suc _)).
        }
        do 2 rewrite sum_suc.
        rewrite all_eq by apply nat_lt_suc.
        rewrite IHn.
        reflexivity.
Qed.

Theorem sum_zero_all : ∀ m n, sum (λ _, 0) m n = 0.
Proof.
    intros m n.
    nat_induction n.
    -   apply sum_zero.
    -   rewrite sum_suc.
        rewrite plus_rid.
        exact IHn.
Qed.

Theorem sum_zero_eq : ∀ f m n, (∀ a, a < n → f (m + a) = 0) → sum f m n = 0.
Proof.
    intros f a b n_zero.
    rewrite <- (sum_zero_all a b).
    apply sum_eq.
    exact n_zero.
Qed.

Theorem sum_plus : ∀ f a b c, sum f a b + sum f (a + b) c = sum f a (b + c).
Proof.
    intros f a b c.
    nat_induction c.
    -   rewrite plus_rid.
        rewrite sum_zero.
        apply plus_rid.
    -   rewrite nat_plus_rsuc.
        do 2 rewrite sum_suc.
        rewrite plus_assoc.
        rewrite IHc.
        rewrite plus_assoc.
        reflexivity.
Qed.

Theorem sum_minus : ∀ f a b c, sum f a (b + c) - sum f a b = sum f (a + b) c.
Proof.
    intros f a b c.
    rewrite <- plus_rrmove.
    symmetry; rewrite plus_comm.
    apply sum_plus.
Qed.

Theorem sum_argument_plus : ∀ f a b c,
    sum (λ n, f (n + c)) a b = sum f (a + c) b.
Proof.
    intros f a b c.
    nat_induction b.
    -   do 2 rewrite sum_zero.
        reflexivity.
    -   do 2 rewrite sum_suc.
        rewrite IHb.
        do 2 apply f_equal.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        apply plus_comm.
Qed.

Theorem sum_func_plus : ∀ f g m n,
    sum (λ n, f n + g n) m n = sum f m n + sum g m n.
Proof.
    intros f g m n.
    nat_induction n.
    -   do 3 rewrite sum_zero.
        symmetry; apply plus_rid.
    -   do 3 rewrite sum_suc.
        rewrite IHn.
        apply plus_4.
Qed.

Theorem sum_func_neg : ∀ f m n, sum (λ n, -f n) m n = -sum f m n.
Proof.
    intros f m n.
    nat_induction n.
    -   do 2 rewrite sum_zero.
        symmetry; apply neg_zero.
    -   do 2 rewrite sum_suc.
        rewrite IHn.
        symmetry; apply neg_plus.
Qed.

(* begin hide *)
End Sum.
