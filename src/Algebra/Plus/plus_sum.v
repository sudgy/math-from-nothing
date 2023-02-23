Require Import init.

Require Export plus_group.
Require Import nat.

(* This will sum all of the terms in the range [m, m + n) *)
Fixpoint sum {U} `{Plus U, Zero U} (a : nat → U) (m n : nat) :=
    match n with
    |   nat_zero => zero
    |   nat_suc n' => sum a m n' + a (m + n')
    end.

(* begin hide *)
Section Sum.

Context {U} `{AllPlus U}.

(* end hide *)
Theorem sum_eq : ∀ f g m n, (∀ a, a < n → f (m + a) = g (m + a)) →
    sum f m n = sum g m n.
Proof.
    intros f g m n all_eq.
    revert all_eq.
    nat_induction n.
    -   intros all_eq.
        unfold zero; cbn.
        reflexivity.
    -   intros all_eq.
        cbn.
        rewrite IHn.
        rewrite all_eq.
        +   reflexivity.
        +   apply nat_lt_suc.
        +   intros a a_ltq.
            rewrite all_eq.
            *   reflexivity.
            *   exact (trans a_ltq (nat_lt_suc _)).
Qed.

Theorem sum_minus : ∀ f a b c, sum f a (b + c) - sum f a b = sum f (a + b) c.
Proof.
    intros f a b c.
    nat_induction c.
    -   rewrite plus_rid.
        rewrite plus_rinv.
        unfold zero at 2; cbn.
        reflexivity.
    -   rewrite nat_plus_rsuc.
        cbn.
        rewrite <- plus_assoc.
        rewrite (plus_comm (f (a + (b + c)))).
        rewrite plus_assoc.
        rewrite IHc.
        rewrite plus_assoc.
        reflexivity.
Qed.

Theorem sum_zero : ∀ f a b, (∀ n, a ≤ n → n < a + b → f n = 0) → sum f a b = 0.
Proof.
    intros f a b n_zero.
    nat_induction b.
    -   unfold zero at 1; cbn.
        reflexivity.
    -   cbn.
        rewrite <- (plus_rid 0).
        apply lrplus.
        +   apply IHb.
            intros n n_geq n_ltq.
            apply n_zero.
            *   exact n_geq.
            *   rewrite nat_plus_rsuc.
                apply (trans n_ltq).
                apply nat_lt_suc.
        +   apply n_zero.
            *   apply nat_le_self_rplus.
            *   rewrite nat_plus_rsuc.
                apply nat_lt_suc.
Qed.

Theorem sum_argument_plus : ∀ f a b c, sum (λ n, f (n + c)) a b = sum f (a + c) b.
Proof.
    intros f a b c.
    nat_induction b.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        rewrite IHb.
        rewrite <- plus_assoc.
        rewrite (plus_comm b c).
        rewrite plus_assoc.
        reflexivity.
Qed.

Theorem sum_plus : ∀ f a b c, sum f a b + sum f (a + b) c = sum f a (b + c).
Proof.
    intros f a b c.
    nat_induction c.
    -   rewrite plus_rid.
        unfold zero; cbn.
        apply plus_rid.
    -   rewrite nat_plus_rsuc.
        cbn.
        rewrite plus_assoc.
        rewrite IHc.
        rewrite plus_assoc.
        reflexivity.
Qed.

(* begin hide *)
End Sum.
