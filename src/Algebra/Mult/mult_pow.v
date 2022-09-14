Require Import init.

Require Import nat.

Fixpoint pow_nat {U} `{Mult U} `{One U} a b :=
    match b with
    | nat_zero => 1
    | nat_suc b' => pow_nat a b' * a
    end.
Infix "^" := pow_nat : nat_scope.

(* begin hide *)
Section Pow.

Context {U} `{OrderedField U, @Archimedean U UP UZ UO}.

Local Open Scope nat_scope.
(* end hide *)
Theorem pow_simpl : ∀ a n, a ^ (nat_suc n) = a^n * a.
Proof.
    intros; reflexivity.
Qed.

Theorem pow_0_nat : ∀ a, a ^ 0 = 1.
Proof.
    intros a.
    unfold zero; cbn.
    reflexivity.
Qed.

Theorem pow_1_nat : ∀ a, a ^ 1 = a.
Proof.
    intros a.
    unfold one; cbn.
    apply mult_lid.
Qed.

Theorem one_pow_nat : ∀ n, 1 ^ n = 1.
Proof.
    nat_induction n.
    -   apply pow_0_nat.
    -   cbn.
        rewrite IHn.
        apply mult_lid.
Qed.

Theorem pow_mult_nat : ∀ a m n, a ^ m * a ^ n = a ^ (m + n).
Proof.
    intros a m n.
    nat_induction n.
    -   rewrite pow_0_nat, mult_rid.
        rewrite plus_rid.
        reflexivity.
    -   rewrite nat_plus_rsuc.
        cbn.
        rewrite mult_assoc.
        rewrite IHn.
        reflexivity.
Qed.

Theorem pow_mult_mult_nat : ∀ a m n, (a ^ m) ^ n = a ^ (m * n).
Proof.
    intros a m n.
    nat_induction n.
    -   rewrite mult_ranni.
        do 2 rewrite pow_0_nat.
        reflexivity.
    -   cbn.
        rewrite IHn.
        rewrite pow_mult_nat.
        rewrite nat_mult_rsuc.
        rewrite plus_comm.
        reflexivity.
Qed.

Theorem pow_not_zero_nat : ∀ a n, 0 ≠ a → 0 ≠ a ^ n.
Proof.
    intros a n a_nz eq.
    nat_induction n.
    -   rewrite pow_0_nat in eq.
        apply not_trivial_one.
        exact eq.
    -   apply IHn.
        cbn in eq.
        rewrite <- (mult_lanni a) in eq.
        apply mult_rcancel in eq; auto.
Qed.

Theorem pow_neg_one_even : ∀ n, (-(1)) ^ (2*n) = 1.
Proof.
    intros n.
    nat_induction n.
    -   rewrite mult_ranni.
        apply pow_0_nat.
    -   rewrite nat_mult_rsuc.
        rewrite <- pow_mult_nat.
        rewrite IHn.
        rewrite mult_rid.
        unfold one at 2 3, plus; cbn.
        rewrite mult_lid.
        rewrite mult_neg_one.
        apply neg_neg.
Qed.

Theorem pow_neg_one_odd : ∀ n, (-(1)) ^ (2*n + 1) = -(1).
Proof.
    intros n.
    rewrite <- pow_mult_nat.
    rewrite pow_neg_one_even.
    rewrite mult_lid.
    apply pow_1_nat.
Qed.

Theorem pow_neg_one_binom2 : ∀ n,
        (-(1)) ^ binom (nat_suc (nat_suc n)) 2 = -(-(1)) ^ binom n 2.
Proof.
    intros n.
    change 2 with (nat_suc (nat_suc 0)) at 1.
    do 3 rewrite binom_suc.
    rewrite binom_zero.
    rewrite binom_one.
    rewrite <- plus_assoc.
    rewrite <- pow_mult_nat.
    rewrite pow_1_nat.
    rewrite mult_neg_one.
    rewrite plus_assoc.
    rewrite <- (mult_lid n) at 1 2.
    rewrite <- rdist.
    rewrite <- pow_mult_nat.
    rewrite pow_neg_one_even.
    rewrite mult_lid.
    reflexivity.
Qed.

Theorem pow_pos : ∀ a n, 0 <= a → 0 <= a^n.
Proof.
    intros a n a_pos.
    nat_induction n.
    -   rewrite pow_0_nat.
        apply one_pos.
    -   cbn.
        apply le_mult; assumption.
Qed.

Theorem pow_pos2 : ∀ a n, 0 < a → 0 < a^n.
Proof.
    intros a n a_pos.
    nat_induction n.
    -   rewrite pow_0_nat.
        exact one_pos.
    -   cbn.
        apply lt_mult; assumption.
Qed.

Theorem pow_le : ∀ a m n, 1 <= a → m <= n → a^m <= a^n.
Proof.
    intros a m n a_ge mn.
    apply nat_le_ex in mn as [c eq]; subst.
    nat_induction c; [>rewrite plus_rid; apply refl|].
    rewrite nat_plus_rsuc.
    cbn.
    apply (trans IHc).
    rewrite <- le_mult_1_a_b_ba_pos.
    +   exact a_ge.
    +   apply pow_pos2.
        exact (lt_le_trans one_pos a_ge).
Qed.

Theorem pow_lt : ∀ a m n, 1 < a → m < n → a^m < a^n.
Proof.
    intros a m n a_gt mn.
    apply nat_lt_ex in mn as [c [c_nz eq]]; subst.
    nat_destruct c; [>contradiction|].
    clear c_nz.
    rewrite nat_plus_rsuc.
    nat_induction c.
    -   rewrite plus_rid.
        cbn.
        rewrite <- lt_mult_1_a_b_ba_pos.
        +   exact a_gt.
        +   apply pow_pos2.
            exact (trans one_pos a_gt).
    -   cbn.
        apply (trans IHc).
        rewrite nat_plus_rsuc.
        rewrite <- lt_mult_1_a_b_ba_pos.
        +   exact a_gt.
        +   apply pow_pos2.
            exact (trans one_pos a_gt).
Qed.

Theorem arch_pow2 : ∀ ε, 0 < ε → ∃ n, /(2^n) < ε.
Proof.
    intros ε ε_pos.
    pose proof (archimedean2 ε ε_pos) as [n ltq].
    exists (nat_suc n).
    apply (trans2 ltq).
    apply lt_div_pos; [>apply from_nat_pos|].
    clear ltq.
    nat_induction n.
    -   rewrite from_nat_one.
        rewrite pow_1_nat.
        rewrite <- lt_plus_0_a_b_ba.
        exact one_pos.
    -   rewrite from_nat_suc.
        apply lt_lplus with 1 in IHn.
        apply (trans IHn).
        rewrite (pow_simpl _ (nat_suc n)).
        rewrite ldist.
        rewrite mult_rid.
        apply lt_rplus.
        clear IHn.
        nat_induction n.
        +   rewrite pow_1_nat.
            rewrite <- lt_plus_0_a_b_ba.
            exact one_pos.
        +   apply (trans IHn).
            rewrite (pow_simpl _ (nat_suc n)).
            rewrite <- (mult_rid (2^nat_suc n)) at 1.
            apply lt_lmult_pos.
            *   apply pow_pos2.
                exact two_pos.
            *   rewrite <- lt_plus_0_a_b_ba.
                exact one_pos.
Qed.
(* begin hide *)
End Pow.
(* end hide *)
