Require Import init.

Require Export nat_base.
Require Export nat_plus.
Require Export nat_mult.
Require Export nat_order.
Require Export nat_binom.

Fixpoint nat_mult {U} `{Plus U, Zero U} (a : nat) (b : U) :=
    match a with
    | nat_zero => 0
    | nat_suc a' => b + nat_mult a' b
    end.
Infix "×" := nat_mult (at level 40, left associativity).
Arguments nat_mult : simpl never.

Fixpoint nat_pow {U} `{Mult U} `{One U} a b :=
    match b with
    | nat_zero => 1
    | nat_suc b' => nat_pow a b' * a
    end.
Infix "^" := nat_pow : nat_scope.
Arguments nat_pow : simpl never.

(* begin hide *)
Section NatAbstract.

Context {U} `{OrderedFieldClass U}.
Local Open Scope nat_scope.
(* end hide *)
Theorem nat_mult_lanni : ∀ a, 0 × a = 0.
Proof.
    reflexivity.
Qed.

Theorem nat_mult_suc : ∀ n a, (nat_suc n) × a = a + n × a.
Proof.
    reflexivity.
Qed.

Theorem nat_mult_ranni : ∀ a, a × 0 = 0.
Proof.
    intros a.
    nat_induction a.
    -   apply nat_mult_lanni.
    -   rewrite nat_mult_suc.
        rewrite plus_lid.
        exact IHa.
Qed.

Theorem nat_mult_lid : ∀ a, 1 × a = a.
Proof.
    intros a.
    rewrite <- nat_one_eq.
    rewrite nat_mult_suc, nat_mult_lanni.
    apply plus_rid.
Qed.

Theorem nat_mult_commute_single :
    ∀ a b c, b + c = c + b → a × b + c = c + a × b.
Proof.
    intros a b c comm.
    nat_induction a.
    -   rewrite nat_mult_lanni.
        rewrite plus_lid, plus_rid.
        reflexivity.
    -   rewrite nat_mult_suc.
        rewrite <- plus_assoc.
        rewrite IHa.
        do 2 rewrite plus_assoc.
        rewrite comm.
        reflexivity.
Qed.

Theorem nat_mult_ldist_comm : ∀ a b c, b + c = c + b →
    a × (b + c) = a × b + a × c.
Proof.
    intros a b c comm.
    nat_induction a.
    -   do 3 rewrite nat_mult_lanni.
        rewrite plus_lid.
        reflexivity.
    -   do 3 rewrite nat_mult_suc.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        rewrite IHa.
        do 2 rewrite plus_assoc.
        rewrite nat_mult_commute_single by exact comm.
        reflexivity.
Qed.

Theorem nat_mult_ldist : ∀ a b c, a × (b + c) = a × b + a × c.
Proof.
    intros a b c.
    apply nat_mult_ldist_comm.
    apply plus_comm.
Qed.

Theorem nat_mult_rdist : ∀ a b c, (a + b) × c = a × c + b × c.
Proof.
    intros a b c.
    nat_induction a.
    -   rewrite nat_mult_lanni.
        do 2 rewrite plus_lid.
        reflexivity.
    -   rewrite nat_plus_lsuc.
        do 2 rewrite nat_mult_suc.
        rewrite IHa.
        apply plus_assoc.
Qed.

Theorem nat_mult_mult : ∀ a b c, a × (b × c) = (a * b) × c.
Proof.
    intros a b c.
    nat_induction a.
    -   rewrite mult_lanni.
        do 2 rewrite nat_mult_lanni.
        reflexivity.
    -   rewrite nat_mult_suc.
        rewrite nat_mult_lsuc.
        rewrite IHa.
        rewrite nat_mult_rdist.
        reflexivity.
Qed.

Theorem nat_mult_assoc : ∀ a b c, a × (b * c) = (a × b) * c.
Proof.
    intros a b c.
    nat_induction a.
    -   do 2 rewrite nat_mult_lanni.
        rewrite mult_lanni.
        reflexivity.
    -   do 2 rewrite nat_mult_suc.
        rewrite IHa.
        rewrite rdist.
        reflexivity.
Qed.

Theorem nat_mult_rneg : ∀ a b, -(a × b) = a × (-b).
Proof.
    intros a b.
    nat_induction a.
    -   do 2 rewrite nat_mult_lanni.
        apply neg_zero.
    -   do 2 rewrite nat_mult_suc.
        rewrite neg_plus_group.
        rewrite IHa.
        rewrite <- (nat_mult_lid (-b)) at 2.
        rewrite <- nat_mult_rdist.
        rewrite (plus_comm a 1).
        rewrite nat_mult_rdist.
        rewrite nat_mult_lid.
        reflexivity.
Qed.

Theorem nat_mult_commute_double :
    ∀ a b c d, c + d = d + c → a × c + b × d = b × d + a × c.
Proof.
    intros a b c d comm.
    nat_induction a.
    -   rewrite nat_mult_lanni.
        rewrite plus_lid, plus_rid.
        reflexivity.
    -   rewrite nat_mult_suc.
        rewrite <- plus_assoc.
        rewrite IHa.
        do 2 rewrite plus_assoc.
        apply rplus.
        rewrite nat_mult_commute_single by (symmetry; exact comm).
        reflexivity.
Qed.

Theorem nat_mult_commute : ∀ a b c, a × c + b × c = b × c + a × c.
Proof.
    intros a b c.
    apply nat_mult_commute_double.
    reflexivity.
Qed.

Theorem nat_mult_commute_neg : ∀ a b c, a × c - b × c = -(b × c) + a × c.
Proof.
    intros a b c.
    rewrite nat_mult_rneg.
    apply nat_mult_commute_double.
    rewrite plus_linv, plus_rinv.
    reflexivity.
Qed.

Theorem nat_pow_zero : ∀ a, a ^ 0 = 1.
Proof.
    reflexivity.
Qed.

Theorem nat_pow_suc : ∀ a n, a ^ (nat_suc n) = a^n * a.
Proof.
    reflexivity.
Qed.

Theorem zero_nat_pow : ∀ n, 0 ^ (nat_suc n) = 0.
Proof.
    intros n.
    rewrite nat_pow_suc.
    apply mult_ranni.
Qed.

Theorem nat_pow_one : ∀ a, a ^ 1 = a.
Proof.
    intros a.
    rewrite <- nat_one_eq.
    rewrite nat_pow_suc.
    rewrite nat_pow_zero.
    apply mult_lid.
Qed.

Theorem one_nat_pow : ∀ n, 1 ^ n = 1.
Proof.
    nat_induction n.
    -   apply nat_pow_zero.
    -   rewrite nat_pow_suc.
        rewrite IHn.
        apply mult_lid.
Qed.

Theorem nat_pow_plus : ∀ a m n, a ^ (m + n) = a ^ m * a ^ n.
Proof.
    intros a m n.
    nat_induction n.
    -   rewrite nat_pow_zero, mult_rid.
        rewrite plus_rid.
        reflexivity.
    -   rewrite nat_plus_rsuc.
        do 2 rewrite nat_pow_suc.
        rewrite IHn.
        rewrite mult_assoc.
        reflexivity.
Qed.

Theorem nat_pow_mult : ∀ a b n, (a * b) ^ n = a ^ n * b ^ n.
Proof.
    intros a b n.
    nat_induction n.
    -   do 3 rewrite nat_pow_zero.
        rewrite mult_lid.
        reflexivity.
    -   do 3 rewrite nat_pow_suc.
        rewrite IHn.
        do 2 rewrite <- mult_assoc.
        apply lmult.
        do 2 rewrite mult_assoc.
        apply rmult.
        apply mult_comm.
Qed.

Theorem nat_pow_pow : ∀ a m n, (a ^ m) ^ n = a ^ (m * n).
Proof.
    intros a m n.
    nat_induction n.
    -   rewrite mult_ranni.
        do 2 rewrite nat_pow_zero.
        reflexivity.
    -   rewrite nat_pow_suc.
        rewrite IHn.
        rewrite nat_mult_rsuc.
        rewrite nat_pow_plus.
        apply mult_comm.
Qed.

Theorem nat_pow_not_zero : ∀ a n, 0 ≠ a → 0 ≠ a ^ n.
Proof.
    intros a n a_nz eq.
    nat_induction n.
    -   rewrite nat_pow_zero in eq.
        exact (not_trivial_one eq).
    -   apply IHn.
        rewrite nat_pow_suc in eq.
        pose proof (mult_zero _ _ eq) as [an_z|a_z].
        +   exact an_z.
        +   contradiction.
Qed.

Theorem nat_pow_neg_even : ∀ n, (-1) ^ (2*n) = 1.
Proof.
    intros n.
    nat_induction n.
    -   rewrite mult_ranni.
        apply nat_pow_zero.
    -   rewrite nat_mult_rsuc.
        rewrite nat_pow_plus.
        rewrite IHn.
        rewrite mult_rid.
        rewrite nat_pow_plus.
        rewrite nat_pow_one.
        rewrite mult_neg_one.
        apply neg_neg.
Qed.

Theorem nat_pow_neg_odd : ∀ n, (-1) ^ (2*n + 1) = -1.
Proof.
    intros n.
    rewrite nat_pow_plus.
    rewrite nat_pow_neg_even.
    rewrite mult_lid.
    apply nat_pow_one.
Qed.

Theorem nat_pow_neg_binom2 : ∀ n,
    (-1) ^ binom (nat_suc (nat_suc n)) 2 = -(-1) ^ binom n 2.
Proof.
    intros n.
    change 2 with (nat_suc (nat_suc 0)) at 1.
    do 3 rewrite binom_suc.
    rewrite binom_zero.
    rewrite binom_one.
    rewrite <- plus_assoc.
    rewrite nat_pow_plus.
    rewrite nat_pow_one.
    rewrite mult_neg_one.
    rewrite plus_assoc.
    rewrite plus_two.
    rewrite nat_pow_plus.
    rewrite nat_pow_neg_even.
    rewrite mult_lid.
    reflexivity.
Qed.

Theorem nat_pow_pos : ∀ a n, 0 ≤ a → 0 ≤ a^n.
Proof.
    intros a n a_pos.
    nat_induction n.
    -   rewrite nat_pow_zero.
        apply one_pos.
    -   rewrite nat_pow_suc.
        apply le_mult; assumption.
Qed.

Theorem nat_pow_pos2 : ∀ a n, 0 < a → 0 < a^n.
Proof.
    intros a n a_pos.
    nat_induction n.
    -   rewrite nat_pow_zero.
        exact one_pos.
    -   rewrite nat_pow_suc.
        apply lt_mult; assumption.
Qed.

Theorem nat_pow_le : ∀ a m n, 1 ≤ a → m ≤ n → a^m ≤ a^n.
Proof.
    intros a m n a_ge mn.
    apply nat_le_ex in mn as [c eq]; subst.
    nat_induction c; [>rewrite plus_rid; apply refl|].
    rewrite nat_plus_rsuc.
    rewrite nat_pow_suc.
    apply (trans IHc).
    rewrite <- le_mult_1_a_b_ba_pos.
    +   exact a_ge.
    +   apply nat_pow_pos2.
        exact (lt_le_trans one_pos a_ge).
Qed.

Theorem nat_pow_lt : ∀ a m n, 1 < a → m < n → a^m < a^n.
Proof.
    intros a m n a_gt mn.
    assert (∀ n, a ^ n < a ^ n * a) as lemma.
    {
        clear m n mn.
        intros n.
        rewrite <- lt_mult_1_a_b_ba_pos.
        +   exact a_gt.
        +   apply nat_pow_pos2.
            exact (trans one_pos a_gt).
    }
    apply nat_lt_ex in mn as [c eq]; subst.
    rewrite nat_plus_rsuc.
    nat_induction c.
    -   rewrite plus_rid.
        apply lemma.
    -   rewrite nat_pow_suc.
        apply (trans IHc).
        rewrite nat_plus_rsuc.
        apply lemma.
Qed.

Theorem nat_pow_le_one : ∀ a n, 1 ≤ a → 1 ≤ a^n.
Proof.
    intros a n a_one.
    nat_induction n.
    -   rewrite nat_pow_zero.
        apply refl.
    -   rewrite nat_pow_suc.
        rewrite <- (mult_lid 1).
        apply le_lrmult_pos; [>
            apply one_pos|
            apply one_pos|
            exact IHn|
            exact a_one
        ].
Qed.

Theorem nat_pow_lt_one : ∀ a n, 1 < a → 1 < a^(nat_suc n).
Proof.
    intros a n a_one.
    nat_induction n.
    -   rewrite nat_pow_one.
        exact a_one.
    -   rewrite nat_pow_suc.
        rewrite <- (mult_lid 1).
        apply lt_lrmult_pos; [>
            apply one_pos|
            apply one_pos|
            exact IHn|
            exact a_one
        ].
Qed.
(* begin hide *)
End NatAbstract.
(* end hide *)
