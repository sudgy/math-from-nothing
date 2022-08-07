Require Import init.

Require Import nat.
Require Import int.
Require Import set.

Require Import fraction_base.
Require Import fraction_plus.
Require Import fraction_mult.
Require Import fraction_order.

Require Export nat_abstract.

Definition rat := frac int.
Definition int_to_rat (a : int) := to_frac int a : rat.
Definition nat_to_rat (a : nat) := int_to_rat (nat_to_int a) : rat.

Definition rat_not_trivial := frac_not_trivial int.
Definition rat_plus := frac_plus int.
Definition rat_plus_comm := frac_plus_comm int.
Definition rat_plus_assoc := frac_plus_assoc int.
Definition rat_zero := frac_zero int.
Definition rat_plus_lid := frac_plus_lid int.
Definition rat_neg := frac_neg int.
Definition rat_plus_linv := frac_plus_linv int.
Definition rat_mult := frac_mult int.
Definition rat_mult_comm := frac_mult_comm int.
Definition rat_mult_assoc := frac_mult_assoc int.
Definition rat_ldist := frac_ldist int.
Definition rat_one := frac_one int.
Definition rat_mult_lid := frac_mult_lid int.
Definition rat_div := frac_div int.
Definition rat_mult_linv := frac_mult_linv int.
Definition rat_order := frac_order int.
Definition rat_le_connex := frac_le_connex int.
Definition rat_le_antisym := frac_le_antisym int.
Definition rat_le_trans := frac_le_trans int.
Definition rat_le_lplus := frac_le_lplus int.
Definition rat_le_mult := frac_le_mult int.
Definition rat_arch := frac_arch int.
Global Existing Instances rat_not_trivial rat_plus rat_plus_comm rat_plus_assoc
    rat_zero rat_plus_lid rat_neg rat_plus_linv rat_mult rat_mult_comm
    rat_mult_assoc rat_ldist rat_one rat_mult_lid rat_div rat_mult_linv
    rat_order rat_le_connex rat_le_antisym rat_le_trans rat_le_lplus
    rat_le_mult rat_arch.

Theorem int_to_rat_eq : ∀ a b, int_to_rat a = int_to_rat b → a = b.
Proof.
    apply to_frac_eq.
Qed.

Theorem nat_to_rat_eq : ∀ a b, nat_to_rat a = nat_to_rat b → a = b.
Proof.
    intros a b eq.
    apply nat_to_int_eq.
    apply int_to_rat_eq.
    exact eq.
Qed.

Theorem int_to_rat_plus : ∀ a b,
    int_to_rat (a + b) = int_to_rat a + int_to_rat b.
Proof.
    apply to_frac_plus.
Qed.

Theorem nat_to_rat_plus : ∀ a b,
    nat_to_rat (a + b) = nat_to_rat a + nat_to_rat b.
Proof.
    intros a b.
    unfold nat_to_rat.
    rewrite nat_to_int_plus.
    rewrite int_to_rat_plus.
    reflexivity.
Qed.

Theorem int_to_rat_neg : ∀ a, int_to_rat (-a) = -int_to_rat a.
Proof.
    apply to_frac_neg.
Qed.

Theorem int_to_rat_mult : ∀ a b,
    int_to_rat (a * b) = int_to_rat a * int_to_rat b.
Proof.
    apply to_frac_mult.
Qed.

Theorem nat_to_rat_mult : ∀ a b,
    nat_to_rat (a * b) = nat_to_rat a * nat_to_rat b.
Proof.
    intros a b.
    unfold nat_to_rat.
    rewrite nat_to_int_mult.
    rewrite int_to_rat_mult.
    reflexivity.
Qed.

Theorem int_to_rat_le : ∀ a b, int_to_rat a <= int_to_rat b ↔ a <= b.
Proof.
    apply to_frac_le.
    exact int_le_antisym_class.
    exact int_le_trans_class.
Qed.
Theorem nat_to_rat_le : ∀ a b, nat_to_rat a <= nat_to_rat b ↔ a <= b.
Proof.
    intros a b.
    unfold nat_to_rat.
    rewrite int_to_rat_le.
    apply nat_to_int_le.
Qed.
Theorem int_to_rat_lt : ∀ a b, int_to_rat a < int_to_rat b ↔ a < b.
Proof.
    apply to_frac_lt.
    exact int_le_antisym_class.
    exact int_le_trans_class.
Qed.
Theorem nat_to_rat_lt : ∀ a b, nat_to_rat a < nat_to_rat b ↔ a < b.
Proof.
    intros a b.
    unfold nat_to_rat.
    rewrite int_to_rat_lt.
    apply nat_to_int_lt.
Qed.

Theorem nat_to_abstract_rat : ∀ a, nat_to_abstract a = nat_to_rat a.
Proof.
    nat_induction a.
    -   rewrite nat_to_abstract_zero.
        reflexivity.
    -   cbn.
        rewrite IHa.
        change (nat_suc a) with (1 + a).
        rewrite nat_to_rat_plus.
        reflexivity.
Qed.
