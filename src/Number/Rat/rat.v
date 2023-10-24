Require Import init.

Require Import nat.
Require Import int.
Require Import set.

Require Import fraction_base.
Require Import fraction_plus.
Require Import fraction_mult.
Require Import fraction_order.

Require Export nat_abstract.

Definition rat := frac_type int.
Definition int_to_rat (a : int) := to_frac int a : rat.
Definition nat_to_rat (a : nat) := int_to_rat (from_nat a) : rat.

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
Definition int_to_rat_inj := to_frac_inj int.
Definition int_to_rat_plus := to_frac_plus int.
Definition int_to_rat_mult := to_frac_mult int.
Definition int_to_rat_le := to_frac_le int.
Global Existing Instances rat_not_trivial rat_plus rat_plus_comm rat_plus_assoc
    rat_zero rat_plus_lid rat_neg rat_plus_linv rat_mult rat_mult_comm
    rat_mult_assoc rat_ldist rat_one rat_mult_lid rat_div rat_mult_linv
    rat_order rat_le_connex rat_le_antisym rat_le_trans rat_le_lplus
    rat_le_mult rat_arch int_to_rat_inj int_to_rat_plus int_to_rat_mult
    int_to_rat_le.

Theorem nat_to_rat_eq : ∀ a b, nat_to_rat a = nat_to_rat b → a = b.
Proof.
    intros a b eq.
    apply (inj (f := (from_nat (U := int)))).
    apply inj.
    exact eq.
Qed.

Theorem nat_to_rat_plus : ∀ a b,
    nat_to_rat (a + b) = nat_to_rat a + nat_to_rat b.
Proof.
    intros a b.
    unfold nat_to_rat.
    setoid_rewrite homo_plus.
    setoid_rewrite homo_plus.
    reflexivity.
Qed.

Theorem nat_to_rat_mult : ∀ a b,
    nat_to_rat (a * b) = nat_to_rat a * nat_to_rat b.
Proof.
    intros a b.
    unfold nat_to_rat.
    setoid_rewrite homo_mult.
    setoid_rewrite homo_mult.
    reflexivity.
Qed.

Theorem nat_to_rat_le : ∀ a b, nat_to_rat a ≤ nat_to_rat b ↔ a ≤ b.
Proof.
    intros a b.
    unfold nat_to_rat.
    rewrite <- homo_le2.
    symmetry; apply homo_le2.
Qed.
Theorem nat_to_rat_lt : ∀ a b, nat_to_rat a < nat_to_rat b ↔ a < b.
Proof.
    intros a b.
    unfold nat_to_rat.
    rewrite <- homo_lt2.
    symmetry; apply homo_lt2.
Qed.

Theorem from_nat_rat : ∀ a, from_nat a = nat_to_rat a.
Proof.
    nat_induction a.
    -   rewrite homo_zero.
        reflexivity.
    -   rewrite from_nat_suc.
        rewrite IHa.
        change (nat_suc a) with (1 + a).
        rewrite nat_to_rat_plus.
        unfold nat_to_rat at 2.
        setoid_rewrite homo_one.
        reflexivity.
Qed.
