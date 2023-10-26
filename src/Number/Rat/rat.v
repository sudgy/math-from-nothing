Require Import init.

Require Import nat.
Require Import int.
Require Import set.

Require Export fraction_category.

Require Export nat_abstract.

Definition rat := ofrac int.

Definition rat_arch := ofrac_arch int.
Global Existing Instances rat_arch.

Theorem from_nat_rat : ∀ n, from_nat n = to_ofrac int (from_nat n).
Proof.
    intros n.
    nat_induction n.
    -   do 2 rewrite (homo_zero (f := from_nat)).
        symmetry; apply homo_zero.
    -   do 2 rewrite from_nat_suc.
        rewrite (homo_plus (f := to_ofrac int)).
        rewrite IHn.
        rewrite (homo_one (f := to_ofrac int)).
        reflexivity.
Qed.

Theorem from_int_rat : ∀ n, from_int n = to_ofrac int n.
Proof.
    intros a.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply int_pos_nat_ex in a_pos as [n a_eq]; subst a.
        rewrite from_int_nat.
        apply from_nat_rat.
    -   apply int_neg_nat_ex in a_neg as [n a_eq]; subst a.
        rewrite homo_neg.
        rewrite (homo_neg (f := to_ofrac int)).
        apply f_equal.
        rewrite from_int_nat.
        apply from_nat_rat.
Qed.
