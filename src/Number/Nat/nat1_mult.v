Require Import init.

Require Export mult.

Require Import nat1_plus.
Require Import nat0_base.
Require Import nat0_mult.

Fixpoint nat1_mult a b :=
    match a with
        | nat1_suc a' => b + nat1_mult a' b
        | nat1_one => b
    end.

Instance nat1_mult_class : Mult nat1 := {
    mult := nat1_mult;
}.

Instance nat1_mult_one : One nat1 := {
    one := nat1_one
}.

Ltac nat1_induction n :=
    induction n;
    change nat1_one with (one (U := nat1)) in *.
Ltac nat1_destruct n :=
    destruct n;
    change nat1_one with (one (U := nat1)) in *.

Theorem nat1_to_nat0_mult : ∀ a b,
        nat1_to_nat0 a * nat1_to_nat0 b = nat1_to_nat0 (a * b).
    nat1_induction a.
    -   intros b.
        unfold one, mult at 2; cbn.
        apply mult_lid.
    -   intros b.
        unfold mult at 2; cbn.
        rewrite nat0_mult_lsuc.
        rewrite IHa.
        rewrite nat1_to_nat0_plus.
        reflexivity.
Qed.

Lemma nat1_mult_comm : ∀ a b, a * b = b * a.
    intros a b.
    apply nat1_to_nat0_eq.
    do 2 rewrite <- nat1_to_nat0_mult.
    apply mult_comm.
Qed.
Instance nat1_mult_comm_class : MultComm nat1 := {
    mult_comm := nat1_mult_comm
}.

Lemma nat1_mult_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
    intros a b c.
    apply nat1_to_nat0_eq.
    do 4 rewrite <- nat1_to_nat0_mult.
    apply mult_assoc.
Qed.
Instance nat1_mult_assoc_class : MultAssoc nat1 := {
    mult_assoc := nat1_mult_assoc
}.

Lemma nat1_mult_lid : ∀ a, 1 * a = a.
    reflexivity.
Qed.
Instance nat1_mult_lid_class : MultLid nat1 := {
    mult_lid := nat1_mult_lid
}.

Lemma nat1_ldist : ∀ a b c, a * (b + c) = a * b + a * c.
    intros a b c.
    apply nat1_to_nat0_eq.
    rewrite <- nat1_to_nat0_plus.
    do 3 rewrite <- nat1_to_nat0_mult.
    rewrite <- nat1_to_nat0_plus.
    apply ldist.
Qed.
Instance nat1_ldist_class : Ldist nat1 := {
    ldist := nat1_ldist
}.

Theorem nat1_mult_lcancel : ∀ a b c, c * a = c * b → a = b.
    intros a b c eq.
    apply nat1_to_nat0_eq.
    apply (f_equal nat1_to_nat0) in eq.
    do 2 rewrite <- nat1_to_nat0_mult in eq.
    apply mult_lcancel in eq.
    -   exact eq.
    -   apply nat1_nz.
Qed.
