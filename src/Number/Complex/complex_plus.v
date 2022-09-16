Require Import init.

Require Export complex_base.
Require Import nat.
Require Import rat.
Require Import real.

Require Import int_abstract.
Require Import rat_abstract.

Global Instance complex_plus : Plus complex := {
    plus a b := (fst a + fst b, snd a + snd b)
}.

Global Program Instance complex_plus_comm : PlusComm complex.
Next Obligation.
    unfold plus; cbn.
    rewrite plus_comm.
    rewrite (plus_comm (snd a)).
    reflexivity.
Qed.

Global Program Instance complex_plus_assoc : PlusAssoc complex.
Next Obligation.
    unfold plus; cbn.
    do 2 rewrite plus_assoc.
    reflexivity.
Qed.

Global Instance complex_zero : Zero complex := {
    zero := (0, 0)
}.

Global Program Instance complex_plus_lid : PlusLid complex.
Next Obligation.
    unfold zero, plus; cbn.
    do 2 rewrite plus_lid.
    destruct a; reflexivity.
Qed.

Global Instance complex_neg : Neg complex := {
    neg a := (-fst a, -snd a)
}.

Global Program Instance complex_plus_linv : PlusLinv complex.
Next Obligation.
    unfold plus, neg; cbn.
    do 2 rewrite plus_linv.
    reflexivity.
Qed.

Theorem real_to_complex_plus : ∀ a b,
    real_to_complex (a + b) = real_to_complex a + real_to_complex b.
Proof.
    intros a b.
    unfold real_to_complex, plus at 2; cbn.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem rat_to_complex_plus : ∀ a b,
    rat_to_complex (a + b) = rat_to_complex a + rat_to_complex b.
Proof.
    intros a b.
    unfold rat_to_complex.
    rewrite rat_to_abstract_plus.
    apply real_to_complex_plus.
Qed.

Theorem int_to_complex_plus : ∀ a b,
    int_to_complex (a + b) = int_to_complex a + int_to_complex b.
Proof.
    intros a b.
    unfold int_to_complex.
    rewrite int_to_abstract_plus.
    apply real_to_complex_plus.
Qed.

Theorem nat_to_complex_plus : ∀ a b,
    nat_to_complex (a + b) = nat_to_complex a + nat_to_complex b.
Proof.
    intros a b.
    unfold nat_to_complex.
    rewrite from_nat_plus.
    apply real_to_complex_plus.
Qed.
