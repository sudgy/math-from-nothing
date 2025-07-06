Require Import init.

Require Export complex_base.
Require Import real.

Global Instance complex_plus : Plus complex := {
    plus a b := (fst a + fst b, snd a + snd b)
}.

Global Instance complex_plus_comm : PlusComm complex.
Proof.
    split.
    intros a b.
    unfold plus; cbn.
    apply prod_combine; apply plus_comm.
Qed.

Global Instance complex_plus_assoc : PlusAssoc complex.
Proof.
    split.
    intros a b c.
    unfold plus; cbn.
    apply prod_combine; apply plus_assoc.
Qed.

Global Instance complex_zero : Zero complex := {
    zero := (0, 0)
}.

Global Instance complex_plus_lid : PlusLid complex.
Proof.
    split.
    intros a.
    unfold zero, plus; cbn.
    apply prod_combine; apply plus_lid.
Qed.

Global Instance complex_neg : Neg complex := {
    neg a := (-fst a, -snd a)
}.

Global Instance complex_plus_linv : PlusLinv complex.
Proof.
    split.
    intros a.
    unfold plus, neg; cbn.
    apply prod_combine; apply plus_linv.
Qed.

Global Instance real_to_complex_plus : HomomorphismPlus real_to_complex.
Proof.
    split.
    intros a b.
    unfold real_to_complex, plus at 2; cbn.
    rewrite plus_lid.
    reflexivity.
Qed.
