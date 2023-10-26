Require Import init.

Require Export complex_base.
Require Export complex_plus.
Require Import nat.
Require Import int.
Require Import rat.
Require Import real.

Require Import rat_abstract.

Global Instance complex_mult : Mult complex := {
    mult a b := (fst a * fst b - snd a * snd b, fst a * snd b + snd a * fst b)
}.

Global Program Instance complex_mult_comm : MultComm complex.
Next Obligation.
    unfold mult; cbn.
    do 2 rewrite (mult_comm (fst a)).
    do 2 rewrite (mult_comm (snd a)).
    rewrite (plus_comm (snd b * _)).
    reflexivity.
Qed.

Global Program Instance complex_mult_assoc : MultAssoc complex.
Next Obligation.
    unfold mult; cbn.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; cbn.
    apply prod_combine; cbn.
    -   do 2 rewrite ldist.
        do 2 rewrite rdist.
        rewrite mult_rneg, mult_lneg.
        do 2 rewrite neg_plus.
        repeat rewrite mult_assoc.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        do 2 rewrite plus_assoc.
        rewrite (plus_comm _ (-(a1 * _ * _))).
        do 2 rewrite <- plus_assoc.
        apply lplus.
        apply plus_comm.
    -   do 2 rewrite ldist.
        do 2 rewrite rdist.
        rewrite mult_rneg, mult_lneg.
        do 4 rewrite mult_assoc.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        do 2 rewrite plus_assoc.
        rewrite (plus_comm _ (a1 * _ * _)).
        do 2 rewrite <- plus_assoc.
        apply lplus.
        apply plus_comm.
Qed.

Global Program Instance complex_ldist : Ldist complex.
Next Obligation.
    unfold plus, mult; cbn.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; cbn.
    apply prod_combine; cbn.
    -   do 2 rewrite ldist.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        rewrite plus_comm.
        rewrite neg_plus.
        rewrite <- plus_assoc.
        apply lplus.
        apply plus_comm.
    -   do 2 rewrite ldist.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        rewrite plus_comm.
        rewrite <- plus_assoc.
        apply lplus.
        apply plus_comm.
Qed.

Global Instance complex_one : One complex := {
    one := (1, 0)
}.

Global Program Instance complex_not_trivial : NotTrivial complex := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Next Obligation.
    intros contr.
    assert (fst 0 = fst 1) as eq.
    {
        rewrite contr.
        reflexivity.
    }
    apply not_trivial_one in eq.
    exact eq.
Qed.

Global Program Instance complex_mult_lid : MultLid complex.
Next Obligation.
    unfold one, mult; cbn.
    do 2 rewrite mult_lid.
    do 2 rewrite mult_lanni.
    rewrite neg_zero.
    do 2 rewrite plus_rid.
    destruct a; reflexivity.
Qed.

Global Instance complex_div : Div complex := {
    div a := let d := fst a * fst a + snd a * snd a in (fst a / d, -snd a / d)
}.

Global Program Instance complex_mult_linv : MultLinv complex.
Next Obligation.
    unfold mult, div; cbn.
    destruct a as [a1 a2]; cbn.
    do 3 rewrite mult_lneg.
    rewrite neg_neg.
    do 2 rewrite (mult_comm (a1 / _)).
    do 2 rewrite (mult_comm (a2 / _)).
    do 4 rewrite mult_assoc.
    rewrite (mult_comm a1 a2).
    rewrite plus_rinv.
    rewrite <- rdist.
    rewrite mult_rinv.
    1: reflexivity.
    intros contr.
    apply H.
    unfold zero; cbn.
    assert (0 = a1) as eq1.
    {
        classic_contradiction neq.
        assert (0 < a1 * a1) as ltq.
        {
            split.
            -   apply square_pos.
            -   apply mult_nz; exact neq.
        }
        pose proof (square_pos a2) as leq.
        apply (le_lplus (a1 * a1)) in leq.
        rewrite plus_rid in leq.
        pose proof (lt_le_trans ltq leq) as [neq' leq']; contradiction.
    }
    subst a1.
    rewrite mult_lanni, plus_lid in contr.
    assert (0 = a2) as eq2.
    {
        classic_contradiction neq.
        assert (0 < a2 * a2) as ltq.
        {
            split.
            -   apply square_pos.
            -   apply mult_nz; exact neq.
        }
        destruct ltq; contradiction.
    }
    subst a2.
    reflexivity.
Qed.

Theorem real_to_complex_mult : ∀ a b,
    real_to_complex (a * b) = real_to_complex a * real_to_complex b.
Proof.
    intros a b.
    unfold real_to_complex, mult at 2; cbn.
    rewrite mult_lanni, mult_lanni, mult_ranni.
    rewrite neg_zero.
    do 2 rewrite plus_rid.
    reflexivity.
Qed.

Theorem rat_to_complex_mult : ∀ a b,
    rat_to_complex (a * b) = rat_to_complex a * rat_to_complex b.
Proof.
    intros a b.
    unfold rat_to_complex.
    setoid_rewrite homo_mult.
    apply real_to_complex_mult.
Qed.

Theorem int_to_complex_mult : ∀ a b,
    int_to_complex (a * b) = int_to_complex a * int_to_complex b.
Proof.
    intros a b.
    unfold int_to_complex.
    setoid_rewrite homo_mult.
    apply real_to_complex_mult.
Qed.

Theorem nat_to_complex_mult : ∀ a b,
    nat_to_complex (a * b) = nat_to_complex a * nat_to_complex b.
Proof.
    intros a b.
    unfold nat_to_complex.
    setoid_rewrite homo_mult.
    apply real_to_complex_mult.
Qed.
