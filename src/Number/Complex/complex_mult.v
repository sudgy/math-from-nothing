Require Import init.

Require Export complex_base.
Require Export complex_plus.
Require Import nat.
Require Import int.
Require Import rat.
Require Import fraction_mult.
Require Import real.

Global Instance complex_mult : Mult complex := {
    mult a b := (fst a * fst b - snd a * snd b, fst a * snd b + snd a * fst b)
}.

Global Instance complex_mult_comm : MultComm complex.
Proof.
    split.
    intros a b.
    unfold mult; cbn.
    do 2 rewrite (mult_comm (fst a)).
    do 2 rewrite (mult_comm (snd a)).
    rewrite (plus_comm (snd b * _)).
    reflexivity.
Qed.

Global Instance complex_mult_assoc : MultAssoc complex.
Proof.
    split.
    intros a b c.
    unfold mult; cbn.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; cbn.
    apply prod_combine; cbn.
    -   do 2 rewrite ldist.
        do 2 rewrite rdist.
        rewrite mult_rneg, mult_lneg.
        do 2 rewrite neg_plus.
        do 4 rewrite mult_assoc.
        rewrite (plus_comm (- _)).
        apply plus_4.
    -   do 2 rewrite ldist.
        do 2 rewrite rdist.
        rewrite mult_rneg, mult_lneg.
        do 4 rewrite mult_assoc.
        rewrite (plus_comm (a2 * _ * _)).
        apply plus_4.
Qed.

Global Instance complex_ldist : Ldist complex.
Proof.
    split.
    intros a b c.
    unfold plus, mult; cbn.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; cbn.
    apply prod_combine; cbn.
    -   do 2 rewrite ldist.
        rewrite neg_plus.
        apply plus_4.
    -   do 2 rewrite ldist.
        apply plus_4.
Qed.

Global Instance complex_one : One complex := {
    one := (1, 0)
}.

#[refine]
Global Instance complex_not_trivial : NotTrivial complex := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Proof.
    intros contr.
    apply (f_equal fst) in contr.
    apply not_trivial_one in contr.
    exact contr.
Qed.

Global Instance complex_mult_lid : MultLid complex.
Proof.
    split.
    intros a.
    unfold one, mult; cbn.
    do 2 rewrite mult_lid.
    do 2 rewrite mult_lanni.
    rewrite neg_zero.
    apply prod_combine; apply plus_rid.
Qed.

Global Instance complex_div : Div complex := {
    div a := let d := fst a * fst a + snd a * snd a in (fst a / d, -snd a / d)
}.

Global Instance complex_mult_linv : MultLinv complex.
Proof.
    split.
    intros a a_nz.
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
    assert (∀ x y : real, 0 = x * x + y * y → 0 = x) as wlog.
    {
        intros x y z_eq.
        apply square_nz.
        apply antisym; [>apply square_pos|].
        order_contradiction ltq.
        rewrite plus_0_ab_nb_a in z_eq.
        rewrite <- z_eq in ltq.
        apply neg_pos2 in ltq.
        contradiction (irrefl _ (lt_le_trans ltq (square_pos y))).
    }
    apply a_nz.
    apply prod_combine; cbn.
    -   apply (wlog _ _ contr).
    -   rewrite plus_comm in contr.
        apply (wlog _ _ contr).
Qed.

Global Instance real_to_complex_mult : HomomorphismMult real_to_complex.
Proof.
    split.
    intros a b.
    unfold real_to_complex, mult at 2; cbn.
    rewrite mult_lanni, mult_lanni, mult_ranni.
    rewrite neg_zero.
    do 2 rewrite plus_rid.
    reflexivity.
Qed.

Global Instance real_to_complex_one : HomomorphismOne real_to_complex.
Proof.
    split.
    reflexivity.
Qed.

Theorem from_nat_complex : ∀ n, real_to_complex (from_nat n) = from_nat n.
Proof.
    intros n.
    unfold real_to_complex.
    nat_induction n.
    -   do 2 rewrite (homo_zero (f := from_nat)).
        reflexivity.
    -   do 2 rewrite from_nat_suc.
        rewrite <- IHn.
        unfold plus at 2, one at 2; cbn.
        rewrite plus_lid.
        reflexivity.
Qed.

Global Instance complex_archimedean : CharacteristicZero complex.
Proof.
    split.
    intros n.
    rewrite <- from_nat_complex.
    rewrite <- (homo_zero (f := real_to_complex)).
    apply (inj_neq real_to_complex).
    apply characteristic_zero.
Qed.

Theorem from_int_complex : ∀ n, real_to_complex (from_int n) = from_int n.
Proof.
    intros n.
    pose proof (int_nat_ex n) as [a [b eq]]; subst n.
    do 2 rewrite (homo_plus (f := from_int)), (homo_neg (f := from_int)).
    do 4 rewrite from_int_nat.
    do 2 rewrite <- from_nat_complex.
    rewrite <- (homo_neg (f := real_to_complex)).
    rewrite <- (homo_plus (f := real_to_complex)).
    reflexivity.
Qed.

Theorem from_rat_complex : ∀ n, real_to_complex (from_rat n) = from_rat n.
Proof.
    intros n.
    equiv_get_value n.
    destruct n as [a b].
    rewrite (to_frac_div _ a b).
    change (to_frac int a) with (to_ofrac int a).
    change (to_frac int [b|]) with (to_ofrac int [b|]).
    do 2 rewrite <- from_int_rat.
    do 2 rewrite (homo_mult (f := from_rat)).
    assert (0 ≠ from_int (U := rat) [b|]) as b_nz.
    {
        apply (inj_zero from_int).
        exact [|b].
    }
    rewrite homo_div by exact b_nz.
    rewrite (homo_div (f := from_rat)) by exact b_nz.
    do 4 rewrite from_rat_int.
    do 2 rewrite <- from_int_complex.
    rewrite <- (homo_div (f := real_to_complex)).
    2: apply (inj_zero from_int); exact [|b].
    rewrite <- (homo_mult (f := real_to_complex)).
    reflexivity.
Qed.
