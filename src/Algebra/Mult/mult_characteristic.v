Require Import init.

Require Export mult_ring.
Require Import nat_abstract.

(* TODO: Make this file more complete *)

Class Characteristic U n `{Plus U, Zero U, One U} := {
    characteristic : 0 = from_nat n
}.

Class CharacteristicNot U n `{Plus U, Zero U, One U} := {
    characteristic_not : 0 ≠ from_nat n
}.

Class CharacteristicZero U `{Plus U, Zero U, One U} := {
    characteristic_zero : ∀ n, 0 ≠ from_nat (nat_suc n)
}.

Section Characteristic.

Context {U} `{
    Field U,
    @CharacteristicNot U 2 UP UZ UE,
    @CharacteristicZero U UP UZ UE
}.

Theorem two_nz : 0 ≠ 2.
Proof.
    pose proof characteristic_not as neq.
    rewrite from_nat_plus in neq.
    rewrite from_nat_one in neq.
    exact neq.
Qed.

Local Program Instance characteristic_zero_not_trivial : NotTrivial U := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Next Obligation.
    rewrite <- from_nat_one.
    apply characteristic_zero.
Qed.

End Characteristic.
Section Characteristic.

Context {U} `{OrderedField U}.

Global Program Instance not_trivial_char : CharacteristicZero U.
Next Obligation.
    apply from_nat_pos.
Qed.

End Characteristic.
