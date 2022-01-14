Require Import init.

Require Export mult_ring.
Require Import nat_abstract.

(* TODO: Make this file more complete *)

Class Characteristic U n `{Plus U, Zero U, One U} := {
    characteristic : 0 = nat_to_abstract n
}.

Class CharacteristicNot U n `{Plus U, Zero U, One U} := {
    characteristic_not : 0 ≠ nat_to_abstract n
}.

Class CharacteristicZero U `{Plus U, Zero U, One U} := {
    characteristic_zero : ∀ n, 0 ≠ nat_to_abstract (nat_suc n)
}.

Section Characteristic.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    UO : One U,
    @CharacteristicNot U 2 UP UZ UO
}.

Theorem two_nz : 0 ≠ 2.
    pose proof characteristic_not as neq.
    unfold one in neq; cbn in neq.
    unfold plus in neq; cbn in neq.
    rewrite plus_rid in neq.
    exact neq.
Qed.

End Characteristic.
