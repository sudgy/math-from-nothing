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
    Field U,
    @CharacteristicNot U 2 UP UZ UE,
    @CharacteristicZero U UP UZ UE
}.

Theorem two_nz : 0 ≠ 2.
Proof.
    pose proof characteristic_not as neq.
    unfold one in neq; cbn in neq.
    unfold plus in neq; cbn in neq.
    rewrite plus_rid in neq.
    exact neq.
Qed.

Theorem nat_to_abstract_eq : ∀ a b,
    nat_to_abstract a = nat_to_abstract b → a = b.
Proof.
    nat_induction a.
    -   intros b eq.
        nat_destruct b.
        +   reflexivity.
        +   rewrite nat_to_abstract_zero in eq.
            apply characteristic_zero in eq.
            contradiction.
    -   intros b eq.
        nat_destruct b.
        +   rewrite nat_to_abstract_zero in eq.
            symmetry in eq.
            apply characteristic_zero in eq.
            contradiction.
        +   apply f_equal.
            apply IHa.
            cbn in eq.
            apply plus_lcancel in eq.
            exact eq.
Qed.

Local Program Instance characteristic_zero_not_trivial : NotTrivial U := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Next Obligation.
    rewrite <- nat_to_abstract_one.
    apply characteristic_zero.
Qed.

End Characteristic.
Section Characteristic.

Context {U} `{OrderedField U}.

Global Program Instance not_trivial_char : CharacteristicZero U.
Next Obligation.
    assert (0 < 1 + nat_to_abstract n) as ltq.
    {
        nat_induction n.
        -   rewrite nat_to_abstract_zero.
            rewrite plus_rid.
            apply one_pos.
        -   cbn.
            rewrite (plus_comm _ (_ n)).
            rewrite plus_assoc.
            rewrite <- (plus_rid 0).
            apply lt_lrplus.
            +   exact IHn.
            +   apply one_pos.
    }
    apply ltq.
Qed.

End Characteristic.
