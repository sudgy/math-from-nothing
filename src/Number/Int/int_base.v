Require Import init.

Require Import nat.
Require Import set.

Declare Scope int_scope.
Delimit Scope int_scope with int.

Section IntEquiv.

Let int_eq (a b : nat * nat) := fst a + snd b = fst b + snd a.
Local Infix "~" := int_eq.

Instance int_eq_reflexive_class : Reflexive int_eq.
Proof.
    split.
    intros [a1 a2].
    unfold int_eq; cbn.
    reflexivity.
Qed.

Instance int_eq_symmetric_class : Symmetric int_eq.
Proof.
    split.
    intros [a1 a2] [b1 b2] ab.
    unfold int_eq in *; cbn in *.
    symmetry.
    exact ab.
Qed.

Instance int_eq_transitive_class : Transitive int_eq.
Proof.
    split.
    intros [a1 a2] [b1 b2] [c1 c2] ab bc.
    unfold int_eq in *; cbn in *.
    pose proof (lrplus ab bc) as eq; clear ab bc.
    rewrite plus_4 in eq.
    rewrite (plus_comm a1 b1) in eq.
    rewrite (plus_comm b2) in eq.
    do 2 rewrite <- plus_assoc in eq.
    apply plus_lcancel in eq.
    do 2 rewrite plus_assoc in eq.
    apply plus_rcancel in eq.
    rewrite eq.
    apply plus_comm.
Qed.

End IntEquiv.

Definition int_equiv := make_equiv _
    int_eq_reflexive_class int_eq_symmetric_class int_eq_transitive_class.
Notation "a ~ b" := (eq_equal int_equiv a b) : int_scope.

Notation "'int'" := (equiv_type int_equiv).
