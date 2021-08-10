Require Import init.

Require Import nat.
Require Import set.

Declare Scope int_scope.
Delimit Scope int_scope with int.

(* begin hide *)
Section IntEquiv.
(* end hide *)
Let int_eq (a b : nat * nat) := fst a + snd b = fst b + snd a.
(* begin hide *)
Local Infix "~" := int_eq.

Lemma int_eq_reflexive : ∀ a, a ~ a.
    intros [a1 a2].
    unfold int_eq; cbn.
    reflexivity.
Qed.
Instance int_eq_reflexive_class : Reflexive _ := {
    refl := int_eq_reflexive
}.

Lemma int_eq_symmetric : ∀ a b, a ~ b → b ~ a.
    intros [a1 a2] [b1 b2] ab.
    unfold int_eq in *; cbn in *.
    symmetry.
    exact ab.
Qed.
Instance int_eq_symmetric_class : Symmetric _ := {
    sym := int_eq_symmetric
}.

Lemma int_eq_transitive : ∀ a b c, a ~ b → b ~ c → a ~ c.
    intros [a1 a2] [b1 b2] [c1 c2] ab bc.
    unfold int_eq in *; cbn in *.
    pose proof (lrplus ab bc) as eq; clear ab bc.
    plus_cancel_left b1 in eq.
    plus_cancel_left b2 in eq.
    rewrite eq.
    apply plus_comm.
Qed.
Instance int_eq_transitive_class : Transitive _ := {
    trans := int_eq_transitive
}.

End IntEquiv.
(* end hide *)

Definition int_equiv := make_equiv _
    int_eq_reflexive_class int_eq_symmetric_class int_eq_transitive_class.
Notation "a ~ b" := (eq_equal int_equiv a b) : int_scope.

Notation "'int'" := (equiv_type int_equiv).

Definition nat_to_int a := to_equiv_type int_equiv (a, zero).

Theorem nat_to_int_eq : ∀ a b, nat_to_int a = nat_to_int b → a = b.
    intros a b eq.
    unfold nat_to_int in eq.
    rewrite equiv_eq in eq; cbn in eq.
    do 2 rewrite plus_rid in eq.
    exact eq.
Qed.
