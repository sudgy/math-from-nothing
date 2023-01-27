Require Import init.

Require Import nat.
Require Import rat.
Require Import real.

Require Import int_abstract.
Require Import rat_abstract.

Declare Scope complex_scope.
Delimit Scope complex_scope with complex.

Definition complex := (real * real)%type.

Definition real_to_complex a := (a, 0) : complex.
Definition rat_to_complex a := real_to_complex (rat_to_abstract a).
Definition int_to_complex a := real_to_complex (int_to_abstract a).
Definition nat_to_complex a := real_to_complex (from_nat a).

Theorem real_to_complex_eq : ∀ a b,
    real_to_complex a = real_to_complex b → a = b.
Proof.
    intros a b eq.
    inversion eq.
    reflexivity.
Qed.

Theorem rat_to_complex_eq : ∀ a b, rat_to_complex a = rat_to_complex b → a = b.
Proof.
    intros a b eq.
    apply rat_to_abstract_eq.
    apply real_to_complex_eq.
    exact eq.
Qed.

Theorem int_to_complex_eq : ∀ a b, int_to_complex a = int_to_complex b → a = b.
Proof.
    intros a b eq.
    apply int_to_abstract_eq.
    apply real_to_complex_eq.
    exact eq.
Qed.

Theorem nat_to_complex_eq : ∀ a b, nat_to_complex a = nat_to_complex b → a = b.
Proof.
    intros a b eq.
    apply homo_inj.
    apply real_to_complex_eq.
    exact eq.
Qed.
