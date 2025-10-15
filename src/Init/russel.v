Require Import init.

Unset Universe Checking.

Inductive set : Type :=
    | make_set : ∀ X : Type, (X → set) → set.

Definition set_type (A : set) : Type
    := match A with | make_set U _ => U end.
Definition set_f (A : set) : set_type A → set
    := match A with | make_set _ f => f end.

Definition set_in (A B : set) := ∃ x, set_f B x = A.

Infix "∈" := set_in (at level 70).

Definition russel := make_set (ex_type (λ S, ¬(S ∈ S))) ex_type_val.

Lemma russel_not_in : ¬(russel ∈ russel).
Proof.
    intros contr.
    pose proof contr as [[S S_nin] eq].
    cbn in eq.
    subst S.
    contradiction.
Qed.

Lemma russel_in : russel ∈ russel.
Proof.
    unfold set_in.
    exists (ex_type_constr _ russel russel_not_in).
    cbn.
    reflexivity.
Qed.

Theorem russels_paradox : False.
Proof.
    exact (russel_not_in russel_in).
Qed.
