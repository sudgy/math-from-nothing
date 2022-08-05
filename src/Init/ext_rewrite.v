(** This file shows my attempt at allowing for rewriting in binders.  It
sometimes works, but I'm not good enough at this to figure out how to make it
work more often.  I've noticed that this often is pretty slow so I'm starting to
wonder if it was a good idea in the first place.
*)

Require Import base_logic.
From Coq Require Import Morphisms.
From Coq Require Export Setoid.

Global Instance ext_rewrite1 T :
        Proper (pointwise_relation T equal ==> equal) (all (A := T)).
    intros x y Heq.
    assert (x = y) as eq.
    {
        apply predicate_ext.
        unfold pointwise_relation in Heq.
        intros a.
        rewrite Heq.
        reflexivity.
    }
    rewrite eq.
    reflexivity.
Qed.

Global Instance ext_rewrite2 : subrelation iff equal.
    intros A B Hequiv.
    apply propositional_ext.
    exact Hequiv.
Qed.

Global Instance ext_rewrite3 U :
        Proper (pointwise_relation U equal ==> Basics.impl) (all (A := U)).
    intros P Q H all_P x.
    rewrite <- H.
    apply all_P.
Qed.

Fact ext_rewrite_test1 {T : Type} {A B : T → Prop} :
        (∀ x: T, A x ↔ B x) → (∀ x: T, A x) = ∀ x: T, B x.
    intros Heq.
    setoid_rewrite Heq.
Abort.

Fact ext_rewrite_test2 {T U : Type} {A B : T → U} (C : U → Prop) :
        (∀ x: T, A x = B x) → (∀ x: T, C (A x)) = ∀ x: T, C (B x).
    intros H.
    setoid_rewrite H.
Abort.

Fact ext_rewrite_test3 {T U : Type} {A B : T → Prop}
        (C : Prop → Prop) `{!Proper (iff ==> iff) C} :
        (∀ x: T, A x ↔ B x) → (∀ x: T, C (A x)) = ∀ x: T, C (B x).
    intros H.
    setoid_rewrite H.
Abort.

Fact ext_rewrite_test4 {T U : Type} {A B : T → Prop} (C : Prop → Prop) :
        (∀ x: T, A x ↔ B x) → (∀ x: T, C (A x)) = ∀ x: T, C (B x).
    intros Heqv.
    assert (∀ x: T, A x = B x) as Heq.
    setoid_rewrite Heqv.
    reflexivity.
    setoid_rewrite Heq.
Abort.

Fact ext_rewrite_test5 {U : Type} {P : U → Prop} :
        (∀ P : Prop, (¬¬P) = P) → (∀ x, ¬¬(P x)) → ∀ x, P x.
    intros not_not eq.
    setoid_rewrite not_not in eq.
Abort.

