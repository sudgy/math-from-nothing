Require Import init.
Require Import set.

Require Export category_base.

Class Functor `(C1 : Category) `(C2 : Category) := {
    functor_f : @cat_U C1 → @cat_U C2;
    functor_morphism : ∀ {A B},
        cat_morphism A B → cat_morphism (functor_f A) (functor_f B);
    functor_compose : ∀ {A B C} (f : cat_morphism B C) (g : cat_morphism A B),
        functor_morphism (f ∘ g) = functor_morphism f ∘ functor_morphism g;
    functor_id : ∀ A, functor_morphism (cat_id A) = cat_id (functor_f A);
}.

Program Instance id_functor `(C0 : Category) : Functor C0 C0 := {
    functor_f A := A;
    functor_morphism {A B} (f : cat_morphism A B) := f;
}.

Program Instance compose_functor `{C1 : Category, C2 : Category, C3 : Category}
    `(@Functor C1 C2) `(@Functor C2 C3) : Functor C1 C3 :=
{
    functor_f a := functor_f (functor_f a);
    functor_morphism {A B} (f : cat_morphism A B)
        := functor_morphism (functor_morphism f);
}.
Next Obligation.
    rewrite functor_compose.
    rewrite functor_compose.
    reflexivity.
Qed.
Next Obligation.
    rewrite functor_id.
    rewrite functor_id.
    reflexivity.
Qed.

Global Remove Hints id_functor compose_functor : typeclass_instances.

Definition faithful_functor `(F : Functor) := ∀ A B,
    injective (functor_morphism (A:=A) (B:=B)).
Definition full_functor `(F : Functor) := ∀ A B,
    surjective (functor_morphism (A:=A) (B:=B)).
