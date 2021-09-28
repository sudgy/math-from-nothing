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

Program Instance inclusion_functor `{C : Category} `(S : @SubCategory C)
    : Functor (subcategory S) C :=
{
    functor_f x := [x|];
    functor_morphism {A B} (f : cat_morphism A B) := [f|];
}.

Global Remove Hints id_functor compose_functor inclusion_functor : typeclass_instances.

Definition faithful_functor `(F : Functor) := ∀ A B,
    injective (functor_morphism (A:=A) (B:=B)).
Definition full_functor `(F : Functor) := ∀ A B,
    surjective (functor_morphism (A:=A) (B:=B)).

Theorem id_functor_faithful : ∀ C, faithful_functor (id_functor C).
    intros C0 A B f g eq.
    cbn in eq.
    exact eq.
Qed.
Theorem id_functor_full : ∀ C, full_functor (id_functor C).
    intros C0 A B f.
    cbn in f.
    exists f.
    cbn.
    reflexivity.
Qed.

Theorem inclusion_functor_faithful : ∀ `(S : SubCategory),
        faithful_functor (inclusion_functor S).
    intros C0 S A B f g eq.
    cbn in eq.
    apply set_type_eq in eq.
    exact eq.
Qed.
Theorem inclusion_functor_full : ∀ `(S : SubCategory), full_subcategory S →
        full_functor (inclusion_functor S).
    intros H S S_full A B f.
    cbn in *.
    unfold full_subcategory in S_full.
    specialize (S_full [A|] [B|]).
    rewrite S_full.
    exists [f|true].
    reflexivity.
Qed.

Section Functor.

Context `{C1 : Category, C2 : Category, F : @Functor C1 C2}.

Theorem functor_isomorphism : ∀ A B,
        isomorphic A B → isomorphic (functor_f A) (functor_f B).
    intros A B [f [g [fg gf]]].
    exists (functor_morphism f).
    exists (functor_morphism g).
    rewrite <- functor_compose.
    rewrite <- functor_compose.
    rewrite fg, gf.
    split; apply functor_id.
Qed.

End Functor.
