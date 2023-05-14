Require Import init.
Require Import set.

Require Export category_base.

Theorem functor_isomorphism {C1 C2 : Category} {F : Functor C1 C2} :
    ∀ {A B}, A ≅ B → (F A) ≅ (F B).
Proof.
    intros A B [f g [fg gf]].
    exists (⌈F⌉ f) (⌈F⌉ g).
    unfold is_isomorphism_pair.
    do 2 rewrite <- functor_compose.
    rewrite fg, gf.
    split; apply functor_id.
Qed.

Definition faithful_functor {C1 C2 : Category} (F : Functor C1 C2) := ∀ A B,
    Injective (functor_morphism F (A:=A) (B:=B)).
Definition full_functor {C1 C2 : Category} (F : Functor C1 C2) := ∀ A B,
    Surjective (functor_morphism F (A:=A) (B:=B)).
Definition essentially_surjective {C1 : Category} {C2 : Category}
    (F : Functor C1 C2) := ∀ B, ∃ A, inhabited ((F A) ≅ B).

Theorem id_functor_faithful : ∀ C, faithful_functor (cat_id C).
Proof.
    intros C A B.
    apply identity_bijective.
Qed.
Theorem id_functor_full : ∀ C, full_functor (cat_id C).
Proof.
    intros C A B.
    apply identity_bijective.
Qed.

Program Definition inclusion_functor {C : Category} (S : SubCategory C)
    : Functor (subcategory S) C :=
{|
    functor_f x := [x|];
    functor_morphism A B (f : morphism A B) := [f|];
|}.

Theorem inclusion_functor_faithful : ∀ {C : Category} (S : SubCategory C),
    faithful_functor (inclusion_functor S).
Proof.
    intros C S A B.
    cbn.
    apply set_type_inj.
Qed.

Theorem inclusion_functor_full : ∀ {C : Category} (S : SubCategory C),
    full_subcategory S → full_functor (inclusion_functor S).
Proof.
    intros H S S_full A B.
    split.
    intros f.
    cbn in *.
    unfold full_subcategory in S_full.
    specialize (S_full [A|] [B|]).
    rewrite S_full.
    exists [f|true].
    reflexivity.
Qed.
