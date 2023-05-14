Require Import init.
Require Import set.

Require Export category_base.

Program Definition inclusion_functor {C : Category} (S : SubCategory C)
    : Functor (subcategory S) C :=
{|
    functor_f x := [x|];
    functor_morphism A B (f : morphism A B) := [f|];
|}.

Definition faithful_functor {C1 C2 : Category} (F : Functor C1 C2) := ∀ A B,
    Injective (functor_morphism F (A:=A) (B:=B)).
Definition full_functor {C1 C2 : Category} (F : Functor C1 C2) := ∀ A B,
    Surjective (functor_morphism F (A:=A) (B:=B)).

Theorem id_functor_faithful : ∀ C, faithful_functor (cat_id C).
Proof.
    intros C A B.
    split.
    intros f g eq.
    cbn in eq.
    exact eq.
Qed.
Theorem id_functor_full : ∀ C, full_functor (cat_id C).
Proof.
    intros C0 A B.
    split.
    intros f.
    cbn in f.
    exists f.
    cbn.
    reflexivity.
Qed.

Theorem inclusion_functor_faithful : ∀ {C : Category} (S : SubCategory C),
    faithful_functor (inclusion_functor S).
Proof.
    intros C0 S A B.
    split.
    intros f g eq.
    cbn in eq.
    apply set_type_eq in eq.
    exact eq.
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

Definition essentially_surjective {C1 : Category} {C2 : Category}
    (F : Functor C1 C2)
    := ∀ B, ∃ A, inhabited ((F A) ≅ B).

(* begin hide *)
Section Functor.

Context {C1 : Category} {C2 : Category} {F : Functor C1 C2}.

(* end hide *)
Theorem functor_isomorphism : ∀ A B, A ≅ B → (F A) ≅ (F B).
Proof.
    intros A B [f g [fg gf]].
    exists (⌈F⌉ f) (⌈F⌉ g).
    unfold is_isomorphism_pair.
    rewrite <- functor_compose.
    rewrite <- functor_compose.
    rewrite fg, gf.
    split; apply functor_id.
Qed.

(* begin hide *)
End Functor.

(* end hide *)
