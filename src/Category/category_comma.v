Require Import init.

Require Export category_def.
Require Export set.

Set Universe Polymorphism.

Section CommaCategory.

Context {A B C : Category} (S : Functor A C) (T : Functor B C).

Record comma_obj := make_comma_obj {
    comma_A : A;
    comma_B : B;
    comma_f : morphism (S comma_A) (T comma_B);
}.

Definition comma_set (f g : comma_obj)
    (h : morphism (comma_A f) (comma_A g) * morphism (comma_B f) (comma_B g))
    := ⌈T⌉ (snd h) ∘ comma_f f = comma_f g ∘ (⌈S⌉ (fst h)).

Definition comma_compose {F G H : comma_obj}
    (f : set_type (comma_set G H)) (g : set_type (comma_set F G))
    := (fst [f|] ∘ fst [g|], snd [f|] ∘ snd [g|]).

Lemma comma_set_compose_in {F G H : comma_obj} :
    ∀ (f : set_type (comma_set G H)) g, comma_set F H (comma_compose f g).
Proof.
    intros [[f1 f2] f_eq] [[g1 g2] g_eq].
    unfold comma_set in *; cbn in *.
    do 2 rewrite functor_compose.
    rewrite <- cat_assoc.
    rewrite g_eq.
    do 2 rewrite cat_assoc.
    rewrite f_eq.
    reflexivity.
Qed.

Lemma comma_set_id_in : ∀ f : comma_obj, comma_set f f (𝟙, 𝟙).
Proof.
    intros f.
    unfold comma_set; cbn.
    do 2 rewrite functor_id.
    rewrite cat_lid, cat_rid.
    reflexivity.
Qed.

Program Definition Comma : Category := {|
    cat_U := comma_obj;
    morphism f g := set_type (comma_set f g);
    cat_compose F G H f g := [_|comma_set_compose_in f g];
    cat_id f := [_|comma_set_id_in f];
|}.
Next Obligation.
    rewrite set_type_eq2.
    unfold comma_compose; cbn.
    do 2 rewrite cat_assoc.
    reflexivity.
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    unfold comma_compose; cbn.
    do 2 rewrite cat_lid.
    destruct f as [[f1 f2] f_in]; reflexivity.
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    unfold comma_compose; cbn.
    do 2 rewrite cat_rid.
    destruct f as [[f1 f2] f_in]; reflexivity.
Qed.

End CommaCategory.

Check make_comma_obj.

Definition make_comma {A B C : Category} (S : Functor A C) (T : Functor B C)
    (a : A) (b : B) f := make_comma_obj S T a b f : Comma S T.

Unset Universe Polymorphism.
