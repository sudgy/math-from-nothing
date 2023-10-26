Require Import init.

Require Export category_def.
Require Export basic_categories.
Require Import category_initterm.
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

Definition make_comma {A B C : Category} (S : Functor A C) (T : Functor B C)
    (a : A) (b : B) f := make_comma_obj S T a b f : Comma S T.
Definition make_comma_l1 {B C : Category} (a : C) (T : Functor B C) (b : B)
    (f : morphism a (T b)) := make_comma (obj_to_functor a) T Single b f.
Definition make_comma_l2 {A C : Category} (S : Functor A C) (a : C) (b : A)
    (f : morphism (S b) a) := make_comma S (obj_to_functor a) b Single f.
Definition make_slice {C : Category} (a : C) (b : C) (f : morphism b a)
    := make_comma 𝟙 (obj_to_functor a) b Single f.
Definition make_coslice {C : Category} (a : C) (b : C) (f : morphism a b)
    := make_comma (obj_to_functor a) 𝟙 Single b f.

Section FreeFunctor.

Context {B C : Category} {T : Functor B C}
    {f : C → B} {g : ∀ a : C, morphism a (T (f a))}.

Hypothesis i : ∀ a : C, initial (make_comma_l1 a T (f a) (g a)).

Definition extend {a : C} {b : B} (h : morphism a (T b))
    := snd [ex_singleton (i a (make_comma_l1 a T b h))|] : morphism (f a) b.

Theorem extend_eq : ∀ {a : C} {b : B} (h : morphism a (T b)),
    ⌈T⌉ (extend h) ∘ g a = h.
Proof.
    intros a b h.
    unfold extend.
    destruct (ex_singleton _) as [[s h'] h'_in]; cbn in *.
    unfold comma_set in h'_in; cbn in h'_in.
    clear s.
    rewrite cat_rid in h'_in.
    exact h'_in.
Qed.

Theorem extend_uni : ∀ {a : C} {b : B} (h : morphism a (T b)),
    ∀ h' : morphism (f a) b, ⌈T⌉ h' ∘ g a = h → extend h = h'.
Proof.
    intros a b h h' h'_eq.
    unfold extend.
    pose (S := i a (make_comma_l1 a T b h)).
    pose proof (singleton_unique2 (ex_singleton S)) as uni.
    cbn in uni.
    unfold comma_set in uni; cbn in uni.
    rewrite <- (cat_rid h) in h'_eq.
    specialize (uni [(Single, _) | h'_eq]).
    rewrite uni.
    reflexivity.
Qed.

Program Definition free_functor : Functor C B := {|
    functor_f := f;
    functor_morphism a b h := extend ((g b) ∘ h);
|}.
Next Obligation.
    rename A into a, B0 into b, C0 into c.
    rename f0 into h1, g0 into h2.
    apply extend_uni.
    rewrite functor_compose.
    rewrite <- cat_assoc.
    rewrite extend_eq.
    rewrite cat_assoc.
    rewrite extend_eq.
    symmetry; apply cat_assoc.
Qed.
Next Obligation.
    rename A into a.
    apply extend_uni.
    rewrite functor_id.
    rewrite cat_rid.
    apply cat_lid.
Qed.

Local Notation "'F'" := free_functor.

Theorem free_commute : ∀ {a b : C} (h : morphism a b),
    (⌈T ∘ F⌉ h) ∘ g a = g b ∘ h.
Proof.
    intros a b h.
    cbn.
    apply extend_eq.
Qed.

Arguments extend : simpl never.
Arguments free_functor : simpl never.

End FreeFunctor.

Unset Universe Polymorphism.
