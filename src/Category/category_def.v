Require Import init.

(* begin show *)
Set Universe Polymorphism.
(* end show *)

(** Note: I am learning category theory while writing this.  Apologies if
anything here is incorrect/not specified in the best way.
*)

Record CategoryObj := make_category {
    cat_U :> Type;
    morphism : cat_U → cat_U → Type;
    cat_compose : ∀ {A B C},
        morphism B C → morphism A B → morphism A C;
    cat_id : ∀ A, morphism A A;
    cat_assoc : ∀ {A B C D}
        (h : morphism C D) (g : morphism B C) (f : morphism A B),
        cat_compose h (cat_compose g f) = cat_compose (cat_compose h g) f;
    cat_lid : ∀ {A B} (f : morphism A B), cat_compose (cat_id B) f = f;
    cat_rid : ∀ {A B} (f : morphism A B), cat_compose f (cat_id A) = f;
}.

Arguments cat_compose {c A B C} f g.
Arguments morphism {c}.
Arguments cat_id {c}.
Arguments cat_assoc {c A B C D}.
Arguments cat_lid {c A B}.
Arguments cat_rid {c A B}.

Infix "∘" := cat_compose.
Notation "𝟙" := (cat_id _).

Definition cat_domain {C : CategoryObj} {A B : C} (f : morphism A B) := A.
Definition cat_codomain {C : CategoryObj} {A B : C} (f : morphism A B) := B.

Record FunctorObj (C1 C2 : CategoryObj) := make_functor {
    functor_f :> C1 → C2;
    functor_morphism : ∀ {A B},
        morphism A B → morphism (functor_f A) (functor_f B);
    functor_compose : ∀ {A B C} (f : morphism B C) (g : morphism A B),
        functor_morphism (f ∘ g) = functor_morphism f ∘ functor_morphism g;
    functor_id : ∀ A, functor_morphism (cat_id A) = 𝟙;
}.

Arguments functor_f {C1 C2} f0 A.
Arguments functor_morphism {C1 C2} f0 {A B} f.
Arguments functor_id {C1 C2}.

Notation "⌈ F ⌉" := (functor_morphism F) (at level 40).

Program Definition id_functor (C : CategoryObj) : FunctorObj C C := {|
    functor_f A := A;
    functor_morphism A B f := f;
|}.

Program Definition compose_functor {C1 C2 C3 : CategoryObj}
    (F : FunctorObj C2 C3) (G : FunctorObj C1 C2) : FunctorObj C1 C3 :=
{|
    functor_f a := F (G a);
    functor_morphism A B (f : morphism A B) := ⌈F⌉ (⌈G⌉ f);
|}.
Next Obligation.
Proof.
    rewrite functor_compose.
    rewrite functor_compose.
    reflexivity.
Qed.
Next Obligation.
Proof.
    rewrite functor_id.
    rewrite functor_id.
    reflexivity.
Qed.

Definition functor_morphism_convert_type {C1 C2 : CategoryObj}
        {F G : FunctorObj C1 C2} {A B} (H : ∀ A, F A = G A)
        (f : morphism (F A) (F B)) : morphism (G A) (G B).
Proof.
    rewrite (H A) in f.
    rewrite (H B) in f.
    exact f.
Defined.

Theorem functor_eq {C1 C2 : CategoryObj} : ∀ {F G : FunctorObj C1 C2},
        ∀ (H : ∀ A, F A = G A),
        (∀ {A B} (f : morphism A B),
            functor_morphism_convert_type H (⌈F⌉ f) = ⌈G⌉ f) →
        F = G.
Proof.
    intros [f1 morphism1 compose1 id1] [f2 morphism2 compose2 id2] H eq'.
    cbn in *.
    assert (f1 = f2) as eq.
    {
        apply functional_ext.
        exact H.
    }
    subst f2.
    assert (morphism1 = morphism2) as eq.
    {
        apply functional_ext; intros A.
        apply functional_ext; intros B.
        apply functional_ext; intros f.
        rewrite <- eq'.
        unfold functor_morphism_convert_type.
        pose (HA := Logic.eq_refl (f1 A)).
        pose (HB := Logic.eq_refl (f1 B)).
        rewrite (proof_irrelevance (H A) HA).
        rewrite (proof_irrelevance (H B) HB).
        cbn.
        reflexivity.
    }
    subst morphism2; clear H eq'.
    rewrite (proof_irrelevance compose2 compose1).
    rewrite (proof_irrelevance id2 id1).
    reflexivity.
Qed.

Program Definition Category : CategoryObj := {|
    cat_U := CategoryObj;
    morphism A B := FunctorObj A B;
    cat_compose A B C f g := compose_functor f g;
    cat_id A := id_functor A;
|}.
Next Obligation.
Proof.
    eapply functor_eq.
    Unshelve.
    2: reflexivity.
    intros X Y F.
    cbn.
    reflexivity.
Qed.
Next Obligation.
Proof.
    eapply functor_eq.
    Unshelve.
    2: reflexivity.
    intros X Y F.
    cbn.
    reflexivity.
Qed.
Next Obligation.
Proof.
    eapply functor_eq.
    Unshelve.
    2: reflexivity.
    intros X Y F.
    cbn.
    reflexivity.
Qed.

Record NatTransformationObj {C1 C2 : Category} (F G : morphism C1 C2) :=
{
    nat_trans_f :> ∀ A,
        morphism (F A) (G A);
    nat_trans_commute : ∀ {A B} (f : morphism A B),
        nat_trans_f B ∘ (⌈F⌉ f) = (⌈G⌉ f) ∘ nat_trans_f A;
}.

Arguments nat_trans_f {C1 C2 F G} n.
Arguments nat_trans_commute {C1 C2 F G} n {A B}.

Program Definition id_nat_transformation {C1 : Category} {C2 : Category}
    (F : morphism C1 C2) : NatTransformationObj F F :=
{|
    nat_trans_f A := 𝟙
|}.
Next Obligation.
    rewrite cat_lid.
    rewrite cat_rid.
    reflexivity.
Qed.

(* begin show *)
Program Definition vcompose_nat_transformation {C1 C2 : Category}
    {F G H : morphism C1 C2}
    (α : NatTransformationObj G H) (β : NatTransformationObj F G)
    : NatTransformationObj F H :=
{|
    nat_trans_f A := α A ∘ β A
|}.
(* end show *)
Next Obligation.
    rewrite cat_assoc.
    rewrite <- cat_assoc.
    rewrite nat_trans_commute.
    rewrite cat_assoc.
    rewrite nat_trans_commute.
    reflexivity.
Qed.

Theorem nat_trans_eq {C1 C2 : Category} {F G : morphism C1 C2} :
    ∀ (α β : NatTransformationObj F G), (∀ A, α A = β A) → α = β.
Proof.
    intros [f1 commute1] [f2 commute2] H.
    cbn in *.
    assert (f1 = f2) as eq.
    {
        apply functional_ext.
        exact H.
    }
    subst f2; clear H.
    rewrite (proof_irrelevance commute2 commute1).
    reflexivity.
Qed.

Program Definition Functor (C1 C2 : Category) : Category := {|
    cat_U := morphism C1 C2;
    morphism F G := NatTransformationObj F G;
    cat_compose A B C α β := vcompose_nat_transformation α β;
    cat_id F := id_nat_transformation F;
|}.
Next Obligation.
    apply nat_trans_eq.
    intros X.
    cbn.
    apply cat_assoc.
Qed.
Next Obligation.
    apply nat_trans_eq.
    intros X.
    cbn.
    apply cat_lid.
Qed.
Next Obligation.
    apply nat_trans_eq.
    intros X.
    cbn.
    apply cat_rid.
Qed.

Notation "'NatTransformation'" := (morphism (c := Functor _ _)).
Notation "𝟏" := (𝟙 : Functor _ _).
Notation "'𝕀'" := (𝟙 : NatTransformation _ _).

Unset Universe Polymorphism.
