Require Import init.

(** Note: I am learning category theory while writing this.  Apologies if
anything here is incorrect/not specified in the best way.
*)

Class Category := {
    cat_U : Type;
    cat_morphism : cat_U → cat_U → Type;
    cat_compose : ∀ {A B C},
        cat_morphism B C → cat_morphism A B → cat_morphism A C;
    cat_id : ∀ A, cat_morphism A A;
    cat_assoc : ∀ {A B C D}
        (f : cat_morphism A B) (g : cat_morphism B C) (h : cat_morphism C D),
        cat_compose h (cat_compose g f) = cat_compose (cat_compose h g) f;
    cat_lid : ∀ {A B} (f : cat_morphism A B), cat_compose (cat_id B) f = f;
    cat_rid : ∀ {A B} (f : cat_morphism A B), cat_compose f (cat_id A) = f;
}.

Infix "∘" := cat_compose.

Definition cat_domain `{Category} {A B} (f : cat_morphism A B) := A.
Definition cat_codomain `{Category} {A B} (f : cat_morphism A B) := B.

Definition isomorphism `{Category} {A B} (f : cat_morphism A B)
    := ∃ g, f ∘ g = cat_id B ∧ g ∘ f = cat_id A.

Definition cat_inverse `{Category} {A B}
    (f : cat_morphism A B) (H : isomorphism f) := ex_val H.

Definition isomorphic `{Category} A B
    := ∃ f : cat_morphism A B, isomorphism f.

Program Instance dual_category `(Category) : Category := {
    cat_U := cat_U;
    cat_morphism A B := cat_morphism B A;
    cat_compose {A B C} f g := cat_compose g f;
    cat_id A := cat_id A;
}.
Next Obligation.
    symmetry.
    apply cat_assoc.
Qed.
Next Obligation.
    apply cat_rid.
Qed.
Next Obligation.
    apply cat_lid.
Qed.

Program Instance product_category `(C1 : Category) `(C2 : Category) : Category
:= {
    cat_U := prod (@cat_U C1) (@cat_U C2);
    cat_morphism A B
        := prod (cat_morphism (fst A) (fst B)) (cat_morphism (snd A) (snd B));
    cat_compose {A B C} f g
        := (cat_compose (fst f) (fst g), cat_compose (snd f) (snd g));
    cat_id A := (cat_id (fst A), cat_id (snd A));
}.
Next Obligation.
    do 2 rewrite cat_assoc.
    reflexivity.
Qed.
Next Obligation.
    do 2 rewrite cat_lid.
    destruct f; reflexivity.
Qed.
Next Obligation.
    do 2 rewrite cat_rid.
    destruct f; reflexivity.
Qed.

Global Remove Hints dual_category product_category : typeclass_instances.

Section Category.

Context `{Category}.

Theorem lcompose : ∀ {A B C} {f g : cat_morphism A B} (h : cat_morphism B C),
        f = g → h ∘ f = h ∘ g.
    intros A B C f g h eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem rcompose : ∀ {A B C} {f g : cat_morphism B C} (h : cat_morphism A B),
        f = g → f ∘ h = g ∘ h.
    intros A B C f g h eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem lrcompose : ∀ {A B C} {f g : cat_morphism B C} {h i : cat_morphism A B},
        f = g → h = i → f ∘ h = g ∘ i.
    intros A B C f g h i eq1 eq2.
    rewrite eq1, eq2.
    reflexivity.
Qed.

Theorem cat_inverse_unique : ∀ {A B} (f : cat_morphism A B) g1 g2,
        f ∘ g1 = cat_id B → g1 ∘ f = cat_id A →
        f ∘ g2 = cat_id B → g2 ∘ f = cat_id A →
        g1 = g2.
    intros A B f g1 g2 fg1 g1f fg2 g2f.
    apply lcompose with g2 in fg1.
    rewrite cat_assoc in fg1.
    rewrite g2f in fg1.
    rewrite cat_lid, cat_rid in fg1.
    exact fg1.
Qed.

End Category.
