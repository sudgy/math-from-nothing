Require Import init.

Require Import set.

(* begin show *)
Set Universe Polymorphism.
(* end show *)

(** Note: I am learning category theory while writing this.  Apologies if
anything here is incorrect/not specified in the best way.
*)

(* begin show *)
Record Category := make_category {
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
(* end show *)

Arguments cat_compose {c A B C} f g.
Arguments morphism {c}.
Arguments cat_id {c}.
Arguments cat_assoc {c A B C D}.
Arguments cat_lid {c A B}.
Arguments cat_rid {c A B}.

Infix "∘" := cat_compose.
Notation "𝟙" := (cat_id _).

Definition cat_domain {C0 : Category} {A B : C0} (f : morphism A B) := A.
Definition cat_codomain {C0 : Category} {A B : C0} (f : morphism A B) := B.

Definition cat_is_inverse {C0 : Category} {A B : C0}
    (f : morphism A B) (g : morphism B A) := f ∘ g = 𝟙 ∧ g ∘ f = 𝟙.
Definition isomorphism {C0 : Category} {A B : C0} (f : morphism A B)
    := ∃ g, f ∘ g = 𝟙 ∧ g ∘ f = 𝟙.

Definition cat_inverse {C0 : Category} {A B : C0}
    (f : morphism A B) (H : isomorphism f) := ex_val H.

Definition isomorphic {C0 : Category} (A B : C0)
    := ∃ f : morphism A B, isomorphism f.

Notation "A ≅ B" := (isomorphic A B) (at level 70, no associativity).

(* begin show *)
Program Definition dual_category (C0 : Category) : Category := {|
    cat_U := cat_U C0;
    morphism A B := morphism B A;
    cat_compose A B C f g := cat_compose g f;
    cat_id A := cat_id A;
|}.
(* end show *)
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

(* begin show *)
Program Definition product_category (C1 : Category) (C2 : Category) := {|
    cat_U := prod_type C1 C2;
    morphism A B
        := prod_type (morphism (fst A) (fst B)) (morphism (snd A) (snd B));
    cat_compose A B C f g := (fst f ∘ fst g, snd f ∘ snd g);
    cat_id A := (𝟙, 𝟙);
|}.
(* end show *)
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

Record SubCategory (C0 : Category) := make_subcategory {
    subcat_S : C0 → Prop;
    subcat_morphism : ∀ {A B : C0}, morphism A B → Prop;
    subcat_compose : ∀ {A B C : C0} (f : morphism B C) (g : morphism A B),
        subcat_morphism f → subcat_morphism g → subcat_morphism (f ∘ g);
    subcat_id : ∀ A, subcat_morphism (cat_id A);
}.

Arguments subcat_S {C0}.
Arguments subcat_morphism {C0} s {A B}.
Arguments subcat_compose {C0} s {A B C}.
Arguments subcat_id {C0}.

(* begin show *)
Program Definition subcategory {C0 : Category} (S : SubCategory C0) := {|
    cat_U := set_type (subcat_S S);
    morphism A B := set_type (subcat_morphism S (A := [A|]) (B := [B|]));
    cat_compose A B C f g := [_|subcat_compose S [f|] [g|] [|f] [|g]];
    cat_id A := [_|subcat_id S [A|]];
|}.
(* end show *)
Next Obligation.
    apply set_type_eq; cbn.
    apply cat_assoc.
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply cat_lid.
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply cat_rid.
Qed.

Definition full_subcategory {C0 : Category} (S : SubCategory C0) := ∀ A B,
    subcat_morphism S (A:=A) (B:=B) = all.

(* begin hide *)
Section Category.

Context {C0 : Category}.

(* end hide *)
Theorem lcompose : ∀ {A B C : C0} {f g : morphism A B} (h : morphism B C),
    f = g → h ∘ f = h ∘ g.
Proof.
    intros A B C f g h eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem rcompose : ∀ {A B C : C0} {f g : morphism B C} (h : morphism A B),
    f = g → f ∘ h = g ∘ h.
Proof.
    intros A B C f g h eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem lrcompose : ∀ {A B C : C0} {f g : morphism B C} {h i : morphism A B},
    f = g → h = i → f ∘ h = g ∘ i.
Proof.
    intros A B C f g h i eq1 eq2.
    rewrite eq1, eq2.
    reflexivity.
Qed.

Theorem id_isomorphism : ∀ A : C0, isomorphism (cat_id A).
Proof.
    intros A.
    exists 𝟙.
    split; apply cat_lid.
Qed.

Theorem compose_isomorphism : ∀ {A B C : C0}
    (f : morphism B C) (g : morphism A B),
    isomorphism f → isomorphism g → isomorphism (f ∘ g).
Proof.
    intros A B C f g [f' [f1 f2]] [g' [g1 g2]].
    exists (g' ∘ f').
    split.
    -   rewrite <- cat_assoc.
        rewrite (cat_assoc g).
        rewrite g1.
        rewrite cat_lid.
        exact f1.
    -   rewrite <- cat_assoc.
        rewrite (cat_assoc f').
        rewrite f2.
        rewrite cat_lid.
        exact g2.
Qed.

Theorem cat_inverse_unique : ∀ {A B : C0} (f : morphism A B) g1 g2,
    f ∘ g1 = 𝟙 → g1 ∘ f = 𝟙 → f ∘ g2 = 𝟙 → g2 ∘ f = 𝟙 → g1 = g2.
Proof.
    intros A B f g1 g2 fg1 g1f fg2 g2f.
    apply lcompose with g2 in fg1.
    rewrite cat_assoc in fg1.
    rewrite g2f in fg1.
    rewrite cat_lid, cat_rid in fg1.
    exact fg1.
Qed.

Theorem isomorphic_refl : ∀ A : C0, A ≅ A.
Proof.
    intros A.
    exists 𝟙, 𝟙.
    rewrite cat_lid.
    split; reflexivity.
Qed.
Theorem isomorphic_sym : ∀ A B : C0, A ≅ B → B ≅ A.
Proof.
    intros A B [f [g [eq1 eq2]]].
    exists g, f.
    split; assumption.
Qed.
Theorem isomorphic_trans : ∀ {A B C : C0}, A ≅ B → B ≅ C → A ≅ C.
Proof.
    intros A B C [f1 [g1 [eq11 eq12]]] [f2 [g2 [eq21 eq22]]].
    exists (f2 ∘ f1).
    exists (g1 ∘ g2).
    split.
    -   rewrite <- cat_assoc.
        rewrite (cat_assoc f1).
        rewrite eq11.
        rewrite cat_lid.
        exact eq21.
    -   rewrite <- cat_assoc.
        rewrite (cat_assoc g2).
        rewrite eq22.
        rewrite cat_lid.
        exact eq12.
Qed.
Theorem isomorphic_trans2 : ∀ {A B C : C0}, B ≅ C → A ≅ B → A ≅ C.
Proof.
    intros A B C eq1 eq2.
    exact (isomorphic_trans eq2 eq1).
Qed.

Theorem dual_isomorphism : ∀ {A B : C0} (f : morphism A B),
    isomorphism (C0 := C0) f ↔ isomorphism (C0:=dual_category C0) f.
Proof.
    intros A B f.
    split.
    -   intros [g [g_eq1 g_eq2]].
        exists g.
        cbn in *.
        split; assumption.
    -   intros [g [g_eq1 g_eq2]].
        exists g.
        cbn in *.
        split; assumption.
Qed.

(* begin hide *)
End Category.

(* end hide *)
Definition convert_type {A B : Type} (H : A = B) (x : A) : B.
    rewrite H in x.
    exact x.
Defined.

Theorem cat_eq : ∀ C1 C2,
    ∀ H : @cat_U C1 = @cat_U C2,
    ∀ H' : (∀ A B, morphism A B =
                   morphism (convert_type H A) (convert_type H B)),
    (∀ A B C (f : morphism B C) (g : morphism A B),
        convert_type (H' _ _) (f ∘ g) =
        (convert_type (H' _ _) f) ∘ (convert_type (H' _ _) g)) →
    (∀ A, convert_type (H' A A) (cat_id A) = cat_id (convert_type H A)) →
    C1 = C2.
Proof.
    intros [U1 morphism1 compose1 id1 assoc1 lid1 rid1]
           [U2 morphism2 compose2 id2 assoc2 lid2 rid2] H H' eq1 eq2.
    cbn in *.
    destruct H.
    assert (morphism1 = morphism2) as eq.
    {
        apply functional_ext.
        intros A.
        apply functional_ext.
        apply H'.
    }
    subst morphism2; cbn in *.
    pose (H'2 A B := Logic.eq_refl (morphism1 A B)).
    rewrite (proof_irrelevance H' H'2) in eq1, eq2.
    clear H'.
    cbn in *.
    assert (compose1 = compose2) as eq.
    {
        apply functional_ext; intros A.
        apply functional_ext; intros B.
        apply functional_ext; intros C.
        apply functional_ext; intros f.
        apply functional_ext; intros g.
        apply eq1.
    }
    subst compose2; clear eq1.
    assert (id1 = id2) as eq.
    {
        apply functional_ext; intros A.
        apply eq2.
    }
    subst id2; clear eq2.
    rewrite (proof_irrelevance assoc2 assoc1).
    rewrite (proof_irrelevance lid2 lid1).
    rewrite (proof_irrelevance rid2 rid1).
    reflexivity.
Qed.

Theorem cat_dual_dual : ∀ C, C = dual_category (dual_category C).
Proof.
    intros C.
    assert (@cat_U C = @cat_U (dual_category (dual_category C))) as H
        by reflexivity.
    pose (H2 := Logic.eq_refl (cat_U C)).
    assert (∀ A B, morphism A B =
                   morphism (convert_type H A) (convert_type H B)) as H'.
    {
        intros A B.
        rewrite (proof_irrelevance H H2).
        cbn.
        reflexivity.
    }
    apply (cat_eq _ _ H H').
    all: pose proof (proof_irrelevance H H2) as H_eq.
    all: subst H.
    all: unfold H2 in *; cbn in *.
    all: clear H2.
    all: pose (H'2 A B := Logic.eq_refl (morphism (c := C) A B)).
    all: rewrite (proof_irrelevance H' H'2).
    all: cbn.
    all: reflexivity.
Qed.

Unset Universe Polymorphism.
