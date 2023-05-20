Require Import init.

Require Export category_def.

Require Import set.

Set Universe Polymorphism.

Section Category.

Context {C0 : Category} {A B C : C0}.

Theorem lcompose : ∀ {f g : morphism A B} (h : morphism B C),
    f = g → h ∘ f = h ∘ g.
Proof.
    intros f g h eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem rcompose : ∀ {f g : morphism B C} (h : morphism A B),
    f = g → f ∘ h = g ∘ h.
Proof.
    intros f g h eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem lrcompose : ∀ {f g : morphism B C} {h i : morphism A B},
    f = g → h = i → f ∘ h = g ∘ i.
Proof.
    intros f g h i eq1 eq2.
    rewrite eq1, eq2.
    reflexivity.
Qed.

End Category.

Definition is_isomorphism_pair {C : Category} {A B : C}
    (f : morphism A B) (g : morphism B A) := f ∘ g = 𝟙 ∧ g ∘ f = 𝟙.
Definition is_isomorphism {C : Category} {A B : C} (f : morphism A B)
    := ∃ g, is_isomorphism_pair f g.

Record isomorphism {C : Category} (A B : C) := make_isomorphism {
    iso_f : morphism A B;
    iso_g : morphism B A;
    iso_inv : is_isomorphism_pair iso_f iso_g;
}.

Arguments make_isomorphism {C A B}.
Arguments iso_f {C A B}.
Arguments iso_g {C A B}.
Arguments iso_inv {C A B}.

Notation "A ≅ B" := (isomorphism A B) (at level 70, no associativity).

Theorem iso_fg : ∀ {C : Category} {A B : C} (AB : isomorphism A B),
    iso_f AB ∘ iso_g AB = 𝟙.
Proof.
    intros C A B AB.
    apply iso_inv.
Qed.
Theorem iso_gf : ∀ {C : Category} {A B : C} (AB : isomorphism A B),
    iso_g AB ∘ iso_f AB = 𝟙.
Proof.
    intros C A B AB.
    apply iso_inv.
Qed.

Section Isomorphism.

Context {C0 : Category}.

Theorem id_isomorphism : ∀ A : C0, is_isomorphism (cat_id A).
Proof.
    intros A.
    exists 𝟙.
    split; apply cat_lid.
Qed.

Theorem compose_isomorphism : ∀ {A B C : C0}
    (f : morphism B C) (g : morphism A B),
    is_isomorphism f → is_isomorphism g → is_isomorphism (f ∘ g).
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
    is_isomorphism_pair f g1 → is_isomorphism_pair f g2 → g1 = g2.
Proof.
    intros A B f g1 g2 [fg1 g1f] [fg2 g2f].
    apply lcompose with g2 in fg1.
    rewrite cat_assoc in fg1.
    rewrite g2f in fg1.
    rewrite cat_lid, cat_rid in fg1.
    exact fg1.
Qed.

Theorem isomorphic_refl : ∀ A : C0, A ≅ A.
Proof.
    intros A.
    exists 𝟙 𝟙.
    split; apply cat_lid.
Qed.
Theorem isomorphic_sym : ∀ A B : C0, A ≅ B → B ≅ A.
Proof.
    intros A B [f g [eq1 eq2]].
    exists g f.
    split; assumption.
Qed.
Theorem isomorphic_trans : ∀ {A B C : C0}, A ≅ B → B ≅ C → A ≅ C.
Proof.
    intros A B C [f1 g1 eq1] [f2 g2 eq2].
    apply indefinite_description.
    pose proof (compose_isomorphism f2 f1
        (ex_intro _ g2 eq2) (ex_intro _ g1 eq1)) as [g eq].
    split.
    exact (make_isomorphism _ _ eq).
Qed.
Theorem isomorphic_trans2 : ∀ {A B C : C0}, B ≅ C → A ≅ B → A ≅ C.
Proof.
    intros A B C eq1 eq2.
    exact (isomorphic_trans eq2 eq1).
Qed.

Theorem is_isomorphism_pair_left : ∀ {A B : C0}
    (a : morphism A B) b, is_isomorphism_pair a b → is_isomorphism a.
Proof.
    intros A B a b eq.
    exists b.
    exact eq.
Qed.

Theorem is_isomorphism_pair_right : ∀ {A B : C0}
    (a : morphism A B) b, is_isomorphism_pair a b → is_isomorphism b.
Proof.
    intros A B a b eq.
    exists a.
    split; apply eq.
Qed.

Theorem is_isomorphism_isomorphic : ∀ {A B : C0}
    (f : morphism A B), is_isomorphism f → A ≅ B.
Proof.
    intros A B f f_iso.
    apply indefinite_description.
    destruct f_iso as [g [fg gf]].
    split.
    exists f g.
    split; assumption.
Qed.

End Isomorphism.

Program Definition dual_category (C0 : Category) : Category := {|
    cat_U := cat_U C0;
    morphism A B := morphism B A;
    cat_compose A B C f g := cat_compose g f;
    cat_id A := cat_id A;
|}.
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

Theorem dual_isomorphism : ∀ {C : Category} {A B : C} (f : morphism A B),
    is_isomorphism (C := C) f ↔ is_isomorphism (C := dual_category C) f.
Proof.
    intros C A B f.
    split.
    -   intros [g [g_eq1 g_eq2]].
        exists g.
        split; assumption.
    -   intros [g [g_eq1 g_eq2]].
        exists g.
        split; assumption.
Qed.

Theorem cat_dual_dual : ∀ C, C = dual_category (dual_category C).
Proof.
    intros C.
    unshelve eapply cat_eq.
    -   reflexivity. (* This is actually asking about cat_U being equal *)
    -   cbn.
        reflexivity.
    -   cbn.
        reflexivity.
    -   cbn.
        reflexivity.
Qed.

Program Definition product_category (C1 : Category) (C2 : Category) := {|
    cat_U := C1 * C2;
    morphism A B
        := prod_type (morphism (fst A) (fst B)) (morphism (snd A) (snd B));
    cat_compose A B C f g := (fst f ∘ fst g, snd f ∘ snd g);
    cat_id A := (𝟙, 𝟙);
|}.
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

Program Definition subcategory {C0 : Category} (S : SubCategory C0) := {|
    cat_U := set_type (subcat_S S);
    morphism A B := set_type (subcat_morphism S (A := [A|]) (B := [B|]));
    cat_compose A B C f g := [_|subcat_compose S [f|] [g|] [|f] [|g]];
    cat_id A := [_|subcat_id S [A|]];
|}.
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

Unset Universe Polymorphism.
