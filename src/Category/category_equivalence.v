Require Import init.

Require Export category_base.
Require Import category_natural_transformation.

Definition cat_equivalence {C1 C2 : Category}
    (F : Functor C1 C2) (G : Functor C2 C1)
    (η : NatTransformation 𝟙 (G ∘ F))
    (ε : NatTransformation (F ∘ G) 𝟙)
    := is_isomorphism η ∧ is_isomorphism ε.

Definition cat_equivalent (C1 C2 : Category)
    := ∃ (F : Functor C1 C2) (G : Functor C2 C1) η ε,
        cat_equivalence F G η ε.

Notation "A ⋍ B" := (cat_equivalent A B) (at level 70, no associativity).

Theorem cat_equiv_refl : ∀ (C0 : Category), C0 ⋍ C0.
Proof.
    intros C0.
    exists 𝟙, 𝟙.
    unfold cat_equivalence.
    rewrite cat_lid.
    exists 𝟙, 𝟙.
    split; apply id_isomorphism.
Qed.

Theorem cat_equiv_trans : ∀ (C1 C2 C3 : Category), C1 ⋍ C2 → C2 ⋍ C3 → C1 ⋍ C3.
Proof.
    intros C1 C2 C3 C12 C23.
    destruct C12 as [F1 [G1 [η1 [ε1 [η1_iso ε1_iso]]]]].
    destruct C23 as [F2 [G2 [η2 [ε2 [η2_iso ε2_iso]]]]].
    exists (F2 ∘ F1), (G1 ∘ G2).
    assert (isomorphism (𝟙 : Functor _ _) (G1 ∘ F1)) as iso1
        by (exists η1 (ex_val η1_iso); exact (ex_proof η1_iso)).
    assert (isomorphism (F1 ∘ G1 : Functor _ _) 𝟙) as iso2
        by (exists ε1 (ex_val ε1_iso); exact (ex_proof ε1_iso)).
    assert (isomorphism (𝟙 : Functor _ _) (G2 ∘ F2)) as iso3
        by (exists η2 (ex_val η2_iso); exact (ex_proof η2_iso)).
    assert (isomorphism (F2 ∘ G2 : Functor _ _) 𝟙) as iso4
        by (exists ε2 (ex_val ε2_iso); exact (ex_proof ε2_iso)).
    assert (isomorphism (𝟙 : Functor _ _) (G1 ∘ G2 ∘ (F2 ∘ F1))) as [η η_iso].
    {
        apply (isomorphic_trans iso1).
        rewrite <- (cat_lid F1) at 1.
        rewrite <- cat_assoc.
        apply lnat_iso.
        rewrite cat_assoc.
        apply rnat_iso.
        exact iso3.
    }
    assert (isomorphism (F2 ∘ F1 ∘ (G1 ∘ G2) : Functor _ _) 𝟙) as [ε ε_iso].
    {
        apply (isomorphic_trans2 iso4).
        rewrite <- (cat_lid G2) at 2.
        rewrite <- cat_assoc.
        apply lnat_iso.
        rewrite cat_assoc.
        apply rnat_iso.
        exact iso2.
    }
    exists η, ε.
    split.
    -   exists η_iso.
        exact iso_inv.
    -   exists ε_iso.
        exact iso_inv0.
Qed.

(* begin hide *)
Section FunctorEquivalence1.

(* end hide *)
Context {C1 C2 : Category}.
Context (F : Functor C1 C2) (G : Functor C2 C1).
Context (η : NatTransformation 𝟙 (G ∘ F)).
Context (ε : NatTransformation (F ∘ G) 𝟙).
Hypothesis equiv : cat_equivalence F G η ε.

Theorem cat_equiv_sym_base : ∃ η' ε', cat_equivalence G F η' ε'.
Proof.
    destruct equiv as [η_iso ε_iso].
    rewrite nat_isomorphism_components in η_iso.
    rewrite nat_isomorphism_components in ε_iso.
    pose (η'_f A := ex_val (ε_iso A)).
    assert (∀ {A B} f, η'_f B ∘ (⌈𝟏⌉ f) = (⌈F ∘ G⌉ f) ∘ η'_f A) as η'_commute.
    {
        intros A B f.
        unfold η'_f.
        rewrite_ex_val B' [B'_eq1 B'_eq2].
        rewrite_ex_val A' [A'_eq1 A'_eq2].
        cbn.
        pose proof (nat_trans_commute ε f) as eq.
        cbn in *.
        apply lcompose with B' in eq.
        rewrite cat_assoc in eq.
        rewrite B'_eq2 in eq.
        rewrite cat_lid in eq.
        rewrite eq.
        do 2 rewrite <- cat_assoc.
        rewrite A'_eq1.
        rewrite cat_rid.
        reflexivity.
    }
    pose (η' := {|nat_trans_f := η'_f; nat_trans_commute := η'_commute|}).
    pose (ε'_f A := ex_val (η_iso A)).
    assert (∀ {A B} f, ε'_f B ∘ (⌈G ∘ F⌉ f) = (⌈𝟏⌉ f) ∘ ε'_f A) as ε'_commute.
    {
        intros A B f.
        unfold ε'_f.
        rewrite_ex_val B' [B'_eq1 B'_eq2].
        rewrite_ex_val A' [A'_eq1 A'_eq2].
        cbn.
        pose proof (nat_trans_commute η f) as eq.
        cbn in *.
        apply rcompose with A' in eq.
        rewrite <- (cat_assoc _ (η A) A') in eq.
        cbn in *.
        rewrite A'_eq1 in eq.
        rewrite cat_rid in eq.
        rewrite <- eq.
        do 2 rewrite cat_assoc.
        rewrite B'_eq2.
        rewrite cat_lid.
        reflexivity.
    }
    pose (ε' := {|nat_trans_f := ε'_f; nat_trans_commute := ε'_commute|}).
    cbn in *.
    exists η', ε'.
    split; rewrite nat_isomorphism_components.
    -   intros A.
        cbn.
        unfold η'_f.
        unfold ex_val.
        destruct (ex_to_type _) as [B [B_eq1 B_eq2]]; cbn.
        exists (ε A).
        split; assumption.
    -   intros A.
        cbn.
        unfold ε'_f.
        unfold ex_val.
        destruct (ex_to_type _) as [B [B_eq1 B_eq2]]; cbn.
        exists (η A).
        split; assumption.
Qed.

Theorem functor_equiv_faithful1 : faithful_functor F.
Proof.
    intros A B.
    split.
    intros f g eq.
    apply (f_equal (functor_morphism G)) in eq.
    pose proof (nat_trans_commute η f) as eq2.
    pose proof (nat_trans_commute η g) as eq3.
    cbn in *.
    rewrite eq in eq2; clear eq.
    rewrite <- eq3 in eq2; clear eq3.
    destruct equiv as [η_iso ε_iso].
    rewrite nat_isomorphism_components in η_iso.
    rewrite nat_isomorphism_components in ε_iso.
    pose proof (η_iso B) as [h [h_eq1 h_eq2]].
    cbn in *.
    apply lcompose with h in eq2.
    do 2 rewrite cat_assoc in eq2.
    rewrite h_eq2 in eq2.
    do 2 rewrite cat_lid in eq2.
    exact eq2.
Qed.

Theorem functor_equiv_sur1 : essentially_surjective F.
Proof.
    intros B.
    exists (G B).
    destruct equiv as [η_iso ε_iso].
    rewrite nat_isomorphism_components in ε_iso.
    pose proof (ε_iso B) as [B' B'_iso].
    split.
    exact (make_isomorphism _ _ B'_iso).
Qed.

(* begin hide *)
End FunctorEquivalence1.

(* end hide *)
Theorem cat_equiv_sym : ∀ C1 C2, cat_equivalent C1 C2 → cat_equivalent C2 C1.
Proof.
    intros C1 C2 [F [G [η [ε equiv]]]].
    pose proof (cat_equiv_sym_base F G η ε equiv) as [η' [ε' equiv']].
    exists G, F, η', ε'.
    exact equiv'.
Qed.

(* begin hide *)
Section FunctorEquivalence2.

Context {C1 C2 : Category}.
Context (F : Functor C1 C2) (G : Functor C2 C1).
Context (η : NatTransformation 𝟙 (G ∘ F)).
Context (ε : NatTransformation (F ∘ G) 𝟙).
Hypothesis equiv : cat_equivalence F G η ε.

(* end hide *)
Theorem functor_equiv_faithful2 : faithful_functor G.
Proof.
    pose proof (cat_equiv_sym_base F G η ε equiv) as [η' [ε' equiv']].
    apply (functor_equiv_faithful1 G F η' ε' equiv').
Qed.

Theorem functor_equiv_sur2 : essentially_surjective G.
Proof.
    pose proof (cat_equiv_sym_base F G η ε equiv) as [η' [ε' equiv']].
    apply (functor_equiv_sur1 G F η' ε' equiv').
Qed.

Theorem functor_equiv_full1 : full_functor F.
Proof.
    intros A B.
    split.
    intros f.
    destruct equiv as [η_iso ε_iso].
    rewrite nat_isomorphism_components in η_iso.
    rewrite nat_isomorphism_components in ε_iso.
    pose proof (η_iso A) as [g' [g_eq1 g_eq2]].
    pose (g := nat_trans_f η A).
    pose proof (η_iso B) as [h [h_eq1 h_eq2]].
    cbn in *.
    pose (f2 := functor_morphism G f).
    pose (f3 := h ∘ f2 ∘ g).
    exists f3.
    unfold f3, f2, g; clear f3 f2 g.
    pose proof (functor_equiv_faithful2) as G_faith.
    apply G_faith.
    repeat rewrite functor_compose.
    pose proof (nat_trans_commute η (nat_trans_f η A)) as eq.
    cbn in eq.
    apply rcompose with g' in eq.
    do 2 rewrite <- cat_assoc in eq.
    rewrite g_eq1 in eq.
    do 2 rewrite cat_rid in eq.
    rewrite <- eq; clear eq.
    pose proof (nat_trans_commute η (functor_morphism G f)) as eq.
    cbn in eq.
    rewrite <- cat_assoc.
    rewrite <- eq; clear eq.
    rewrite cat_assoc.
    pose proof (nat_trans_commute η h) as eq.
    cbn in eq.
    rewrite <- eq.
    rewrite h_eq1.
    rewrite cat_lid.
    reflexivity.
Qed.

(* begin hide *)
End FunctorEquivalence2.
Section FunctorEquivalence3.

Context {C1 C2 : Category}.
Context (F : Functor C1 C2) (G : Functor C2 C1).
Context (η : NatTransformation 𝟙 (G ∘ F)).
Context (ε : NatTransformation (F ∘ G) 𝟙).
Hypothesis equiv : cat_equivalence F G η ε.

(* end hide *)
Theorem functor_equiv_full2 : full_functor G.
Proof.
    pose proof (cat_equiv_sym_base F G η ε equiv) as [η' [ε' equiv']].
    apply (functor_equiv_full1 G F η' ε' equiv').
Qed.

(* begin hide *)
End FunctorEquivalence3.

(* end hide *)
Theorem functor_equivalence {C1 C2 : Category} :
    ∀ (F : Functor C1 C2),
    full_functor F → faithful_functor F → essentially_surjective F →
    cat_equivalent C1 C2.
Proof.
    intros F F_full F_faith F_sur.
    exists F.
    pose (G_f B := ex_val (F_sur B)).
    pose (g B := iso_g (indefinite_description (ex_proof (F_sur B)))).
    pose (h A := iso_f (indefinite_description (ex_proof (F_sur A)))).
    pose (G_morphism A B (f : morphism A B) :=
        ex_val (sur _ (Surjective := F_full _ _) (g B ∘ f ∘ h A))
    ).
    assert (∀ A, g A ∘ h A = 𝟙) as gh_id.
    {
        intros A.
        unfold g, h.
        unfold ex_val, ex_proof.
        destruct (ex_to_type (F_sur A)) as [GA CC0]; cbn.
        destruct (indefinite_description CC0) as [f f' [f_eq1 f_eq2]]; cbn.
        exact f_eq2.
    }
    assert (∀ A, h A ∘ g A = 𝟙) as hg_id.
    {
        intros A.
        unfold g, h.
        unfold ex_val, ex_proof.
        destruct (ex_to_type (F_sur A)) as [GA CC0]; cbn.
        destruct (indefinite_description CC0) as [f f' [f_eq1 f_eq2]]; cbn.
        exact f_eq1.
    }
    assert (∀ {A B C} (f : morphism B C) (g : morphism A B),
        G_morphism _ _ (f ∘ g) = G_morphism _ _ f ∘ G_morphism _ _ g)
        as G_compose.
    {
        intros A B C f1 f2.
        unfold G_morphism.
        rewrite_ex_val f12' f12'_eq.
        rewrite_ex_val f1' f1'_eq.
        rewrite_ex_val f2' f2'_eq.
        clear G_morphism.
        pose proof (lrcompose f1'_eq f2'_eq) as eq.
        rewrite <- functor_compose in eq.
        rewrite <- cat_assoc in eq.
        do 2 rewrite (cat_assoc (h B)) in eq.
        rewrite hg_id in eq.
        rewrite cat_lid in eq.
        rewrite cat_assoc in eq.
        rewrite cat_assoc in f12'_eq.
        rewrite <- eq in f12'_eq.
        apply F_faith in f12'_eq.
        exact f12'_eq.
    }
    assert (∀ A, G_morphism _ _ (cat_id A) = 𝟙) as G_id.
    {
        intros A.
        unfold G_morphism.
        change (ex_type_val (ex_to_type (F_sur A))) with (G_f A).
        rewrite_ex_val f f_eq.
        rewrite cat_rid in f_eq.
        specialize (gh_id A).
        change (ex_type_val (ex_to_type (F_sur A))) with (G_f A) in *.
        rewrite gh_id in f_eq.
        rewrite <- functor_id in f_eq.
        apply F_faith in f_eq.
        exact f_eq.
    }
    pose (G := {|
        functor_f := G_f;
        functor_morphism := G_morphism;
        functor_compose := G_compose;
        functor_id := G_id;
    |} : Functor _ _).
    pose (η_f A := ex_val (sur _ (Surjective := F_full _ _) (g (F A)))
        : morphism ((𝟏) A) ((G ∘ F) A)).
    assert (∀ {A B} (f : morphism A B),
        η_f B ∘ (⌈𝟏⌉ f) = (⌈G ∘ F⌉ f) ∘ η_f A) as η_commute.
    {
        intros A B f0.
        cbn.
        unfold G_morphism.
        change (ex_type_val (ex_to_type (F_sur (F A)))) with (G_f (F A)).
        change (ex_type_val (ex_to_type (F_sur (F B)))) with (G_f (F B)).
        unfold η_f.
        rewrite_ex_val f1 f1_eq.
        rewrite_ex_val f2 f2_eq.
        rewrite_ex_val f3 f3_eq.
        rewrite <- f1_eq in f2_eq.
        pose proof (lrcompose f2_eq f3_eq) as eq.
        clear f1_eq f2_eq f3_eq.
        rewrite <- functor_compose in eq.
        rewrite <- functor_compose in eq.
        rewrite <- cat_assoc in eq.
        rewrite hg_id in eq.
        rewrite cat_rid in eq.
        apply F_faith in eq.
        symmetry; exact eq.
    }
    assert (∀ {A B} (f : morphism A B),
        h B ∘ (⌈F ∘ G⌉ f) = (⌈𝟏⌉ f) ∘ h A) as ε_commute.
    {
        intros A B f.
        cbn.
        unfold G_morphism.
        change (ex_type_val (ex_to_type (F_sur A))) with (G_f A).
        change (ex_type_val (ex_to_type (F_sur B))) with (G_f B).
        rewrite_ex_val f' f'_eq.
        rewrite f'_eq.
        do 2 rewrite cat_assoc.
        rewrite hg_id.
        rewrite cat_lid.
        reflexivity.
    }
    pose (ε_f B := h B : morphism ((F ∘ G) B) (𝟏 B)).
    pose (η := {|nat_trans_f := η_f; nat_trans_commute := η_commute|}).
    pose (ε := {|nat_trans_f := ε_f; nat_trans_commute := ε_commute|}).
    exists G, η, ε.
    split; rewrite nat_isomorphism_components.
    -   intros A.
        unfold is_isomorphism.
        exists (ex_val (sur _ (Surjective := F_full _ _) (h (F A)))).
        cbn.
        unfold η_f.
        change (ex_type_val (ex_to_type (F_sur (F A)))) with (G (F A)).
        rewrite_ex_val f1 f1_eq.
        rewrite_ex_val f2 f2_eq.
        split.
        +   pose proof (lrcompose f1_eq f2_eq) as eq.
            rewrite <- functor_compose in eq.
            specialize (gh_id (F A)).
            cbn in *.
            change (ex_type_val (ex_to_type (F_sur (F A)))) with (G_f (F A)) in *.
            rewrite gh_id in eq.
            rewrite <- functor_id in eq.
            apply F_faith in eq.
            exact eq.
        +   pose proof (lrcompose f2_eq f1_eq) as eq.
            rewrite <- functor_compose in eq.
            specialize (hg_id (F A)).
            cbn in *.
            change (ex_type_val (ex_to_type (F_sur (F A)))) with (G_f (F A)) in *.
            rewrite hg_id in eq.
            rewrite <- functor_id in eq.
            apply F_faith in eq.
            exact eq.
    -   intros A.
        unfold is_isomorphism.
        exists (g A).
        cbn.
        unfold ε_f.
        split.
        +   apply hg_id.
        +   apply gh_id.
Qed.
