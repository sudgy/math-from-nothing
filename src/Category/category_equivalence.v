Require Import init.

Require Export category_base.
Require Import category_natural_transformation.

Record cat_equivalence {C1 C2 : Category}
    (F : Functor C1 C2) (G : Functor C2 C1) := make_cat_equiv
{
    cat_equiv_η : (𝟙 : Functor C1 C1) ≅ G ∘ F;
    cat_equiv_ε : (F ∘ G : Functor C2 C2) ≅ 𝟙;
}.

Definition cat_equivalent (C1 C2 : Category)
    := ∃ (F : Functor C1 C2) (G : Functor C2 C1),
        inhabited (cat_equivalence F G).

Notation "A ≃ B" := (cat_equivalent A B) (at level 70, no associativity).

Theorem cat_equiv_refl : ∀ (C : Category), C ≃ C.
Proof.
    intros C.
    exists 𝟙, 𝟙.
    split.
    split.
    -   rewrite cat_lid.
        apply isomorphic_refl.
    -   rewrite cat_lid.
        apply isomorphic_refl.
Qed.

Theorem cat_equiv_sym_base : ∀ {C1 C2} (F : Functor C1 C2) (G : Functor C2 C1),
    cat_equivalence F G → cat_equivalence G F.
Proof.
    intros C1 C2 F G [iso1 iso2].
    apply isomorphic_sym in iso1, iso2.
    exact (make_cat_equiv _ _ _ _ iso2 iso1).
Qed.

Theorem cat_equiv_sym : ∀ C1 C2, C1 ≃ C2 → C2 ≃ C1.
Proof.
    intros C1 C2 [F [G [iso]]].
    apply cat_equiv_sym_base in iso.
    exists G, F.
    split.
    exact iso.
Qed.

Theorem cat_equiv_trans : ∀ (C1 C2 C3 : Category), C1 ≃ C2 → C2 ≃ C3 → C1 ≃ C3.
Proof.
    intros C1 C2 C3 C12 C23.
    destruct C12 as [F1 [G1 [[iso1 iso2]]]].
    destruct C23 as [F2 [G2 [[iso3 iso4]]]].
    exists (F2 ∘ F1), (G1 ∘ G2).
    do 2 split.
    -   apply (isomorphic_trans iso1).
        apply (lnat_iso G1) in iso3.
        apply (rnat_iso F1) in iso3.
        rewrite cat_rid in iso3.
        rewrite cat_assoc.
        rewrite cat_assoc in iso3.
        exact iso3.
    -   apply (isomorphic_trans2 iso4).
        apply (lnat_iso F2) in iso2.
        apply (rnat_iso G2) in iso2.
        rewrite cat_rid in iso2.
        rewrite cat_assoc.
        rewrite cat_assoc in iso2.
        exact iso2.
Qed.

Section FunctorEquivalence1.

Context {C1 C2 : Category}.
Context (F : Functor C1 C2) (G : Functor C2 C1).
Hypothesis equiv : cat_equivalence F G.

Theorem functor_equiv_faithful1 : faithful_functor F.
Proof.
    intros A B.
    split.
    intros f g eq.
    apply (f_equal (⌈G⌉)) in eq.
    destruct equiv as [[η1 η2 η_iso] [ε1 ε2 ε_iso]].
    pose proof (nat_trans_commute η1 f) as eq2.
    pose proof (nat_trans_commute η1 g) as eq3.
    cbn in eq2, eq3.
    rewrite eq in eq2; clear eq.
    rewrite <- eq3 in eq2; clear eq3.
    apply is_isomorphism_pair_left in η_iso.
    rewrite nat_isomorphism_components in η_iso.
    pose proof (η_iso B) as [h [h_eq1 h_eq2]].
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
    destruct equiv as [η_iso [ε ε' ε_iso]].
    apply is_isomorphism_pair_left in ε_iso.
    rewrite nat_isomorphism_components in ε_iso.
    pose proof (ε_iso B) as [B' B'_iso].
    split.
    exact (make_isomorphism _ _ B'_iso).
Qed.

End FunctorEquivalence1.

Section FunctorEquivalence2.

Context {C1 C2 : Category}.
Context (F : Functor C1 C2) (G : Functor C2 C1).
Hypothesis equiv : cat_equivalence F G.

Theorem functor_equiv_faithful2 : faithful_functor G.
Proof.
    apply cat_equiv_sym_base in equiv.
    apply (functor_equiv_faithful1 G F equiv).
Qed.

Theorem functor_equiv_sur2 : essentially_surjective G.
Proof.
    apply cat_equiv_sym_base in equiv.
    apply (functor_equiv_sur1 G F equiv).
Qed.

Theorem functor_equiv_full1 : full_functor F.
Proof.
    intros A B.
    split.
    intros f.
    destruct equiv as [η_iso ε_iso].
    destruct η_iso as [η η' η_iso].
    apply is_isomorphism_pair_left in η_iso.
    rewrite nat_isomorphism_components in η_iso.
    pose proof (η_iso A) as [g [g_eq1 g_eq2]].
    pose proof (η_iso B) as [h [h_eq1 h_eq2]].
    cbn in *.
    exists (h ∘ (⌈G⌉ f) ∘ (η A)).
    apply functor_equiv_faithful2.
    do 4 rewrite functor_compose.
    pose proof (nat_trans_commute η (η A)) as eq.
    cbn in eq.
    apply rcompose with g in eq.
    do 2 rewrite <- cat_assoc in eq.
    rewrite g_eq1 in eq.
    do 2 rewrite cat_rid in eq.
    rewrite <- eq; clear eq.
    rewrite <- cat_assoc.
    rewrite <- (nat_trans_commute η (⌈G⌉ f)); cbn.
    rewrite cat_assoc.
    rewrite <- (nat_trans_commute η h); cbn.
    rewrite h_eq1.
    apply cat_lid.
Qed.

End FunctorEquivalence2.
Section FunctorEquivalence3.

Context {C1 C2 : Category}.
Context (F : Functor C1 C2) (G : Functor C2 C1).
Hypothesis equiv : cat_equivalence F G.

Theorem functor_equiv_full2 : full_functor G.
Proof.
    apply cat_equiv_sym_base in equiv.
    apply (functor_equiv_full1 G F equiv).
Qed.

End FunctorEquivalence3.

Theorem functor_equivalence {C1 C2 : Category} :
    ∀ (F : Functor C1 C2),
    full_functor F → faithful_functor F → essentially_surjective F →
    cat_equivalent C1 C2.
Proof.
    intros F F_full F_faith F_sur.
    exists F.
    pose (G_f B := ex_val (F_sur B)).
    pose (g A := iso_g (indefinite_description (ex_proof (F_sur A)))).
    pose (h A := iso_f (indefinite_description (ex_proof (F_sur A)))).
    pose (G_morphism A B (f : morphism A B) :=
        ex_val (sur _ (Surjective := F_full _ _) (g B ∘ f ∘ h A))
    ).
    assert (∀ A, g A ∘ h A = 𝟙) as gh_id.
    {
        intros A.
        unfold g, h.
        destruct (indefinite_description _) as [f f' [f_eq1 f_eq2]]; cbn.
        exact f_eq2.
    }
    assert (∀ A, h A ∘ g A = 𝟙) as hg_id.
    {
        intros A.
        unfold g, h.
        destruct (indefinite_description _) as [f f' [f_eq1 f_eq2]]; cbn.
        exact f_eq1.
    }
    assert (∀ A B (f : morphism A B), ⌈F⌉ (G_morphism _ _ f) = g B ∘ f ∘ h A)
        as G_morphism_eq.
    {
        intros A B f.
        unfold G_morphism.
        rewrite_ex_val f' f'_eq.
        exact f'_eq.
    }
    pose (G := make_functor _ _ G_f G_morphism).
    prove_parts G.
    {
        intros A B C f1 f2.
        apply F_faith.
        rewrite functor_compose.
        do 3 rewrite G_morphism_eq.
        rewrite <- (cat_assoc _ (h B)).
        do 2 rewrite (cat_assoc (h B)).
        rewrite hg_id, cat_lid.
        do 2 rewrite cat_assoc.
        reflexivity.
    }
    {
        intros A.
        apply F_faith.
        rewrite G_morphism_eq, functor_id.
        rewrite cat_rid.
        apply gh_id.
    }
    pose (η_f A := ex_val (sur _ (Surjective := F_full _ _) (g (F A)))
        : morphism ((𝟏) A) ((G ∘ F) A)).
    assert (∀ A, ⌈F⌉ (η_f A) = g (F A)) as η_f_eq.
    {
        intros A.
        exact (ex_proof (sur _ (g (F A)))).
    }
    pose (η := make_nat_trans _ _ η_f).
    prove_parts η.
    {
        intros A B f.
        cbn.
        apply F_faith.
        do 2 rewrite functor_compose.
        do 2 rewrite η_f_eq.
        rewrite G_morphism_eq.
        rewrite <- (cat_assoc _ (h (F A))).
        rewrite hg_id, cat_rid.
        reflexivity.
    }
    pose (ε := make_nat_trans _ _ (λ B, h B : morphism ((F ∘ G) B) (𝟏 B))).
    prove_parts ε.
    {
        intros A B f.
        cbn.
        rewrite G_morphism_eq.
        do 2 rewrite cat_assoc.
        rewrite hg_id, cat_lid.
        reflexivity.
    }
    exists G.
    split; split.
    -   apply (is_isomorphism_isomorphic η).
        apply nat_isomorphism_components.
        intros A.
        unfold is_isomorphism.
        exists (ex_val (sur _ (Surjective := F_full _ _) (h (F A)))).
        rewrite_ex_val f f_eq.
        split.
        +   apply F_faith.
            rewrite functor_compose, functor_id.
            rewrite η_f_eq, f_eq.
            apply gh_id.
        +   apply F_faith.
            rewrite functor_compose, functor_id.
            rewrite η_f_eq, f_eq.
            apply hg_id.
    -   apply (is_isomorphism_isomorphic ε).
        apply nat_isomorphism_components.
        intros A.
        exists (g A).
        cbn.
        split.
        +   apply hg_id.
        +   apply gh_id.
Qed.
