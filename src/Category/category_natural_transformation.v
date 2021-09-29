Require Import init.

Require Export category_functor.

Class NatTransformation `{C1 : Category, C2 : Category}
    `(F : @Functor C1 C2, G : @Functor C1 C2) :=
{
    nat_trans_f : ∀ A,
        cat_morphism C2 (F ⌈A⌉) (G ⌈A⌉);
    nat_trans_commute : ∀ {A B} (f : cat_morphism C1 A B),
        nat_trans_f B ∘ (F ⋄ f) = (G ⋄ f) ∘ nat_trans_f A;
}.

Arguments nat_trans_f {C1 C2 F G} NatTransformation.
Arguments nat_trans_commute {C1 C2 F G} NatTransformation {A B}.

Notation "α • A" := (nat_trans_f α A) (at level 30).
(** So nat_trans_commute says:
    [(α • B) ∘ (F ⋄ f) = (G ⋄ f) ∘ (α • A)]
*)

Program Instance id_nat_transformation `{C1 : Category, C2 : Category}
    `(F : @Functor C1 C2) : NatTransformation F F :=
{
    nat_trans_f A := 𝟙
}.
Next Obligation.
    rewrite cat_lid.
    rewrite cat_rid.
    reflexivity.
Qed.

Notation "'𝕀'" := (id_nat_transformation _).

Program Instance vcompose_nat_transformation `{C1 : Category, C2 : Category}
    `{F : @Functor C1 C2, G : @Functor C1 C2, H : @Functor C1 C2}
    `(α : @NatTransformation C1 C2 G H, β : @NatTransformation C1 C2 F G)
    : NatTransformation F H :=
{
    nat_trans_f A := α • A ∘ β • A
}.
Next Obligation.
    rewrite cat_assoc.
    rewrite <- cat_assoc.
    rewrite nat_trans_commute.
    rewrite cat_assoc.
    rewrite nat_trans_commute.
    reflexivity.
Qed.

Program Instance hcompose_nat_transformation
    `{C1 : Category, C2 : Category, C3 : Category}
    `{F' : @Functor C2 C3, G' : @Functor C2 C3}
    `{F : @Functor C1 C2, G : @Functor C1 C2}
    `(β : @NatTransformation C2 C3 F' G', α : @NatTransformation C1 C2 F G)
    : NatTransformation (F' ○ F) (G' ○ G) :=
{
    nat_trans_f A := β • (G ⌈A⌉) ∘ (F' ⋄ α • A)
}.
Next Obligation.
    rewrite nat_trans_commute.
    rewrite <- cat_assoc.
    rewrite nat_trans_commute.
    rewrite cat_assoc.
    rewrite <- functor_compose.
    rewrite nat_trans_commute.
    rewrite functor_compose.
    rewrite <- cat_assoc.
    rewrite nat_trans_commute.
    reflexivity.
Qed.

Notation "α □ β" := (vcompose_nat_transformation α β) (at level 20, left associativity).
Notation "α ⊡ β" := (hcompose_nat_transformation α β) (at level 20, left associativity).

Global Remove Hints id_nat_transformation vcompose_nat_transformation hcompose_nat_transformation : typeclass_instances.

Theorem nat_trans_compose_eq `{C1 : Category, C2 : Category}
        `{F : @Functor C1 C2, G : @Functor C1 C2, H : @Functor C1 C2} :
        ∀ (α : NatTransformation G H) (β : NatTransformation F G),
        ∀ A, (α □ β) • A = α • A ∘ β • A.
    intros α β A.
    cbn.
    reflexivity.
Qed.

Theorem nat_trans_eq `{C1 : Category, C2 : Category}
        `{F : @Functor C1 C2, G : @Functor C1 C2} :
        ∀ (α β : NatTransformation F G), (∀ A, α • A = β • A) → α = β.
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

Theorem nat_trans_interchange `{C1 : Category, C2 : Category, C3 : Category}
        `{F  : @Functor C1 C2, G  : @Functor C1 C2, H  : @Functor C1 C2}
        `{F' : @Functor C2 C3, G' : @Functor C2 C3, H' : @Functor C2 C3} :
        ∀ (α  : NatTransformation F  G ) (β  : NatTransformation G  H)
          (α' : NatTransformation F' G') (β' : NatTransformation G' H'),
        (β' □ α') ⊡ (β □ α) = (β' ⊡ β) □ (α' ⊡ α).
    intros α β α' β'.
    apply nat_trans_eq.
    intros A.
    cbn.
    do 2 rewrite <- cat_assoc.
    apply lcompose.
    rewrite functor_compose.
    do 2 rewrite cat_assoc.
    apply rcompose.
    apply nat_trans_commute.
Qed.

Theorem nat_trans_id_interchange `{C1 : Category, C2 : Category, C3 : Category}
        `{F : @Functor C2 C3, G : @Functor C1 C2} :
        (id_nat_transformation F) ⊡ (id_nat_transformation G) =
        id_nat_transformation (F ○ G).
    apply nat_trans_eq.
    intros A.
    cbn.
    rewrite cat_lid.
    apply functor_id.
Qed.

Theorem nat_trans_lid `{C1 : Category, C2 : Category}
        `{F : @Functor C1 C2, G : @Functor C1 C2} :
        ∀ (α : NatTransformation F G), 𝕀 □ α = α.
    intros α.
    apply nat_trans_eq.
    intros A.
    cbn.
    apply cat_lid.
Qed.
Theorem nat_trans_rid `{C1 : Category, C2 : Category}
        `{F : @Functor C1 C2, G : @Functor C1 C2} :
        ∀ (α : NatTransformation F G), α □ 𝕀 = α.
    intros α.
    apply nat_trans_eq.
    intros A.
    cbn.
    apply cat_rid.
Qed.
Theorem nat_trans_assoc `{C1 : Category, C2 : Category}
        `{F : @Functor C1 C2, G : @Functor C1 C2,
          H : @Functor C1 C2, I : @Functor C1 C2} :
        ∀ (α : NatTransformation H I)
          (β : NatTransformation G H)
          (γ : NatTransformation F G),
          α □ (β □ γ) = (α □ β) □ γ.
    intros α β γ.
    apply nat_trans_eq.
    intros A.
    cbn.
    apply cat_assoc.
Qed.

Program Instance FUNCTOR `(C1 : Category, C2 : Category) : Category := {
    cat_U := Functor C1 C2;
    cat_morphism F G := NatTransformation F G;
    cat_compose {A B C} α β := α □ β;
    cat_id F := id_nat_transformation F;
}.
Next Obligation.
    apply nat_trans_assoc.
Qed.
Next Obligation.
    apply nat_trans_lid.
Qed.
Next Obligation.
    apply nat_trans_rid.
Qed.

Global Remove Hints FUNCTOR : typeclass_instances.

Definition nat_isomorphism `{C1 : Category, C2 : Category}
    `{F : @Functor C1 C2, G : @Functor C1 C2} `(α : @NatTransformation C1 C2 F G)
    := isomorphism (C0 := FUNCTOR C1 C2) α.

Theorem nat_isomorphism_A `{C1 : Category, C2 : Category}
        `{F : @Functor C1 C2, G : @Functor C1 C2} : ∀ α : NatTransformation F G,
        nat_isomorphism α ↔ (∀ A, isomorphism (α • A)).
    intros α.
    split.
    -   intros α_iso A.
        destruct α_iso as [β [β_eq1 β_eq2]].
        cbn in *.
        exists (β • A).
        do 2 rewrite <- nat_trans_compose_eq.
        rewrite β_eq1, β_eq2.
        cbn.
        split; reflexivity.
    -   intros all_iso.
        pose (β_f A := ex_val (all_iso A)).
        assert (∀ {A B} (f : cat_morphism C1 A B),
            β_f B ∘ (G ⋄ f) = (F ⋄ f) ∘ β_f A) as β_commute.
        {
            intros A B f.
            unfold β_f.
            rewrite_ex_val A' [A'_eq1 A'_eq2].
            rewrite_ex_val B' [B'_eq1 B'_eq2].
            apply rcompose with (F ⋄ f) in A'_eq2.
            rewrite cat_lid in A'_eq2.
            rewrite <- cat_assoc in A'_eq2.
            rewrite nat_trans_commute in A'_eq2.
            apply rcompose with B' in A'_eq2.
            do 2 rewrite <- cat_assoc in A'_eq2.
            rewrite B'_eq1 in A'_eq2.
            rewrite cat_rid in A'_eq2.
            exact A'_eq2.
        }
        pose (β := {|nat_trans_commute := β_commute|}).
        exists β.
        cbn.
        split.
        +   apply nat_trans_eq.
            intros A.
            cbn.
            unfold β_f.
            rewrite_ex_val B [B_eq1 B_eq2].
            exact B_eq1.
        +   apply nat_trans_eq.
            intros A.
            cbn.
            unfold β_f.
            rewrite_ex_val B [B_eq1 B_eq2].
            exact B_eq2.
Qed.

Definition nat_isomorphic `{C1 : Category, C2 : Category}
    `(F : @Functor C1 C2, G : @Functor C1 C2)
    := ∃ α : @NatTransformation C1 C2 F G, nat_isomorphism α.

Definition cat_equivalence `{C1 : Category, C2 : Category}
    `(F : @Functor C1 C2, G : @Functor C2 C1)
    `(η : @NatTransformation C1 C1 𝟏 (G ○ F))
    `(ε : @NatTransformation C2 C2 (F ○ G) 𝟏)
    := nat_isomorphism η ∧ nat_isomorphism ε.

Definition cat_equivalent `(C1 : Category, C2 : Category)
    := ∃ (F : @Functor C1 C2) (G : @Functor C2 C1) η ε,
        cat_equivalence F G η ε.

Notation "A ⋍ B" := (cat_equivalent A B) (at level 70, no associativity).

Theorem cat_equiv_refl : ∀ `(C0 : Category), C0 ⋍ C0.
    intros C0.
    exists 𝟏, 𝟏.
    unfold cat_equivalence.
    rewrite functor_lid.
    exists 𝕀, 𝕀.
    assert (nat_isomorphism (F:=𝟏) (G:=𝟏) 𝕀) as H.
    {
        exists 𝕀.
        cbn.
        rewrite nat_trans_lid.
        split; reflexivity.
    }
    split; exact H.
Qed.

Section FunctorEquivalence1.

Context `{C1 : Category, C2 : Category}.
Context `(F : @Functor C1 C2, G : @Functor C2 C1).
Context `(η : @NatTransformation C1 C1 𝟏 (G ○ F)).
Context `(ε : @NatTransformation C2 C2 (F ○ G) 𝟏).
Hypothesis equiv : cat_equivalence F G η ε.

Theorem cat_equiv_sym_base : ∃ η' ε', cat_equivalence G F η' ε'.
    destruct equiv as [η_iso ε_iso].
    rewrite nat_isomorphism_A in η_iso.
    rewrite nat_isomorphism_A in ε_iso.
    pose (η'_f A := ex_val (ε_iso A)).
    assert (∀ {A B} f, η'_f B ∘ (𝟏 ⋄ f) = (F ○ G ⋄ f) ∘ η'_f A) as η'_commute.
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
    assert (∀ {A B} f, ε'_f B ∘ (G ○ F ⋄ f) = (𝟏 ⋄ f) ∘ ε'_f A) as ε'_commute.
    {
        intros A B f.
        unfold ε'_f.
        rewrite_ex_val B' [B'_eq1 B'_eq2].
        rewrite_ex_val A' [A'_eq1 A'_eq2].
        cbn.
        pose proof (nat_trans_commute η f) as eq.
        cbn in *.
        apply rcompose with A' in eq.
        rewrite <- (cat_assoc _ (η • A) A') in eq.
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
    split; rewrite nat_isomorphism_A.
    -   intros A.
        cbn.
        unfold η'_f.
        unfold ex_val.
        destruct (ex_to_type _) as [B [B_eq1 B_eq2]]; cbn.
        exists (ε • A).
        split; assumption.
    -   intros A.
        cbn.
        unfold ε'_f.
        unfold ex_val.
        destruct (ex_to_type _) as [B [B_eq1 B_eq2]]; cbn.
        exists (η • A).
        split; assumption.
Qed.

Theorem functor_equiv_faithful1 : faithful_functor F.
    intros A B f g eq.
    apply (f_equal (functor_morphism G)) in eq.
    pose proof (nat_trans_commute η f) as eq2.
    pose proof (nat_trans_commute η g) as eq3.
    cbn in *.
    rewrite eq in eq2; clear eq.
    rewrite <- eq3 in eq2; clear eq3.
    destruct equiv as [η_iso ε_iso].
    rewrite nat_isomorphism_A in η_iso.
    rewrite nat_isomorphism_A in ε_iso.
    pose proof (η_iso B) as [h [h_eq1 h_eq2]].
    cbn in *.
    apply lcompose with h in eq2.
    do 2 rewrite cat_assoc in eq2.
    rewrite h_eq2 in eq2.
    do 2 rewrite cat_lid in eq2.
    exact eq2.
Qed.

Theorem functor_equiv_sur1 : essentially_surjective F.
    intros B.
    exists (G ⌈B⌉).
    exists (ε • B).
    destruct equiv as [η_iso ε_iso].
    rewrite nat_isomorphism_A in ε_iso.
    apply ε_iso.
Qed.

End FunctorEquivalence1.

Theorem cat_equiv_sym : ∀ C1 C2, cat_equivalent C1 C2 → cat_equivalent C2 C1.
    intros C1 C2 [F [G [η [ε equiv]]]].
    pose proof (cat_equiv_sym_base F G η ε equiv) as [η' [ε' equiv']].
    exists G, F, η', ε'.
    exact equiv'.
Qed.

Section FunctorEquivalence2.

Context `{C1 : Category, C2 : Category}.
Context `(F : @Functor C1 C2, G : @Functor C2 C1).
Context `(η : @NatTransformation C1 C1 𝟏 (G ○ F)).
Context `(ε : @NatTransformation C2 C2 (F ○ G) 𝟏).
Hypothesis equiv : cat_equivalence F G η ε.

Theorem functor_equiv_faithful2 : faithful_functor G.
    pose proof (cat_equiv_sym_base F G η ε equiv) as [η' [ε' equiv']].
    apply (functor_equiv_faithful1 G F η' ε' equiv').
Qed.

Theorem functor_equiv_sur2 : essentially_surjective G.
    pose proof (cat_equiv_sym_base F G η ε equiv) as [η' [ε' equiv']].
    apply (functor_equiv_sur1 G F η' ε' equiv').
Qed.

Theorem functor_equiv_full1 : full_functor F.
    intros A B f.
    destruct equiv as [η_iso ε_iso].
    rewrite nat_isomorphism_A in η_iso.
    rewrite nat_isomorphism_A in ε_iso.
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

End FunctorEquivalence2.
Section FunctorEquivalence3.

Context `{C1 : Category, C2 : Category}.
Context `(F : @Functor C1 C2, G : @Functor C2 C1).
Context `(η : @NatTransformation C1 C1 𝟏 (G ○ F)).
Context `(ε : @NatTransformation C2 C2 (F ○ G) 𝟏).
Hypothesis equiv : cat_equivalence F G η ε.

Theorem functor_equiv_full2 : full_functor G.
    pose proof (cat_equiv_sym_base F G η ε equiv) as [η' [ε' equiv']].
    apply (functor_equiv_full1 G F η' ε' equiv').
Qed.

End FunctorEquivalence3.

Theorem functor_equivalence `{C1 : Category, C2 : Category} :
        ∀ `(F : @Functor C1 C2),
        full_functor F → faithful_functor F → essentially_surjective F →
        cat_equivalent C1 C2.
    intros F F_full F_faith F_sur.
    exists F.
    pose (G_f B := ex_val (F_sur B)).
    pose (g B := ex_val (ex_proof (ex_proof (F_sur B)))).
    pose (h A := ex_val (ex_proof (F_sur A))).
    pose (G_morphism A B (f : cat_morphism C2 A B) :=
        ex_val (F_full _ _ (g B ∘ f ∘ h A))
    ).
    assert (∀ A, g A ∘ h A = 𝟙) as gh_id.
    {
        intros A.
        unfold g, h.
        unfold ex_val, ex_proof.
        destruct (ex_to_type (F_sur A)) as [GA CC0]; cbn.
        destruct (ex_to_type CC0) as [f CC1]; cbn; clear CC0.
        destruct (ex_to_type CC1) as [f' [f_eq1 f_eq2]]; cbn; clear CC1.
        exact f_eq2.
    }
    assert (∀ A, h A ∘ g A = 𝟙) as hg_id.
    {
        intros A.
        unfold g, h.
        unfold ex_val, ex_proof.
        destruct (ex_to_type (F_sur A)) as [GA CC0]; cbn.
        destruct (ex_to_type CC0) as [f CC1]; cbn; clear CC0.
        destruct (ex_to_type CC1) as [f' [f_eq1 f_eq2]]; cbn; clear CC1.
        exact f_eq1.
    }
    assert (∀ {A B C} (f : cat_morphism C2 B C) (g : cat_morphism C2 A B),
        G_morphism _ _ (f ∘ g) = G_morphism _ _ f ∘ G_morphism _ _ g)
        as G_compose.
    {
        intros A B C f1 f2.
        unfold G_morphism.
        change (ex_type_val (ex_to_type (F_sur A))) with (G_f A).
        change (ex_type_val (ex_to_type (F_sur B))) with (G_f B).
        change (ex_type_val (ex_to_type (F_sur C))) with (G_f C).
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
    assert (∀ A, G_morphism _ _ (cat_id _ A) = 𝟙) as G_id.
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
    |}).
    pose (η_f A := ex_val (F_full _ _ (g (F ⌈A⌉)))
        : cat_morphism C1 (𝟏 ⌈A⌉) (G ○ F ⌈A⌉)).
    assert (∀ {A B} (f : cat_morphism C1 A B),
        η_f B ∘ (𝟏 ⋄ f) = (G ○ F ⋄ f) ∘ η_f A) as η_commute.
    {
        intros A B f0.
        cbn.
        unfold G_morphism.
        change (ex_type_val (ex_to_type (F_sur (F ⌈A⌉)))) with (G_f (F ⌈A⌉)).
        change (ex_type_val (ex_to_type (F_sur (F ⌈B⌉)))) with (G_f (F ⌈B⌉)).
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
    assert (∀ {A B} (f : cat_morphism C2 A B),
        h B ∘ (F ○ G ⋄ f) = (𝟏 ⋄ f) ∘ h A) as ε_commute.
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
    pose (ε_f B := h B : cat_morphism C2 (F ○ G ⌈B⌉) (𝟏 ⌈B⌉)).
    pose (η := {|nat_trans_f := η_f; nat_trans_commute := η_commute|}).
    pose (ε := {|nat_trans_f := ε_f; nat_trans_commute := ε_commute|}).
    exists G, η, ε.
    split; rewrite nat_isomorphism_A.
    -   intros A.
        unfold isomorphism.
        exists (ex_val (F_full _ _ (h (F ⌈A⌉)))).
        cbn.
        unfold η_f.
        change (ex_type_val (ex_to_type (F_sur (F ⌈A⌉)))) with (G ⌈F ⌈A⌉⌉).
        rewrite_ex_val f1 f1_eq.
        rewrite_ex_val f2 f2_eq.
        split.
        +   pose proof (lrcompose f1_eq f2_eq) as eq.
            rewrite <- functor_compose in eq.
            specialize (gh_id (F ⌈A⌉)).
            cbn in *.
            change (ex_type_val (ex_to_type (F_sur (F ⌈A⌉)))) with (G_f (F ⌈A⌉)) in *.
            rewrite gh_id in eq.
            rewrite <- functor_id in eq.
            apply F_faith in eq.
            exact eq.
        +   pose proof (lrcompose f2_eq f1_eq) as eq.
            rewrite <- functor_compose in eq.
            specialize (hg_id (F ⌈A⌉)).
            cbn in *.
            change (ex_type_val (ex_to_type (F_sur (F ⌈A⌉)))) with (G_f (F ⌈A⌉)) in *.
            rewrite hg_id in eq.
            rewrite <- functor_id in eq.
            apply F_faith in eq.
            exact eq.
    -   intros A.
        unfold isomorphism.
        exists (g A).
        cbn.
        unfold ε_f.
        split.
        +   apply hg_id.
        +   apply gh_id.
Qed.
