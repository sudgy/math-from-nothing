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
    := isomorphic (C0 := FUNCTOR C1 C2) F G.

Theorem nat_isomorphic_wd `{C1 : Category, C2 : Category, C3 : Category} :
        ∀ (F G : Functor C2 C3) (H I : Functor C1 C2),
        nat_isomorphic F G → nat_isomorphic H I →
        nat_isomorphic (F ○ H) (G ○ I).
    intros F G H I [α [α' [α_eq1 α_eq2]]] [β [β' [β_eq1 β_eq2]]].
    cbn in *.
    exists (α ⊡ β).
    exists (α' ⊡ β').
    cbn.
    split.
    -   rewrite <- nat_trans_interchange.
        rewrite α_eq1, β_eq1.
        apply nat_trans_id_interchange.
    -   rewrite <- nat_trans_interchange.
        rewrite α_eq2, β_eq2.
        apply nat_trans_id_interchange.
Qed.

Theorem lnat_iso `{C1 : Category, C2 : Category, C3 : Category} :
        ∀ {F G : Functor C1 C2} (H : Functor C2 C3),
        isomorphic (C0 := FUNCTOR C1 C2) F G →
        isomorphic (C0 := FUNCTOR C1 C3) (H ○ F) (H ○ G).
    intros F G H eq.
    pose proof (isomorphic_refl (C0:= FUNCTOR C2 C3) H) as eq2.
    exact (nat_isomorphic_wd _ _ _ _ eq2 eq).
Qed.
Theorem rnat_iso `{C1 : Category, C2 : Category, C3 : Category} :
        ∀ {F G : Functor C2 C3} (H : Functor C1 C2),
        isomorphic (C0 := FUNCTOR C2 C3) F G →
        isomorphic (C0 := FUNCTOR C1 C3) (F ○ H) (G ○ H).
    intros F G H eq.
    pose proof (isomorphic_refl (C0:= FUNCTOR C1 C2) H) as eq2.
    exact (nat_isomorphic_wd _ _ _ _ eq eq2).
Qed.
