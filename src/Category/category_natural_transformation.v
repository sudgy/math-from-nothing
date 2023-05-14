Require Import init.

Require Export category_functor.

Program Definition hcompose_nat_transformation
    {C1 C2 C3 : Category} {F' G' : Functor C2 C3} {F G : Functor C1 C2}
    (β : NatTransformation F' G') (α : NatTransformation F G)
    : NatTransformation (F' ∘ F) (G' ∘ G) :=
{|
    nat_trans_f A := β (G A) ∘ (⌈F'⌉ (α A))
|}.
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

Notation "α ○ β" := (hcompose_nat_transformation α β) (at level 20, left associativity).

Theorem nat_trans_compose_eq {C1 C2 : Category}
    {F G H : Functor C1 C2} :
    ∀ (α : NatTransformation G H) (β : NatTransformation F G),
    ∀ A, (α ∘ β) A = α A ∘ β A.
Proof.
    intros α β A.
    cbn.
    reflexivity.
Qed.

Theorem nat_trans_interchange {C1 C2 C3 : Category}
    {F  G  H  : Functor C1 C2}
    {F' G' H' : Functor C2 C3} :
    ∀ (α  : NatTransformation F  G ) (β  : NatTransformation G  H)
      (α' : NatTransformation F' G') (β' : NatTransformation G' H'),
    (β' ∘ α') ○ (β ∘ α) = (β' ○ β) ∘ (α' ○ α).
Proof.
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

Theorem nat_trans_id_interchange {C1 C2 C3 : Category}
    {F : Functor C2 C3} {G : Functor C1 C2} :
    (id_nat_transformation F) ○ (id_nat_transformation G) =
    id_nat_transformation (F ∘ G).
Proof.
    apply nat_trans_eq.
    intros A.
    cbn.
    rewrite cat_lid.
    apply functor_id.
Qed.

Definition nat_isomorphism {C1 C2 : Category}
    {F G : Functor C1 C2} (α : NatTransformation F G)
    := is_isomorphism α.

Theorem nat_isomorphism_A {C1 C2 : Category} {F G : Functor C1 C2} :
    ∀ α : NatTransformation F G, nat_isomorphism α ↔ (∀ A, is_isomorphism (α A)).
Proof.
    intros α.
    split.
    -   intros α_iso A.
        destruct α_iso as [β [β_eq1 β_eq2]].
        exists (β A).
        unfold is_isomorphism_pair.
        do 2 rewrite <- nat_trans_compose_eq.
        rewrite β_eq1, β_eq2.
        cbn.
        split; reflexivity.
    -   intros all_iso.
        pose (β_f A := ex_val (all_iso A)).
        assert (∀ {A B} (f : morphism A B),
            β_f B ∘ (⌈G⌉ f) = (⌈F⌉ f) ∘ β_f A) as β_commute.
        {
            intros A B f.
            unfold β_f.
            rewrite_ex_val A' [A'_eq1 A'_eq2].
            rewrite_ex_val B' [B'_eq1 B'_eq2].
            apply rcompose with (⌈F⌉ f) in A'_eq2.
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

Definition nat_isomorphic {C1 C2 : Category} (F G : Functor C1 C2) := F ≅ G.

Theorem nat_isomorphic_wd {C1 C2 C3 : Category} :
    ∀ (F G : Functor C2 C3) (H I : Functor C1 C2),
    nat_isomorphic F G → nat_isomorphic H I →
    nat_isomorphic (F ∘ H) (G ∘ I).
Proof.
    intros F G H I [α α' [α_eq1 α_eq2]] [β β' [β_eq1 β_eq2]].
    exists (α ○ β) (α' ○ β').
    split.
    -   rewrite <- nat_trans_interchange.
        rewrite α_eq1, β_eq1.
        apply nat_trans_id_interchange.
    -   rewrite <- nat_trans_interchange.
        rewrite α_eq2, β_eq2.
        apply nat_trans_id_interchange.
Qed.

Theorem lnat_iso {C1 C2 C3 : Category} :
    ∀ {F G : Functor C1 C2} (H : Functor C2 C3),
    F ≅ G → (H ∘ F : Functor C1 C3) ≅ (H ∘ G).
Proof.
    intros F G H eq.
    pose proof (isomorphic_refl (C0:= Functor C2 C3) H) as eq2.
    exact (nat_isomorphic_wd _ _ _ _ eq2 eq).
Qed.
Theorem rnat_iso {C1 C2 C3 : Category} :
    ∀ {F G : Functor C2 C3} (H : Functor C1 C2),
    F ≅ G → (F ∘ H : Functor C1 C3) ≅ (G ∘ H).
Proof.
    intros F G H eq.
    pose proof (isomorphic_refl (C0:= Functor C1 C2) H) as eq2.
    exact (nat_isomorphic_wd _ _ _ _ eq eq2).
Qed.
