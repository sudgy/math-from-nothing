Require Import init.

Require Export category_functor.

Program Definition hcompose_nat_transformation
    {C1 C2 C3 : Category} {F2 G2 : Functor C2 C3} {F1 G1 : Functor C1 C2}
    (β : NatTransformation F2 G2) (α : NatTransformation F1 G1)
    : NatTransformation (F2 ∘ F1) (G2 ∘ G1) :=
{|
    nat_trans_f A := β (G1 A) ∘ (⌈F2⌉ (α A))
|}.
Next Obligation.
    rewrite <- cat_assoc.
    rewrite <- functor_compose.
    do 3 rewrite nat_trans_commute.
    rewrite cat_assoc.
    rewrite <- functor_compose.
    reflexivity.
Qed.

Notation "α ○ β" := (hcompose_nat_transformation α β)
    (at level 20, left associativity).

Theorem nat_trans_interchange {C1 C2 C3 : Category}
    {F1 G1 H1 : Functor C1 C2}
    {F2 G2 H2 : Functor C2 C3} :
    ∀ (α1 : NatTransformation F1 G1) (β1 : NatTransformation G1 H1)
      (α2 : NatTransformation F2 G2) (β2 : NatTransformation G2 H2),
    (β2 ∘ α2) ○ (β1 ∘ α1) = (β2 ○ β1) ∘ (α2 ○ α1).
Proof.
    intros α1 β1 α2 β2.
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

Theorem nat_trans_hid {C1 C2 C3 : Category}
    {F : Functor C2 C3} {G : Functor C1 C2} :
    𝟙 ○ 𝟙 = (𝟙 : NatTransformation (F ∘ G) (F ∘ G)).
Proof.
    apply nat_trans_eq.
    intros A.
    cbn.
    rewrite cat_lid.
    apply functor_id.
Qed.

Theorem nat_isomorphism_components {C1 C2 : Category} {F G : Functor C1 C2} :
    ∀ α : NatTransformation F G,
    is_isomorphism α ↔ (∀ A, is_isomorphism (α A)).
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
        pose (β := make_nat_trans _ _ (λ A, ex_val (all_iso A))).
        prove_parts β.
        {
            intros A B f.
            cbn.
            rewrite_ex_val B' [B'_eq1 B'_eq2].
            rewrite_ex_val A' [A'_eq1 A'_eq2].
            rewrite <- (cat_lid (⌈F⌉ f)).
            rewrite <- B'_eq2.
            rewrite <- (cat_assoc B').
            rewrite nat_trans_commute.
            do 2 rewrite <- cat_assoc.
            rewrite A'_eq1, cat_rid.
            reflexivity.
        }
        exists β.
        split.
        +   apply nat_trans_eq; cbn.
            intros A.
            rewrite_ex_val B [B_eq1 B_eq2].
            exact B_eq1.
        +   apply nat_trans_eq; cbn.
            intros A.
            rewrite_ex_val B [B_eq1 B_eq2].
            exact B_eq2.
Qed.

Theorem nat_isomorphic_wd {C1 C2 C3 : Category} :
    ∀ {F G : Functor C2 C3} {H I : Functor C1 C2},
    F ≅ G → H ≅ I → (F ∘ H : Functor _ _) ≅ G ∘ I.
Proof.
    intros F G H I [α1 α2 [α12 α21]] [β1 β2 [β12 β21]].
    exists (α1 ○ β1) (α2 ○ β2).
    split.
    -   rewrite <- nat_trans_interchange.
        rewrite α12, β12.
        apply nat_trans_hid.
    -   rewrite <- nat_trans_interchange.
        rewrite α21, β21.
        apply nat_trans_hid.
Qed.

Theorem lnat_iso {C1 C2 C3 : Category} :
    ∀ {F G : Functor C1 C2} (H : Functor C2 C3),
    F ≅ G → (H ∘ F : Functor C1 C3) ≅ (H ∘ G).
Proof.
    intros F G H eq.
    exact (nat_isomorphic_wd (isomorphic_refl H) eq).
Qed.
Theorem rnat_iso {C1 C2 C3 : Category} :
    ∀ {F G : Functor C2 C3} (H : Functor C1 C2),
    F ≅ G → (F ∘ H : Functor C1 C3) ≅ (G ∘ H).
Proof.
    intros F G H eq.
    exact (nat_isomorphic_wd eq (isomorphic_refl H)).
Qed.
