Require Import init.

Require Export category_def.
Require Export category_initterm.

Require Import set.

Set Universe Polymorphism.

Section Product.

Context {C : Category} (A B : C).

Record product_base := make_product_obj {
    product_obj :> C;
    obj_π1 : morphism product_obj A;
    obj_π2 : morphism product_obj B;
}.

Definition product_set (a b : product_base) (h : morphism a b)
    := obj_π1 b ∘ h = obj_π1 a ∧ obj_π2 b ∘ h = obj_π2 a.

Definition product_compose {a b c : product_base}
    (f : set_type (product_set b c)) (g : set_type (product_set a b))
    := [f|] ∘ [g|].

Lemma product_compose_in {a b c : product_base} :
    ∀ (f : set_type (product_set b c)) g, product_set a c (product_compose f g).
Proof.
    intros [f [f1 f2]] [g [g1 g2]].
    unfold product_compose; cbn.
    split.
    -   rewrite cat_assoc.
        rewrite f1.
        exact g1.
    -   rewrite cat_assoc.
        rewrite f2.
        exact g2.
Qed.

Lemma product_id_in : ∀ f : product_base, product_set f f 𝟙.
Proof.
    intros f.
    split; apply cat_rid.
Qed.

Program Definition ProductCat : Category := {|
    cat_U := product_base;
    morphism f g := set_type (product_set f g);
    cat_compose F G H f g := [_|product_compose_in f g];
    cat_id f := [_|product_id_in f];
|}.
Next Obligation.
    unfold product_compose.
    apply set_type_eq; cbn.
    apply cat_assoc.
Qed.
Next Obligation.
    unfold product_compose.
    apply set_type_eq; cbn.
    apply cat_lid.
Qed.
Next Obligation.
    unfold product_compose.
    apply set_type_eq; cbn.
    apply cat_rid.
Qed.

End Product.

Arguments product_obj {C A B}.
Arguments obj_π1 {C A B}.
Arguments obj_π2 {C A B}.

Class HasProducts (C : Category) := {
    product (A B : C) : ProductCat A B;
    product_term : ∀ A B, terminal (product A B);
    π1 (A B : C) := obj_π1 (product A B);
    π2 (A B : C) := obj_π2 (product A B);
}.

Notation "A ∏ B" := (product_obj (product A B)).

Class HasCoproducts (C : Category) := {
    coproduct (A B : C) : ProductCat (C := dual_category C) A B;
    coproduct_init : ∀ A B, terminal (coproduct A B);
    ι1 (A B : C) := obj_π1 (coproduct A B);
    ι2 (A B : C) := obj_π2 (coproduct A B);
}.

Section Product.

Context {C : Category} `{HasProducts C}.

Context (A B : C).
Context (P : ProductCat A B).

Definition product_f := [ex_singleton (product_term A B P)|].

Theorem product_f1 : π1 A B ∘ product_f = obj_π1 P.
Proof.
    apply [|ex_singleton (product_term A B P)].
Qed.

Theorem product_f2 : π2 A B ∘ product_f = obj_π2 P.
Proof.
    apply [|ex_singleton (product_term A B P)].
Qed.

Theorem product_f_uni : ∀ f,
    π1 A B ∘ f = obj_π1 P → π2 A B ∘ f = obj_π2 P → f = product_f.
Proof.
    intros f eq1 eq2.
    pose proof (product_term A B P) as S.
    cbn in S.
    assert (product_set A B P (product A B) f) as f_in by (split; assumption).
    pose proof [|ex_singleton (product_term A B P)] as f_in'.
    pose proof (singleton_unique2 [_|f_in] [_|f_in']) as eq.
    rewrite set_type_eq2 in eq.
    exact eq.
Qed.

Theorem product_f_uni2 : ∀ f g,
    π1 A B ∘ f = obj_π1 P → π2 A B ∘ f = obj_π2 P →
    π1 A B ∘ g = obj_π1 P → π2 A B ∘ g = obj_π2 P →
    f = g.
Proof.
    intros f g f_eq1 f_eq2 g_eq1 g_eq2.
    rewrite (product_f_uni f f_eq1 f_eq2).
    symmetry; exact (product_f_uni g g_eq1 g_eq2).
Qed.

End Product.

Arguments product_f {C H A B}.
Arguments product_f1 {C H A B}.
Arguments product_f2 {C H A B}.
Arguments product_f_uni {C H A B}.
Arguments product_f_uni2 {C H A B}.

Section ProductComm.

Context {C : Category} `{HasProducts C}.

Context (A B : C).

Theorem product_mono : ∀ Z : C, ∀ f g : morphism Z (A ∏ B),
    π1 A B ∘ f = π1 A B ∘ g → π2 A B ∘ f = π2 A B ∘ g → f = g.
Proof.
    intros Z f g eq1 eq2.
    pose (ZP := make_product_obj A B Z (π1 A B ∘ f) (π2 A B ∘ f)).
    apply (product_f_uni2 ZP).
    3: rewrite <- eq1.
    4: rewrite <- eq2.
    all: reflexivity.
Qed.

Let BA := make_product_obj A B (B ∏ A) (π2 B A) (π1 B A) : ProductCat A B.

Lemma product_comm_term : terminal BA.
Proof.
    intros [P p1 p2].
    pose (P' := make_product_obj B A P p2 p1).
    cbn in *.
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        exists (product_f P').
        split; cbn.
        +   apply (product_f2 P').
        +   apply (product_f1 P').
    -   intros [a [a_in1 a_in2]] [b [b_in1 b_in2]].
        rewrite set_type_eq2.
        apply (product_f_uni2 P'); assumption.
Qed.

Definition product_comm_f :=
    [iso_f (terminal_unique _ _ (product_term A B) product_comm_term)|]
    : morphism (A ∏ B) (B ∏ A).

Definition product_comm_g :=
    [iso_g (terminal_unique _ _ (product_term A B) product_comm_term)|]
    : morphism (B ∏ A) (A ∏ B).

Let f := product_comm_f.
Let g := product_comm_g.

Theorem product_comm_iso : is_isomorphism_pair f g.
Proof.
    unfold f, g, product_comm_f, product_comm_g.
    destruct (terminal_unique _ _ _ _) as [f' g' [fg gf]]; cbn.
    apply set_type_eq in fg, gf.
    split; assumption.
Qed.

Theorem product_comm : A ∏ B ≅ B ∏ A.
Proof.
    exists f g.
    exact product_comm_iso.
Qed.

Theorem product_comm_f1 : π2 B A ∘ f = π1 A B.
Proof.
    unfold f, product_comm_f.
    apply [|iso_f (terminal_unique _ BA _ _)].
Qed.
Theorem product_comm_f2 : π1 B A ∘ f = π2 A B.
Proof.
    unfold f, product_comm_f.
    apply [|iso_f (terminal_unique _ BA _ _)].
Qed.
Theorem product_comm_g1 : π2 A B ∘ g = π1 B A.
Proof.
    unfold g, product_comm_g.
    apply [|iso_g (terminal_unique _ BA _ _)].
Qed.
Theorem product_comm_g2 : π1 A B ∘ g = π2 B A.
Proof.
    unfold g, product_comm_g.
    apply [|iso_g (terminal_unique _ BA _ _)].
Qed.

End ProductComm.
Section ProductAssoc.

Context {C0 : Category} `{HasProducts C0}.

Context (A B C : C0).

Let π1' := π1 A B ∘ π1 (A ∏ B) C.
Let π2' := π2 A B ∘ π1 (A ∏ B) C.
Let π3' := π2 (A ∏ B) C.

Let ABC_BC := make_product_obj B C ((A ∏ B) ∏ C) π2' π3' : ProductCat B C.

Let π23' := product_f ABC_BC.

Let ABC := make_product_obj A (B ∏ C) ((A ∏ B) ∏ C) π1' π23'
    : ProductCat A (B ∏ C).

Lemma product_assoc_term : terminal ABC.
Proof.
    intros [P p1 p23].
    pose (p2 := π1 B C ∘ p23).
    pose (p3 := π2 B C ∘ p23).
    pose (P12 := make_product_obj A B P p1 p2).
    pose (f := product_f P12).
    pose (P' := make_product_obj _ _ P f p3).
    pose (g := product_f P').
    cbn.
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        unfold product_set; cbn.
        exists g.
        unfold π1'.
        split.
        +   rewrite <- cat_assoc.
            rewrite (product_f1 P').
            exact (product_f1 P12).
        +   (*unfold p2 in f_in2.
            unfold p3 in g_in2.*)
            apply product_mono.
            *   rewrite cat_assoc.
                rewrite (product_f1 ABC_BC); cbn.
                unfold π2'.
                rewrite <- cat_assoc.
                rewrite (product_f1 P').
                exact (product_f2 P12).
            *   rewrite cat_assoc.
                rewrite (product_f2 ABC_BC).
                rewrite (product_f2 P').
                reflexivity.
    -   intros [a a_in] [b b_in].
        assert (∀ c,
            product_set _ _ (make_product_obj _ _ P p1 p23) ABC c →
            product_set _ _ (make_product_obj _ _ P f p3) ((A ∏ B) ∏ C) c)
            as in_wlog.
        {
            intros c.
            unfold product_set; cbn.
            unfold π1'.
            intros [c_in1 c_in2].
            change (obj_π1 _) with (π1 (A ∏ B) C).
            change (obj_π2 _) with (π2 (A ∏ B) C).
            split.
            -   apply product_mono.
                +   rewrite cat_assoc.
                    rewrite c_in1.
                    symmetry; apply (product_f1 P12).
                +   rewrite cat_assoc.
                    pose proof (product_f1 ABC_BC) as eq.
                    cbn in eq.
                    unfold π2' in eq.
                    rewrite <- eq.
                    rewrite (product_f2 P12).
                    rewrite <- cat_assoc.
                    rewrite c_in2.
                    reflexivity.
            -   unfold p3.
                rewrite <- c_in2.
                rewrite cat_assoc.
                rewrite (product_f2 ABC_BC).
                reflexivity.
        }
        rewrite set_type_eq2.
        apply in_wlog in a_in, b_in.
        apply (product_f_uni2 (make_product_obj _ _ P f p3)).
        1, 2: apply a_in.
        1, 2: apply b_in.
Qed.

Definition product_assoc_f :=
    [iso_f (terminal_unique _ _ (product_term A (B ∏ C)) product_assoc_term)|]
    : morphism (A ∏ (B ∏ C)) ((A ∏ B) ∏ C).

Definition product_assoc_g :=
    [iso_g (terminal_unique _ _ (product_term A (B ∏ C)) product_assoc_term)|]
    : morphism ((A ∏ B) ∏ C) (A ∏ (B ∏ C)).

Let f := product_assoc_f.
Let g := product_assoc_g.

Theorem product_assoc_iso : is_isomorphism_pair f g.
Proof.
    unfold f, g, product_assoc_f, product_assoc_g.
    destruct (terminal_unique _ _ _ _) as [f' g' [fg gf]]; cbn.
    apply set_type_eq in fg, gf.
    split; assumption.
Qed.

Theorem product_assoc : A ∏ (B ∏ C) ≅ (A ∏ B) ∏ C.
Proof.
    exists f g.
    exact product_assoc_iso.
Qed.

Theorem product_assoc_f1 : π1 A (B ∏ C) = π1 A B ∘ π1 (A ∏ B) C ∘ f.
Proof.
    unfold f, product_assoc_f.
    symmetry; apply [|iso_f (terminal_unique _ ABC _ _)].
Qed.
Theorem product_assoc_f2 : π1 B C ∘ π2 A (B ∏ C) = π2 A B ∘ π1 (A ∏ B) C ∘ f.
Proof.
    pose proof [|iso_f (terminal_unique _ ABC (product_term A (B ∏ C))
        product_assoc_term)] as eq.
    unfold product_set in eq; cbn in eq.
    change [_|] with f in eq.
    change [_|] with f.
    change (obj_π1 _) with (π1 A (B ∏ C)) in eq.
    change (obj_π2 _) with (π2 A (B ∏ C)) in eq.
    rewrite <- (rand eq).
    pose proof (product_f1 ABC_BC) as eq'.
    cbn in eq'.
    unfold π2' in eq'.
    rewrite <- eq'.
    apply cat_assoc.
Qed.
Theorem product_assoc_f3 : π2 B C ∘ π2 A (B ∏ C) = π2 (A ∏ B) C ∘ f.
Proof.
    pose proof [|iso_f (terminal_unique _ ABC (product_term A (B ∏ C))
        product_assoc_term)] as eq.
    unfold product_set in eq; cbn in eq.
    change [_|] with f in eq.
    change (obj_π1 _) with (π1 A (B ∏ C)) in eq.
    change (obj_π2 _) with (π2 A (B ∏ C)) in eq.
    rewrite <- (rand eq).
    pose proof (product_f2 ABC_BC) as eq'.
    cbn in eq'.
    unfold π3' in eq'.
    rewrite <- eq'.
    apply cat_assoc.
Qed.
Theorem product_assoc_g1 : π1 A B ∘ π1 (A ∏ B) C = π1 A (B ∏ C) ∘ g.
Proof.
    pose proof product_assoc_iso as fg.
    pose proof (is_isomorphism_pair_left _ _ fg) as f_iso.
    apply isomorphism_epimorphism in f_iso.
    apply f_iso.
    rewrite <- (cat_assoc _ g).
    rewrite (rand fg), cat_rid.
    symmetry; apply product_assoc_f1.
Qed.
Theorem product_assoc_g2 : π2 A B ∘ π1 (A ∏ B) C = π1 B C ∘ π2 A (B ∏ C) ∘ g.
Proof.
    pose proof product_assoc_iso as fg.
    pose proof (is_isomorphism_pair_left _ _ fg) as f_iso.
    apply isomorphism_epimorphism in f_iso.
    apply f_iso.
    rewrite <- (cat_assoc _ g).
    rewrite (rand fg), cat_rid.
    symmetry; apply product_assoc_f2.
Qed.
Theorem product_assoc_g3 : π2 (A ∏ B) C = π2 B C ∘ π2 A (B ∏ C) ∘ g.
Proof.
    pose proof product_assoc_iso as fg.
    pose proof (is_isomorphism_pair_left _ _ fg) as f_iso.
    apply isomorphism_epimorphism in f_iso.
    apply f_iso.
    rewrite <- (cat_assoc _ g).
    rewrite (rand fg), cat_rid.
    symmetry; apply product_assoc_f3.
Qed.

End ProductAssoc.

Unset Universe Polymorphism.
