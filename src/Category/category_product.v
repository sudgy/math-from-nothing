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
    := obj_π1 a = obj_π1 b ∘ h ∧ obj_π2 a = obj_π2 b ∘ h.

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
        rewrite <- f1.
        exact g1.
    -   rewrite cat_assoc.
        rewrite <- f2.
        exact g2.
Qed.

Lemma product_id_in : ∀ f : product_base, product_set f f 𝟙.
Proof.
    intros f.
    split; symmetry; apply cat_rid.
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

Arguments obj_π1 {C A B}.
Arguments obj_π2 {C A B}.

Class HasProducts (C : Category) := {
    product (A B : C) : ProductCat A B;
    product_term : ∀ A B, terminal (product A B);
    π1 (A B : C) := obj_π1 (product A B);
    π2 (A B : C) := obj_π2 (product A B);
}.

Class HasCoproducts (C : Category) := {
    coproduct (A B : C) : ProductCat (C := dual_category C) A B;
    coproduct_init : ∀ A B, terminal (coproduct A B);
    ι1 (A B : C) := obj_π1 (coproduct A B);
    ι2 (A B : C) := obj_π2 (coproduct A B);
}.

Unset Universe Polymorphism.
