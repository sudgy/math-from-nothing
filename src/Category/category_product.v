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

Arguments product_obj {C A B}.
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

Section ProductComm.

Context {C : Category} `{HasProducts C}.

Local Notation "A × B" := (product_obj (product A B)).

Context (A B : C).

Let BA := make_product_obj A B (B×A) (π2 B A) (π1 B A) : ProductCat A B.

Lemma product_comm_term : terminal BA.
Proof.
    intros [P p1 p2].
    pose proof (product_term B A (make_product_obj B A P p2 p1)) as term.
    cbn in *.
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        apply ex_singleton in term as [f [f_eq1 f_eq2]]; cbn in *.
        exists f.
        split; assumption.
    -   intros [a a_in] [b b_in].
        rewrite set_type_eq2.
        assert (product_set B A (make_product_obj B A P p2 p1)
            (product B A) a) as a_in2.
        {
            destruct a_in as [a_in1 a_in2].
            split; assumption.
        }
        assert (product_set B A (make_product_obj B A P p2 p1)
            (product B A) b) as b_in2.
        {
            destruct b_in as [b_in1 b_in2].
            split; assumption.
        }
        pose proof (singleton_unique2 [a|a_in2] [b|b_in2]) as eq.
        rewrite set_type_eq2 in eq.
        exact eq.
Qed.

Definition product_comm_f :=
    [iso_f (terminal_unique _ _ (product_term A B) product_comm_term)|]
    : morphism (A × B) (B × A).

Definition product_comm_g :=
    [iso_g (terminal_unique _ _ (product_term A B) product_comm_term)|]
    : morphism (B × A) (A × B).

Let f := product_comm_f.
Let g := product_comm_g.

Theorem product_comm_iso : is_isomorphism_pair f g.
Proof.
    unfold f, g, product_comm_f, product_comm_g.
    destruct (terminal_unique _ _ _ _) as [f' g' [fg gf]]; cbn.
    apply set_type_eq in fg, gf.
    split; assumption.
Qed.

Theorem product_comm : A × B ≅ B × A.
Proof.
    exists f g.
    exact product_comm_iso.
Qed.

Theorem product_comm_f1 : π1 A B = π2 B A ∘ f.
Proof.
    unfold f, product_comm_f.
    apply [|iso_f (terminal_unique _ BA _ _)].
Qed.
Theorem product_comm_f2 : π2 A B = π1 B A ∘ f.
Proof.
    unfold f, product_comm_f.
    apply [|iso_f (terminal_unique _ BA _ _)].
Qed.
Theorem product_comm_g1 : π1 B A = π2 A B ∘ g.
Proof.
    unfold g, product_comm_g.
    apply [|iso_g (terminal_unique _ BA _ _)].
Qed.
Theorem product_comm_g2 : π2 B A = π1 A B ∘ g.
Proof.
    unfold g, product_comm_g.
    apply [|iso_g (terminal_unique _ BA _ _)].
Qed.

End ProductComm.

Unset Universe Polymorphism.
