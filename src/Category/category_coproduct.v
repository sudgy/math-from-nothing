Require Import init.

Require Import category_product.

Require Import set.

(** While coproducts could be defined as products in the dual category, and I
even had that as my original definition, I've found that using that definition
can be confusing and it's better to just define it separately and then prove and
use duality in theorems later. *)

Set Universe Polymorphism.

Section Coproduct.

Context {C : Category} (A B : C).

Record coproduct_base := make_coproduct_obj {
    coproduct_obj :> C;
    obj_ι1 : morphism A coproduct_obj;
    obj_ι2 : morphism B coproduct_obj;
}.

Definition coproduct_set (a b : coproduct_base) (h : morphism a b)
    := h ∘ obj_ι1 a = obj_ι1 b ∧ h ∘ obj_ι2 a = obj_ι2 b.

Definition coproduct_compose {a b c : coproduct_base}
    (f : set_type (coproduct_set b c)) (g : set_type (coproduct_set a b))
    := [f|] ∘ [g|].

Lemma coproduct_compose_in {a b c : coproduct_base} :
    ∀ (f : set_type (coproduct_set b c)) g,
    coproduct_set a c (coproduct_compose f g).
Proof.
    intros [f [f1 f2]] [g [g1 g2]].
    unfold coproduct_compose; cbn.
    split.
    -   rewrite <- cat_assoc.
        rewrite g1.
        exact f1.
    -   rewrite <- cat_assoc.
        rewrite g2.
        exact f2.
Qed.

Lemma coproduct_id_in : ∀ f : coproduct_base, coproduct_set f f 𝟙.
Proof.
    intros f.
    split; apply cat_lid.
Qed.

Program Definition CoproductCat : Category := {|
    cat_U := coproduct_base;
    morphism f g := set_type (coproduct_set f g);
    cat_compose F G H f g := [_|coproduct_compose_in f g];
    cat_id f := [_|coproduct_id_in f];
|}.
Next Obligation.
    unfold coproduct_compose.
    apply set_type_eq; cbn.
    apply cat_assoc.
Qed.
Next Obligation.
    unfold coproduct_compose.
    apply set_type_eq; cbn.
    apply cat_lid.
Qed.
Next Obligation.
    unfold coproduct_compose.
    apply set_type_eq; cbn.
    apply cat_rid.
Qed.

End Coproduct.

Arguments coproduct_obj {C A B}.
Arguments obj_ι1 {C A B}.
Arguments obj_ι2 {C A B}.

Class HasCoproducts (C : Category) := {
    coproduct (A B : C) : CoproductCat A B;
    coproduct_term : ∀ A B, initial (coproduct A B);
    ι1 (A B : C) := obj_ι1 (coproduct A B);
    ι2 (A B : C) := obj_ι2 (coproduct A B);
}.

Notation "A ∐ B" := (coproduct_obj (coproduct A B)).

Unset Universe Polymorphism.
