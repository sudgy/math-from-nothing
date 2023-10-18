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
    coproduct_init : ∀ A B, initial (coproduct A B);
    ι1 (A B : C) := obj_ι1 (coproduct A B);
    ι2 (A B : C) := obj_ι2 (coproduct A B);
}.

Notation "A ∐ B" := (coproduct_obj (coproduct A B)).

Section ProductCoproduct.

Context {C : Category} `{HasProducts C, HasCoproducts C}.

Local Program Instance product_coproduct : HasCoproducts (dual_category C) := {
    coproduct (A B : C) := make_coproduct_obj A B (A ∏ B) (π1 A B) (π2 A B)
}.
Next Obligation.
    intros [P i1 i2].
    exact (product_term A B (make_product_obj A B P i1 i2)).
Qed.

Local Program Instance coproduct_product : HasProducts (dual_category C) := {
    product (A B : C) := make_product_obj A B (A ∐ B) (ι1 A B) (ι2 A B)
}.
Next Obligation.
    intros [P i1 i2].
    exact (coproduct_init A B (make_coproduct_obj A B P i1 i2)).
Qed.

End ProductCoproduct.

Section Coproduct.

Context {C : Category} `{HasCoproducts C}.

Context (A B : C).
Context (P : CoproductCat A B).

Definition coproduct_f := [ex_singleton (coproduct_init A B P)|].

Check coproduct_f.

Theorem coproduct_f1 : coproduct_f ∘ ι1 A B = obj_ι1 P.
Proof.
    apply [|ex_singleton (coproduct_init A B P)].
Qed.

Theorem coproduct_f2 : coproduct_f ∘ ι2 A B = obj_ι2 P.
Proof.
    apply [|ex_singleton (coproduct_init A B P)].
Qed.

Theorem coproduct_f_uni : ∀ f,
    f ∘ ι1 A B = obj_ι1 P → f ∘ ι2 A B = obj_ι2 P → f = coproduct_f.
Proof.
    intros f eq1 eq2.
    pose proof (coproduct_init A B P) as S.
    cbn in S.
    assert (coproduct_set A B (coproduct A B) P f) as f_in by (split; assumption).
    pose proof [|ex_singleton (coproduct_init A B P)] as f_in'.
    pose proof (singleton_unique2 [_|f_in] [_|f_in']) as eq.
    rewrite set_type_eq2 in eq.
    exact eq.
Qed.

Theorem coproduct_f_uni2 : ∀ f g,
    f ∘ ι1 A B = obj_ι1 P → f ∘ ι2 A B = obj_ι2 P →
    g ∘ ι1 A B = obj_ι1 P → g ∘ ι2 A B = obj_ι2 P →
    f = g.
Proof.
    intros f g f_eq1 f_eq2 g_eq1 g_eq2.
    rewrite (coproduct_f_uni f f_eq1 f_eq2).
    symmetry; exact (coproduct_f_uni g g_eq1 g_eq2).
Qed.

End Coproduct.

Arguments coproduct_f {C H A B}.
Arguments coproduct_f1 {C H A B}.
Arguments coproduct_f2 {C H A B}.
Arguments coproduct_f_uni {C H A B}.
Arguments coproduct_f_uni2 {C H A B}.

Section CoproductComm.

Context {C : Category} `{HasCoproducts C}.

Context (A B : C).

Theorem coproduct_epi : ∀ Z : C, ∀ f g : morphism (A ∐ B) Z,
    f ∘ ι1 A B = g ∘ ι1 A B → f ∘ ι2 A B = g ∘ ι2 A B → f = g.
Proof.
    intros Z f g eq1 eq2.
    pose (ZP := make_coproduct_obj A B Z (f ∘ ι1 A B) (f ∘ ι2 A B)).
    apply (coproduct_f_uni2 ZP).
    3: rewrite <- eq1.
    4: rewrite <- eq2.
    all: reflexivity.
Qed.

Local Existing Instance coproduct_product.

Definition coproduct_comm_f := product_comm_g (C := dual_category C) A B
    : morphism (A ∐ B) (B ∐ A).
Definition coproduct_comm_g := product_comm_f (C := dual_category C) A B
    : morphism (B ∐ A) (A ∐ B).

Let f := coproduct_comm_f.
Let g := coproduct_comm_g.

Theorem coproduct_comm_iso : is_isomorphism_pair f g.
Proof.
    exact (product_comm_iso (C := dual_category C) A B).
Qed.

Theorem coproduct_comm : A ∐ B ≅ B ∐ A.
Proof.
    exists f g.
    exact coproduct_comm_iso.
Qed.

Theorem coproduct_comm_f1 : f ∘ ι2 A B = ι1 B A.
Proof.
    exact (product_comm_g1 (C := dual_category C) A B).
Qed.
Theorem coproduct_comm_f2 : f ∘ ι1 A B = ι2 B A.
Proof.
    exact (product_comm_g2 (C := dual_category C) A B).
Qed.
Theorem coproduct_comm_g1 : g ∘ ι2 B A = ι1 A B.
Proof.
    exact (product_comm_f1 (C := dual_category C) A B).
Qed.
Theorem coproduct_comm_g2 : g ∘ ι1 B A = ι2 A B.
Proof.
    exact (product_comm_f2 (C := dual_category C) A B).
Qed.

End CoproductComm.
Section CoproductAssoc.

Context {C0 : Category} `{HasCoproducts C0}.

Context (A B C : C0).

Local Existing Instance coproduct_product.

Definition coproduct_assoc_f := product_assoc_g (C0 := dual_category C0) A B C
    : morphism (A ∐ (B ∐ C)) ((A ∐ B) ∐ C).
Definition coproduct_assoc_g := product_assoc_f (C0 := dual_category C0) A B C
    : morphism ((A ∐ B) ∐ C) (A ∐ (B ∐ C)).

Let f := coproduct_assoc_f.
Let g := coproduct_assoc_g.

Theorem coproduct_assoc_iso : is_isomorphism_pair f g.
Proof.
    (* Note that this proof could be simplified to a single line like
    [coproduct_comm_iso], but for some reason it takes a while to run so I'm
    writing it the long way. *)
    pose proof (product_assoc_iso (C0 := dual_category C0) A B C) as [eq1 eq2].
    split.
    -   exact eq1.
    -   exact eq2.
Qed.

Theorem coproduct_assoc : A ∐ (B ∐ C) ≅ (A ∐ B) ∐ C.
Proof.
    exists f g.
    exact coproduct_assoc_iso.
Qed.

Theorem coproduct_assoc_f1 : f ∘ ι1 A (B ∐ C) = ι1 (A ∐ B) C ∘ ι1 A B.
Proof.
    exact (product_assoc_g1 (C0 := dual_category C0) A B C).
Qed.
Theorem coproduct_assoc_f2 : f ∘ ι2 A (B ∐ C) ∘ ι1 B C = ι1 (A ∐ B) C ∘ ι2 A B.
Proof.
    rewrite <- cat_assoc.
    exact (product_assoc_g2 (C0 := dual_category C0) A B C).
Qed.
Theorem coproduct_assoc_f3 : f ∘ ι2 A (B ∐ C) ∘ ι2 B C = ι2 (A ∐ B) C.
Proof.
    rewrite <- cat_assoc.
    exact (product_assoc_g3 (C0 := dual_category C0) A B C).
Qed.
Theorem coproduct_assoc_g1 : g ∘ ι1 (A ∐ B) C ∘ ι1 A B = ι1 A (B ∐ C).
Proof.
    rewrite <- cat_assoc.
    exact (product_assoc_f1 (C0 := dual_category C0) A B C).
Qed.
Theorem coproduct_assoc_g2 : g ∘ ι1 (A ∐ B) C ∘ ι2 A B = ι2 A (B ∐ C) ∘ ι1 B C.
Proof.
    rewrite <- cat_assoc.
    exact (product_assoc_f2 (C0 := dual_category C0) A B C).
Qed.
Theorem coproduct_assoc_g3 : g ∘ ι2 (A ∐ B) C = ι2 A (B ∐ C) ∘ ι2 B C.
Proof.
    exact (product_assoc_f3 (C0 := dual_category C0) A B C).
Qed.

End CoproductAssoc.

Unset Universe Polymorphism.
