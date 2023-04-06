Require Import init.

Require Import algebra_category.
Require Import set.

Section TensorAlgebraDefs.

Context {F : CRingObj} (V : ModuleObj F).

Record to_algebra := make_to_algebra {
    to_algebra_algebra : Algebra F;
    to_algebra_homo : ModuleObjHomomorphism V (algebra_module to_algebra_algebra);
}.

Definition to_algebra_set (f g : to_algebra)
    (h : cat_morphism (to_algebra_algebra f)
                      (to_algebra_algebra g))
    := ∀ x, h (to_algebra_homo f x) = to_algebra_homo g x.

Definition to_algebra_compose {F G H : to_algebra}
    (f : set_type (to_algebra_set G H)) (g : set_type (to_algebra_set F G))
    := [f|] ∘ [g|].

Lemma to_algebra_set_compose_in {F' G H : to_algebra} :
    ∀ (f : set_type (to_algebra_set G H)) g,
    to_algebra_set F' H (to_algebra_compose f g).
Proof.
    intros [f f_eq] [g g_eq].
    unfold to_algebra_set in *.
    unfold to_algebra_compose; cbn.
    intros x.
    rewrite g_eq.
    apply f_eq.
Qed.

Lemma to_algebra_set_id_in : ∀ f : to_algebra, to_algebra_set f f 𝟙.
Proof.
    intros f.
    unfold to_algebra_set.
    intros x.
    cbn.
    reflexivity.
Qed.

Program Instance TO_ALGEBRA : Category := {
    cat_U := to_algebra;
    cat_morphism f g := set_type (to_algebra_set f g);
    cat_compose {F G H} f g := [_|to_algebra_set_compose_in f g];
    cat_id f := [_|to_algebra_set_id_in f];
}.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_assoc (Algebra F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_lid (Algebra F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_rid (Algebra F)).
Qed.

End TensorAlgebraDefs.
