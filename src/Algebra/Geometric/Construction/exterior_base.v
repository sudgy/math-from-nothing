Require Import init.

Require Import geometric_sum.
Require Import algebra_category.
Require Import category_initterm.
Require Import linear_unital_zero.

Section ExteriorAlgebra.

Context {U : CRingObj} (V : Module U).

Definition zero_bilinear (a b : V) : U := 0.

Lemma zero_bilinear_in : bilinear_form zero_bilinear.
Proof.
    repeat split; unfold zero_bilinear; intros.
    all: symmetry.
    1, 2: apply mult_ranni.
    1, 2: apply plus_lid.
Qed.

Definition exterior_algebra : Algebra U
    := geometric_algebra [_|zero_bilinear_in].
Local Notation ext := exterior_algebra.

Definition vector_to_ext : ModuleObjHomomorphism V ext := vector_to_geo _.

Definition scalar_to_ext (a : U) : ext := scalar_to_geo _ a.

Theorem scalar_to_ext_plus : ∀ a b,
    scalar_to_ext (a + b) = scalar_to_ext a + scalar_to_ext b.
Proof.
    apply scalar_to_geo_plus.
Qed.
Theorem scalar_to_ext_zero : scalar_to_ext 0 = 0.
Proof.
    apply scalar_to_geo_zero.
Qed.
Theorem scalar_to_ext_mult : ∀ a b,
    scalar_to_ext (a * b) = scalar_to_ext a * scalar_to_ext b.
Proof.
    apply scalar_to_geo_mult.
Qed.
Theorem scalar_to_ext_scalar : ∀ a A, scalar_to_ext a * A = a · A.
Proof.
    apply scalar_to_geo_scalar.
Qed.
Theorem scalar_to_ext_neg : ∀ a, scalar_to_ext (-a) = -scalar_to_ext a.
Proof.
    apply scalar_to_geo_neg.
Qed.
Theorem scalar_to_ext_one : scalar_to_ext 1 = 1.
Proof.
    apply scalar_to_geo_one.
Qed.
Theorem scalar_to_ext_comm : ∀ a A, scalar_to_ext a * A = A * scalar_to_ext a.
Proof.
    apply scalar_to_geo_comm.
Qed.

Theorem ext_alternating : ∀ v, 0 = vector_to_ext v * vector_to_ext v.
Proof.
    intros v.
    rewrite geo_contract.
    unfold zero_bilinear; cbn.
    rewrite scalar_lanni.
    reflexivity.
Qed.

Theorem ext_anticomm : ∀ u v,
    vector_to_ext u * vector_to_ext v = -(vector_to_ext v * vector_to_ext u).
Proof.
    intros u v.
    pose proof (ext_alternating (v + u)) as eq.
    rewrite module_homo_plus in eq.
    rewrite ldist in eq.
    do 2 rewrite rdist in eq.
    do 2 rewrite <- ext_alternating in eq.
    rewrite plus_rid, plus_lid in eq.
    rewrite plus_0_ab_a_nb in eq.
    exact eq.
Qed.

Theorem ext_sum : ∀ x : ext, ∃ l : ulist (U * list V),
    x = ulist_sum (ulist_image (λ p, fst p · list_prod
        (list_image (λ v, vector_to_ext v) (snd p))) l).
Proof.
    apply geo_sum.
Qed.

Record to_ext := make_to_ext {
    to_ext_algebra : Algebra U;
    to_ext_homo : ModuleObjHomomorphism V (algebra_module to_ext_algebra);
    to_ext_alternating : ∀ v, 0 = to_ext_homo v * to_ext_homo v;
}.

Definition to_ext_set (f g : to_ext)
    (h : cat_morphism (to_ext_algebra f)
                      (to_ext_algebra g))
    := ∀ x, h (to_ext_homo f x) = to_ext_homo g x.

Definition to_ext_compose {F G H : to_ext}
    (f : set_type (to_ext_set G H)) (g : set_type (to_ext_set F G))
    := [f|] ∘ [g|].

Lemma to_ext_set_compose_in {F' G H : to_ext} :
        ∀ (f : set_type (to_ext_set G H)) g,
        to_ext_set F' H (to_ext_compose f g).
Proof.
    intros [f f_eq] [g g_eq].
    unfold to_ext_set in *.
    unfold to_ext_compose; cbn.
    intros x.
    rewrite g_eq.
    apply f_eq.
Qed.

Lemma to_ext_set_id_in : ∀ f : to_ext, to_ext_set f f 𝟙.
Proof.
    intros f.
    unfold to_ext_set.
    intros x.
    cbn.
    reflexivity.
Qed.

Program Instance TO_EXT : Category := {
    cat_U := to_ext;
    cat_morphism f g := set_type (to_ext_set f g);
    cat_compose {F G H} f g := [_|to_ext_set_compose_in f g];
    cat_id f := [_|to_ext_set_id_in f];
}.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_assoc (Algebra U)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_lid (Algebra U)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_rid (Algebra U)).
Qed.

Definition ext_to_ext := make_to_ext
    exterior_algebra
    vector_to_ext
    ext_alternating.

Theorem exterior_universal : @initial TO_EXT ext_to_ext.
Proof.
    unfold initial.
    intros [A f f_alt].
    assert (∀ v, f v * f v = zero_bilinear v v · 1) as f_contr.
    {
        intros v.
        unfold zero_bilinear.
        rewrite <- f_alt.
        rewrite scalar_lanni.
        reflexivity.
    }
    exact (geometric_universal _ (make_to_geo[_|zero_bilinear_in] A f f_contr)).
Qed.

Let to_uz (v : V) : unital_zero_algebra V := (0, v).

Lemma to_uz_plus : ∀ u v, to_uz (u + v) = to_uz u + to_uz v.
Proof.
    intros u v.
    unfold to_uz.
    unfold plus at 2; cbn.
    rewrite plus_lid.
    reflexivity.
Qed.

Lemma to_uz_scalar : ∀ a v, to_uz (a · v) = a · to_uz v.
Proof.
    intros a v.
    unfold to_uz.
    unfold scalar_mult at 2; cbn.
    unfold scalar_mult at 2; cbn.
    rewrite mult_ranni.
    reflexivity.
Qed.

Lemma to_uz_alternating : ∀ v, 0 = to_uz v * to_uz v.
Proof.
    intros v.
    unfold mult; cbn.
    rewrite mult_lanni.
    rewrite scalar_lanni.
    rewrite plus_lid.
    reflexivity.
Qed.

Let to_uz_homo := make_module_homomorphism
    U
    V
    (algebra_module (unital_zero_algebra V))
    to_uz
    to_uz_plus
    to_uz_scalar.

Let to_uz_base := make_to_ext
    (unital_zero_algebra V)
    to_uz_homo
    to_uz_alternating.

Let ext_to_uz_base := ex_singleton (exterior_universal to_uz_base).
Let ext_to_uz := [ext_to_uz_base|].

Theorem vector_to_ext_eq : ∀ a b, vector_to_ext a = vector_to_ext b → a = b.
Proof.
    intros a b eq.
    apply (f_equal ext_to_uz) in eq.
    pose proof [|ext_to_uz_base] as to_uz_eq.
    unfold to_ext_set in to_uz_eq; cbn in to_uz_eq.
    unfold ext_to_uz in eq.
    do 2 rewrite to_uz_eq in eq.
    inversion eq.
    reflexivity.
Qed.

Theorem scalar_to_ext_eq : ∀ a b, scalar_to_ext a = scalar_to_ext b → a = b.
Proof.
    intros a b eq.
    apply (f_equal ext_to_uz) in eq.
    unfold scalar_to_ext in eq.
    unfold ext_to_uz in eq.
    do 2 rewrite algebra_homo_scalar in eq.
    rewrite algebra_homo_one in eq.
    unfold one, scalar_mult in eq; cbn in eq.
    unfold scalar_mult at 1 3 in eq; cbn in eq.
    do 2 rewrite mult_rid in eq.
    inversion eq.
    reflexivity.
Qed.

End ExteriorAlgebra.
