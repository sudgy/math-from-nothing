Require Import init.

Require Export linear_grade.
Require Import linear_grade_isomorphism.
Require Export linear_bilinear_form.

Require Export geometric_universal.
Require Import geometric_exterior_isomorphism.
Require Import exterior_grade2.
Require Import exterior_base.
Require Export nat.

Section GeometricGrade.

Context {F : CRingObj} {V : ModuleObj F}.
Context (B : set_type (bilinear_form (V := V))).

Local Notation φ := (vector_to_geo B).
Local Notation σ := (scalar_to_geo B).
Local Notation E := (geo_to_ext B).
Local Notation G := (ext_to_geo B).
Local Notation geo := (geometric_algebra B).
Local Notation ext := (exterior_algebra V).

Let EG := exterior_grade V.
Let EGA := exterior_grade_mult V.

Existing Instances EG EGA.

Definition geo_grade := grade_isomorphism
    (ext_to_geo_homo B) (geo_to_ext_homo B)
    (make_and (ext_to_geo_to_ext_homo B) (geo_to_ext_to_geo_homo B)).

Existing Instance geo_grade.

Theorem scalar_to_geo_grade : ∀ a, of_grade 0 (σ a).
Proof.
    intros a.
    apply of_grade_iso_g.
    cbn.
    rewrite geo_to_ext_of_scalar.
    apply scalar_to_ext_grade.
Qed.

Theorem geo_grade_zero_scalar : ∀ v : geo, of_grade 0 v → (∃ a, v = σ a).
Proof.
    intros v v0.
    apply of_grade_iso_g in v0.
    apply ext_grade_zero_scalar in v0 as [a eq].
    exists a.
    cbn in eq.
    apply (f_equal G) in eq.
    rewrite ext_to_geo_to_ext in eq.
    rewrite ext_to_geo_of_scalar in eq.
    exact eq.
Qed.

Theorem vector_to_geo_grade : ∀ a, of_grade 1 (φ a).
Proof.
    intros a.
    apply of_grade_iso_g.
    cbn.
    rewrite geo_to_ext_vector.
    apply vector_to_ext_grade.
Qed.

Theorem geo_grade_one_vector : ∀ v : geo, of_grade 1 v → (∃ a, v = φ a).
Proof.
    intros v v1.
    apply of_grade_iso_g in v1.
    apply ext_grade_one_vector in v1 as [a eq].
    exists a.
    cbn in eq.
    apply (f_equal G) in eq.
    rewrite ext_to_geo_to_ext in eq.
    rewrite ext_to_geo_vector in eq.
    exact eq.
Qed.

Theorem geo_orthogonal_ext : ∀ l : list V,
    list_prop2 (λ a b, [B|] a b = 0) l →
    list_prod (list_image φ l) = G (list_prod (list_image (vector_to_ext V) l)).
Proof.
    intros l l_orth.
    induction l as [|v l].
    {
        do 2 rewrite list_image_end.
        do 2 rewrite list_prod_end.
        symmetry; apply ext_to_geo_one.
    }
    rewrite list_prop2_add in l_orth.
    destruct l_orth as [v_orth l_orth].
    specialize (IHl l_orth).
    do 2 rewrite list_image_add.
    do 2 rewrite list_prod_add.
    rewrite IHl; clear IHl.
    rewrite ext_to_geo_add.
    rewrite <- plus_0_a_b_ab.
    clear l_orth.
    rewrite <- ext_to_geo_inner.
    rewrite <- neg_zero.
    apply f_equal.
    rewrite <- ext_to_geo_zero.
    apply f_equal.
    list_prop_induction l v_orth as u u_ortho IHl.
    {
        rewrite list_image_end, list_prod_end.
        rewrite <- scalar_to_ext_one.
        rewrite ext_inner_scalar.
        reflexivity.
    }
    rewrite list_image_add, list_prod_add.
    rewrite ext_inner_add.
    rewrite <- IHl.
    rewrite u_ortho.
    rewrite scalar_lanni, mult_ranni.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem geo_orthogonal_grade : ∀ l : list V,
    list_prop2 (λ a b, [B|] a b = 0) l →
    of_grade (list_size l) (list_prod (list_image φ l)).
Proof.
    intros l l_orth.
    rewrite (geo_orthogonal_ext l l_orth).
    apply of_grade_iso_g.
    cbn.
    rewrite geo_to_ext_to_geo.
    apply ext_list_grade.
Qed.

Theorem ext_to_geo_project : ∀ (a : ext) (n : nat),
    grade_project (G a) n = G (grade_project a n).
Proof.
    intros a n.
    pose proof (grade_iso_f_project _ _ (make_and
        (ext_to_geo_to_ext_homo B) (geo_to_ext_to_geo_homo B)) n a) as eq.
    cbn in eq.
    exact eq.
Qed.

Theorem geo_to_ext_project : ∀ (a : geo) (n : nat),
    grade_project (E a) n = E (grade_project a n).
Proof.
    intros a n.
    rewrite <- (geo_to_ext_to_geo B (grade_project (E a) n)).
    rewrite <- ext_to_geo_project.
    rewrite ext_to_geo_to_ext.
    reflexivity.
Qed.

Theorem ext_to_geo_of_grade : ∀ (a : ext) (n : nat),
    of_grade n a ↔ of_grade n (G a).
Proof.
    intros a n.
    apply of_grade_iso_f.
Qed.

Theorem geo_to_ext_of_grade : ∀ (a : geo) (n : nat),
    of_grade n a ↔ of_grade n (E a).
Proof.
    intros a n.
    apply of_grade_iso_g.
Qed.

End GeometricGrade.
