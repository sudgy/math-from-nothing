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

Definition geo_grade := grade_isomorphism (ext_to_geo_homo B) (ext_to_geo_iso B).

Existing Instance geo_grade.

Theorem scalar_to_geo_grade : ∀ a, of_grade 0 (σ a).
Proof.
    intros a.
    exists (scalar_to_ext V a).
    cbn.
    split.
    -   apply scalar_to_ext_grade.
    -   apply ext_to_geo_of_scalar.
Qed.

Theorem geo_grade_zero_scalar : ∀ v : geo, of_grade 0 v → (∃ a, v = σ a).
Proof.
    intros v.
    intros [v' [v0 v_eq]].
    subst v.
    apply (ext_grade_zero_scalar V v') in v0 as [a v'_eq].
    subst v'.
    exists a.
    apply ext_to_geo_of_scalar.
Qed.

Theorem vector_to_geo_grade : ∀ a, of_grade 1 (φ a).
Proof.
    intros a.
    exists (vector_to_ext V a).
    cbn.
    split.
    -   apply vector_to_ext_grade.
    -   apply ext_to_geo_vector.
Qed.

Theorem geo_grade_one_vector : ∀ v : geo, of_grade 1 v → (∃ a, v = φ a).
Proof.
    intros v.
    intros [v' [v0 v_eq]].
    subst v.
    apply (ext_grade_one_vector V v') in v0 as [a v'_eq].
    subst v'.
    exists a.
    apply ext_to_geo_vector.
Qed.

Theorem geo_orthogonal_grade : ∀ l : list V,
    list_prop2 (λ a b, [B|] a b = 0) l →
    of_grade (H9 := geo_grade) (list_size l) (list_prod (list_image φ l)).
Proof.
    intros l l_orth.
    exists (list_prod (list_image (vector_to_ext V) l)).
    induction l as [|v l].
    {
        rewrite list_image_end; cbn.
        rewrite list_prod_end.
        split.
        -   rewrite <- scalar_to_ext_one.
            apply scalar_to_ext_grade.
        -   apply ext_to_geo_one.
    }
    destruct l_orth as [v_orth l_orth].
    specialize (IHl l_orth) as [IHl1 IHl2].
    rewrite list_image_add; cbn.
    split.
    -   change (list_size (v ꞉ l)) with (1 + list_size l).
        apply (grade_mult (GradedAlgebraObj := exterior_grade_mult V)).
        +   apply vector_to_ext_grade.
        +   exact IHl1.
    -   cbn in IHl2.
        rewrite ext_to_geo_add.
        rewrite IHl2.
        apply plus_0_a_ab_b.
        rewrite <- neg_zero.
        apply f_equal.
        clear l_orth IHl1 IHl2.
        induction l as [|u l].
        +   rewrite list_image_end; cbn.
            rewrite list_prod_end.
            rewrite <- scalar_to_geo_one.
            symmetry; apply geo_mult_inner_scalar.
        +   destruct v_orth as [uv_orth u_orth].
            specialize (IHl u_orth).
            rewrite list_image_add; cbn.
            rewrite geo_mult_inner_add.
            rewrite <- IHl.
            rewrite mult_ranni.
            rewrite neg_zero, plus_rid.
            rewrite uv_orth.
            rewrite scalar_lanni.
            reflexivity.
Qed.

Theorem ext_to_geo_project : ∀ (a : ext) (n : nat),
    grade_project (G a) n = G (grade_project (VG := EG) a n).
Proof.
    intros a n.
    induction a as [|a a' i ai a'i IHa] using (grade_induction (VG := EG)).
    {
        rewrite ext_to_geo_zero.
        do 2 rewrite grade_project_zero.
        rewrite ext_to_geo_zero.
        reflexivity.
    }
    rewrite ext_to_geo_plus.
    do 2 rewrite grade_project_plus.
    rewrite ext_to_geo_plus.
    rewrite IHa.
    apply rplus; clear a' a'i IHa.
    assert (of_grade (H9 := geo_grade) i (G a)) as ai'.
    {
        exists a.
        split; [>exact ai|reflexivity].
    }
    classic_case (i = n) as [eq|neq].
    -   subst.
        rewrite (grade_project_of_grade _ _ ai).
        apply (grade_project_of_grade _ _ ai').
    -   rewrite (grade_project_of_grade_neq _ _ _ ai neq).
        rewrite ext_to_geo_zero.
        apply (grade_project_of_grade_neq _ _ _ ai' neq).
Qed.

Theorem geo_to_ext_project : ∀ (a : geo) (n : nat),
    grade_project (VG := EG) (E a) n = E (grade_project a n).
Proof.
    intros a n.
    rewrite <- (geo_to_ext_to_geo B (grade_project (VG := EG) (E a) n)).
    rewrite <- ext_to_geo_project.
    rewrite ext_to_geo_to_ext.
    reflexivity.
Qed.

End GeometricGrade.
