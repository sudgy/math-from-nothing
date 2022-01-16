Require Import init.

Require Import mult_product.

Require Export linear_grade.
Require Import linear_grade_isomorphism.

Require Export geometric_construct.
Require Import geometric_exterior_isomorphism.
Require Import exterior_grade.

Section GeometricGrade.

Context {F : CRing} {V : Module F}.

Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMC := cring_mult_comm F.

Existing Instances UP UZ UN UPC UPZ UPN UM UO UMC.

Let VP := module_plus V.
Let VS := module_scalar V.

Existing Instances VP VS.

Context (B : set_type bilinear_form).

Let GP := ga_plus B.
Let GZ := ga_zero B.
Let GN := ga_neg B.
Let GPA := ga_plus_assoc B.
Let GPC := ga_plus_comm B.
Let GPZ := ga_plus_lid B.
Let GPN := ga_plus_linv B.
Let GM := ga_mult B.
Let GO := ga_one B.
Let GL := ga_ldist B.
Let GR := ga_rdist B.
Let GS := ga_scalar B.
Let GSL := ga_scalar_ldist B.
Let GSR := ga_scalar_rdist B.
Let GSC := ga_scalar_comp B.
Let GSMR := ga_scalar_rmult B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GL GR GS GSL GSR GSC GSMR.

Local Notation "'φ'" := (vector_to_ga B).
Local Notation "'σ'" := (scalar_to_ga B).
Local Notation "'E'" := (geo_to_ext B).
Local Notation "'G'" := (ext_to_geo B).

Let EM := ext_mult V.
Let EO := ext_one V.
Let EG := exterior_grade V.

Existing Instances EM EO EG.

Definition ga_grade := grade_isomorphism (ext_to_geo_homo B) (ext_to_geo_iso B).

Existing Instance ga_grade.

Theorem scalar_to_ga_grade : ∀ a, of_grade 0 (σ a).
    intros a.
    exists (scalar_to_ext V a).
    cbn.
    split.
    -   apply scalar_to_ext_grade.
    -   apply ext_to_geo_of_scalar.
Qed.

Theorem ext_grade_zero_scalar : ∀ v : ga B, of_grade 0 v ↔ (∃ a, v = σ a).
    intros v.
    split.
    -   intros [v' [v0 v_eq]].
        subst v.
        apply (ext_grade_zero_scalar V v') in v0 as [a v'_eq].
        subst v'.
        exists a.
        apply ext_to_geo_of_scalar.
    -   intros [a v_eq]; subst v.
        apply scalar_to_ga_grade.
Qed.

Theorem vector_to_ga_grade : ∀ a, of_grade 1 (φ a).
    intros a.
    exists (vector_to_ext V a).
    cbn.
    split.
    -   apply vector_to_ext_grade.
    -   apply ext_to_geo_vector.
Qed.

Theorem ga_grade_one_vector : ∀ v : ga B, of_grade 1 v ↔ (∃ a, v = φ a).
    intros v.
    split.
    -   intros [v' [v0 v_eq]].
        subst v.
        apply (ext_grade_one_vector V v') in v0 as [a v'_eq].
        subst v'.
        exists a.
        apply ext_to_geo_vector.
    -   intros [a v_eq]; subst v.
        apply vector_to_ga_grade.
Qed.

Theorem ga_orthogonal_grade : ∀ l : list (module_V V),
        list_prop2 (λ a b, [B|] a b = 0) l →
        of_grade (list_size l) (list_prod (list_image l φ)).
    intros l l_orth.
    exists (list_prod (list_image l (vector_to_ext V))).
    induction l as [|v l].
    {
        cbn.
        split.
        -   rewrite <- scalar_to_ext_one.
            apply scalar_to_ext_grade.
        -   apply ext_to_geo_one.
    }
    destruct l_orth as [v_orth l_orth].
    specialize (IHl l_orth) as [IHl1 IHl2].
    cbn.
    split.
    -   change (nat_suc (list_size l)) with (1 + list_size l).
        apply (grade_mult (GradedAlgebra := exterior_grade_mult V)).
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
        +   cbn.
            rewrite <- scalar_to_ga_one.
            symmetry; apply ga_mult_inner_scalar.
        +   destruct v_orth as [uv_orth u_orth].
            specialize (IHl u_orth).
            cbn.
            rewrite ga_mult_inner_add.
            rewrite <- IHl.
            rewrite mult_ranni.
            rewrite neg_zero, plus_rid.
            rewrite uv_orth.
            rewrite scalar_lanni.
            reflexivity.
Qed.

End GeometricGrade.
