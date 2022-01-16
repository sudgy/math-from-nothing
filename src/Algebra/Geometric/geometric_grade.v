Require Import init.

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
Let GL := ga_ldist B.
Let GR := ga_rdist B.
Let GS := ga_scalar B.
Let GSL := ga_scalar_ldist B.
Let GSC := ga_scalar_comp B.
Let GSMR := ga_scalar_rmult B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GL GR GS GSL GSC GSMR.

Local Notation "'φ'" := (vector_to_ga B).
Local Notation "'σ'" := (scalar_to_ga B).
Local Notation "'E'" := (geo_to_ext B).
Local Notation "'G'" := (ext_to_geo B).

Let EG := exterior_grade V.

Existing Instances EG.

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

End GeometricGrade.
