Require Import init.

Require Import mult_product.

Require Export linear_grade.
Require Import linear_grade_isomorphism.

Require Export geometric_construct.
Require Import geometric_exterior_isomorphism.
Require Import exterior_grade.

(* begin hide *)
Section GeometricGrade.

(* end hide *)
Context {F : CRingObj} {V : ModuleObj F}.
(* begin hide *)

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

(* end hide *)
Context (B : set_type bilinear_form).

(* begin hide *)
Let GP := geo_plus B.
Let GZ := geo_zero B.
Let GN := geo_neg B.
Let GPA := geo_plus_assoc B.
Let GPC := geo_plus_comm B.
Let GPZ := geo_plus_lid B.
Let GPN := geo_plus_linv B.
Let GM := geo_mult B.
Let GO := geo_one B.
Let GL := geo_ldist B.
Let GR := geo_rdist B.
Let GS := geo_scalar B.
Let GSL := geo_scalar_ldist B.
Let GSR := geo_scalar_rdist B.
Let GSO := geo_scalar_id B.
Let GSC := geo_scalar_comp B.
Let GSMR := geo_scalar_rmult B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GL GR GS GSL GSR GSO GSC GSMR.

Local Notation "'φ'" := (vector_to_geo B).
Local Notation "'σ'" := (scalar_to_geo B).
Local Notation "'E'" := (geo_to_ext B).
Local Notation "'G'" := (ext_to_geo B).

Let EP := ext_plus V.
Let EZ := ext_zero V.
Let EN := ext_neg V.
Let EPA := ext_plus_assoc V.
Let EPC := ext_plus_comm V.
Let EPZ := ext_plus_lid V.
Let EPN := ext_plus_linv V.
Let EM := ext_mult V.
Let EO := ext_one V.
Let EL := ext_ldist V.
Let ER := ext_rdist V.
Let EMR := ext_mult_rid V.
Let EMA := ext_mult_assoc V.
Let ES := ext_scalar V.
Let ESO := ext_scalar_id V.
Let ESL := ext_scalar_ldist V.
Let ESR := ext_scalar_rdist V.
Let EG := exterior_grade V.
Let EGA := exterior_grade_mult V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO EL ER EMR EMA ES ESO ESL ESR
    EG EGA.

(* end hide *)
Definition geo_grade := grade_isomorphism (ext_to_geo_homo B) (ext_to_geo_iso B).

Existing Instance geo_grade.

Theorem scalar_to_geo_grade : ∀ a, of_grade 0 (σ a).
    intros a.
    exists (scalar_to_ext V a).
    cbn.
    split.
    -   apply scalar_to_ext_grade.
    -   apply ext_to_geo_of_scalar.
Qed.

Theorem geo_grade_zero_scalar : ∀ v : geo B, of_grade 0 v → (∃ a, v = σ a).
    intros v.
    intros [v' [v0 v_eq]].
    subst v.
    apply (ext_grade_zero_scalar V v') in v0 as [a v'_eq].
    subst v'.
    exists a.
    apply ext_to_geo_of_scalar.
Qed.

Theorem vector_to_geo_grade : ∀ a, of_grade 1 (φ a).
    intros a.
    exists (vector_to_ext V a).
    cbn.
    split.
    -   apply vector_to_ext_grade.
    -   apply ext_to_geo_vector.
Qed.

Theorem geo_grade_one_vector : ∀ v : geo B, of_grade 1 v → (∃ a, v = φ a).
    intros v.
    intros [v' [v0 v_eq]].
    subst v.
    apply (ext_grade_one_vector V v') in v0 as [a v'_eq].
    subst v'.
    exists a.
    apply ext_to_geo_vector.
Qed.

Theorem geo_orthogonal_grade : ∀ l : list (module_V V),
        list_prop2 (λ a b, [B|] a b = 0) l →
        of_grade (H10 := geo_grade) (list_size l) (list_prod (list_image l φ)).
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
        +   cbn.
            rewrite <- scalar_to_geo_one.
            symmetry; apply geo_mult_inner_scalar.
        +   destruct v_orth as [uv_orth u_orth].
            specialize (IHl u_orth).
            cbn.
            rewrite geo_mult_inner_add.
            rewrite <- IHl.
            rewrite mult_ranni.
            rewrite neg_zero, plus_rid.
            rewrite uv_orth.
            rewrite scalar_lanni.
            reflexivity.
Qed.

Theorem ext_to_geo_project : ∀ (a : ext V) (n : nat),
        grade_project (G a) n = G (grade_project (VG := EG) a n).
    intros a n.
    induction a as [|a a' i ai a'i IHa] using grade_induction.
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
    assert (of_grade (H10 := geo_grade) i (G a)) as ai'.
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

Theorem geo_to_ext_project : ∀ (a : geo B) (n : nat),
        grade_project (VG := EG) (E a) n = E (grade_project a n).
    intros a n.
    rewrite <- (geo_to_ext_to_geo B (grade_project (VG := EG) (E a) n)).
    rewrite <- ext_to_geo_project.
    rewrite ext_to_geo_to_ext.
    reflexivity.
Qed.
(* begin hide *)

End GeometricGrade.
(* end hide *)
