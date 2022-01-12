Require Import init.

Require Import module_category.
Require Import algebra_category.
Require Import tensor_algebra.
Require Import linear_grade.

Require Import ring_ideal.

Require Import set.
Require Import unordered_list.

Section ExteriorConstruct.

Context {F : CRing} (V : Module F).

Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UR := cring_ldist F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let VP := module_plus V.
Let VZ := module_zero V.
Let VN := module_neg V.
Let VPA := module_plus_assoc V.
Let VPC := module_plus_comm V.
Let VPZ := module_plus_lid V.
Let VPN := module_plus_linv V.
Let VSM := module_scalar V.
Let VSMO := module_scalar_id V.
Let VSMR := module_scalar_rdist V.
Let TAP := algebra_plus (tensor_algebra V).
Let TAZ := algebra_zero (tensor_algebra V).
Let TAN := algebra_neg (tensor_algebra V).
Let TAPA := algebra_plus_assoc (tensor_algebra V).
Let TAPC := algebra_plus_comm (tensor_algebra V).
Let TAPZ := algebra_plus_lid (tensor_algebra V).
Let TAPN := algebra_plus_linv (tensor_algebra V).
Let TASM := algebra_scalar (tensor_algebra V).
Let TASMO := algebra_scalar_id (tensor_algebra V).
Let TASMC := algebra_scalar_comp (tensor_algebra V).
Let TASL := algebra_scalar_ldist (tensor_algebra V).
Let TASR := algebra_scalar_rdist (tensor_algebra V).
Let TASLM := algebra_scalar_lmult (tensor_algebra V).
Let TASRM := algebra_scalar_rmult (tensor_algebra V).
Let TAM := algebra_mult (tensor_algebra V).
Let TAO := algebra_one (tensor_algebra V).
Let TAL := algebra_ldist (tensor_algebra V).
Let TAR := algebra_rdist (tensor_algebra V).
Let TAMA := algebra_mult_assoc (tensor_algebra V).
Let TAML := algebra_mult_lid (tensor_algebra V).
Let TAMR := algebra_mult_rid (tensor_algebra V).
Let TAG := tensor_grade V.
Let TAGM := tensor_grade_mult V.

Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UR UMC UMO VP VZ VN VPA VPC
    VPZ VPN VSM VSMO VSMR TAP TAZ TAN TAPA TAPC TAPZ TAPN TASM TASMO TASMC TASL
    TASR TASLM TASRM TAM TAO TAL TAR TAMA TAML TAMR TAG TAGM.

Definition ext_ideal_base (x : algebra_V (tensor_algebra V))
    := ∃ v, x = vector_to_tensor v * vector_to_tensor v.

Definition ext_ideal := ideal_generated_by ext_ideal_base.

Definition ext := quotient_ring ext_ideal.
Definition ext_plus := quotient_ring_plus ext_ideal.
Definition ext_plus_assoc := quotient_ring_plus_assoc ext_ideal.
Definition ext_plus_comm := quotient_ring_plus_comm ext_ideal.
Definition ext_zero := quotient_ring_zero ext_ideal.
Definition ext_plus_lid := quotient_ring_plus_lid ext_ideal.
Definition ext_neg := quotient_ring_neg ext_ideal.
Definition ext_plus_linv := quotient_ring_plus_linv ext_ideal.
Definition ext_mult := quotient_ring_mult ext_ideal.
Definition ext_ldist := quotient_ring_ldist ext_ideal.
Definition ext_rdist := quotient_ring_rdist ext_ideal.
Definition ext_mult_assoc := quotient_ring_mult_assoc ext_ideal.
Definition ext_one := quotient_ring_one ext_ideal.
Definition ext_mult_lid := quotient_ring_mult_lid ext_ideal.
Definition ext_mult_rid := quotient_ring_mult_rid ext_ideal.

Existing Instances ext_plus ext_plus_assoc ext_plus_comm ext_zero ext_plus_lid
    ext_neg ext_plus_linv ext_mult ext_ldist ext_rdist ext_mult_assoc ext_one
    ext_mult_lid ext_mult_rid.

Lemma ext_scalar_wd : ∀ u v c, eq_equal (ideal_equiv ext_ideal) u v →
        eq_equal (ideal_equiv ext_ideal) (c · u) (c · v).
    cbn.
    change (ideal_generated_by_set ext_ideal_base) with (ideal_set ext_ideal).
    intros u v c eq.
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    rewrite <- (scalar_to_tensor_scalar V).
    apply (ideal_lmult ext_ideal).
    exact eq.
Qed.

Instance ext_scalar : ScalarMult (cring_U F) ext := {
    scalar_mult := binary_rself_op ext_scalar_wd
}.

Program Instance ext_scalar_id : ScalarId (cring_U F) ext.
Next Obligation.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_id.
Qed.

Program Instance ext_scalar_ldist : ScalarLdist (cring_U F) ext.
Next Obligation.
    equiv_get_value u v.
    unfold scalar_mult, plus; equiv_simpl.
    apply f_equal.
    apply scalar_ldist.
Qed.

Program Instance ext_scalar_rdist : ScalarRdist (cring_U F) ext.
Next Obligation.
    equiv_get_value v.
    unfold scalar_mult, plus at 2; equiv_simpl.
    apply f_equal.
    apply scalar_rdist.
Qed.

Program Instance ext_scalar_comp : ScalarComp (cring_U F) ext.
Next Obligation.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_comp.
Qed.

Program Instance ext_scalar_lmult : ScalarLMult (cring_U F) ext.
Next Obligation.
    equiv_get_value u v.
    unfold scalar_mult, mult; equiv_simpl.
    apply f_equal.
    apply scalar_lmult.
Qed.

Program Instance ext_scalar_rmult : ScalarRMult (cring_U F) ext.
Next Obligation.
    equiv_get_value u v.
    unfold scalar_mult, mult; equiv_simpl.
    apply f_equal.
    apply scalar_rmult.
Qed.

Definition exterior_algebra := make_algebra F
    (make_module F
        ext
        ext_plus
        ext_zero
        ext_neg
        ext_plus_assoc
        ext_plus_comm
        ext_plus_lid
        ext_plus_linv
        ext_scalar
        ext_scalar_id
        ext_scalar_ldist
        ext_scalar_rdist
        ext_scalar_comp
    )
    ext_mult
    ext_ldist
    ext_rdist
    ext_mult_assoc
    ext_one
    ext_mult_lid
    ext_mult_rid
    ext_scalar_lmult
    ext_scalar_rmult.

Definition to_ext v := to_equiv_type (ideal_equiv ext_ideal) v.

Theorem to_ext_plus : ∀ u v, to_ext (u + v) = to_ext u + to_ext v.
    intros u v.
    unfold to_ext, plus at 2; equiv_simpl.
    rewrite plus_rinv.
    exact (ideal_zero ext_ideal).
Qed.

Theorem to_ext_mult : ∀ u v, to_ext (u * v) = to_ext u * to_ext v.
    intros u v.
    unfold to_ext, mult at 2; equiv_simpl.
    rewrite plus_rinv.
    exact (ideal_zero ext_ideal).
Qed.

Theorem to_ext_scalar : ∀ a v, to_ext (a · v) = a · to_ext v.
    intros a v.
    unfold to_ext, scalar_mult at 2; equiv_simpl.
    rewrite plus_rinv.
    exact (ideal_zero ext_ideal).
Qed.

Theorem to_ext_zero : to_ext 0 = 0.
    reflexivity.
Qed.

Definition vector_to_ext v := to_ext (vector_to_tensor v).

Theorem vector_to_ext_plus :
        ∀ u v, vector_to_ext (u + v) = vector_to_ext u + vector_to_ext v.
    intros u v.
    unfold vector_to_ext.
    rewrite (vector_to_tensor_plus V).
    apply to_ext_plus.
Qed.

Theorem vector_to_ext_scalar : ∀ a v, vector_to_ext (a · v) = a · vector_to_ext v.
    intros a v.
    unfold vector_to_ext.
    rewrite (vector_to_tensor_scalar V).
    apply to_ext_scalar.
Qed.

Theorem vector_to_ext_zero : vector_to_ext 0 = 0.
    unfold vector_to_ext.
    unfold VZ.
    rewrite (vector_to_tensor_zero V).
    apply to_ext_zero.
Qed.

Theorem vector_to_ext_neg : ∀ v, vector_to_ext (-v) = -vector_to_ext v.
    intros v.
    rewrite <- scalar_neg_one.
    rewrite vector_to_ext_scalar.
    apply scalar_neg_one.
Qed.

Definition scalar_to_ext a := to_ext (scalar_to_tensor V a).

Theorem scalar_to_ext_plus : ∀ a b,
        scalar_to_ext (a + b) = scalar_to_ext a + scalar_to_ext b.
    intros a b.
    unfold scalar_to_ext.
    rewrite (scalar_to_tensor_plus V).
    apply to_ext_plus.
Qed.

Theorem scalar_to_ext_zero : scalar_to_ext 0 = 0.
    unfold scalar_to_ext.
    unfold UZ.
    rewrite (scalar_to_tensor_zero V).
    apply to_ext_zero.
Qed.

Theorem scalar_to_ext_mult : ∀ a b,
        scalar_to_ext (a * b) = scalar_to_ext a * scalar_to_ext b.
    intros a b.
    unfold scalar_to_ext.
    rewrite (scalar_to_tensor_mult V).
    apply to_ext_mult.
Qed.

Theorem scalar_to_ext_scalar : ∀ a A, scalar_to_ext a * A = a · A.
    intros a A.
    equiv_get_value A.
    unfold scalar_to_ext, to_ext, mult, scalar_mult; equiv_simpl.
    rewrite (scalar_to_tensor_scalar V).
    rewrite plus_rinv.
    exact (ideal_zero ext_ideal).
Qed.

Theorem scalar_to_ext_neg : ∀ a, scalar_to_ext (-a) = -scalar_to_ext a.
    intros a.
    rewrite <- mult_neg_one.
    rewrite scalar_to_ext_mult.
    rewrite scalar_to_ext_scalar.
    apply scalar_neg_one.
Qed.

Theorem scalar_to_ext_one : scalar_to_ext 1 = 1.
    unfold scalar_to_ext.
    unfold UO.
    rewrite (scalar_to_tensor_one V).
    reflexivity.
Qed.

Theorem scalar_to_ext_comm : ∀ a A, scalar_to_ext a * A = A * scalar_to_ext a.
    intros a A.
    equiv_get_value A.
    unfold scalar_to_ext, to_ext, mult; equiv_simpl.
    rewrite (scalar_to_tensor_comm V).
    rewrite plus_rinv.
    exact (ideal_zero ext_ideal).
Qed.

Theorem scalar_to_ext_one_scalar : ∀ a, scalar_to_ext a = a · 1.
    intros a.
    rewrite <- (mult_rid (scalar_to_ext a)).
    apply scalar_to_ext_scalar.
Qed.

Theorem ext_alternating : ∀ v, 0 = vector_to_ext v * vector_to_ext v.
    intros v.
    unfold mult, zero, vector_to_ext, to_ext; equiv_simpl.
    rewrite plus_lid.
    apply (ideal_neg ext_ideal).
    unfold ideal_set; cbn.
    unfold ideal_generated_by_set; cbn.
    assert (ext_ideal_base (vector_to_tensor v * vector_to_tensor v)) as v2_in.
    {
        exists v.
        reflexivity.
    }
    exists (((1, 1), [_|v2_in]) ::: ulist_end).
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ulist_image_end, ulist_sum_end; cbn.
    rewrite mult_lid, mult_rid.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem ext_anticomm : ∀ u v,
        vector_to_ext u * vector_to_ext v =
        -(vector_to_ext v * vector_to_ext u).
    intros u v.
    pose proof (ext_alternating (v + u)) as eq.
    rewrite vector_to_ext_plus in eq.
    rewrite ldist in eq.
    do 2 rewrite rdist in eq.
    do 2 rewrite <- ext_alternating in eq.
    rewrite plus_rid, plus_lid in eq.
    rewrite plus_0_ab_a_nb in eq.
    exact eq.
Qed.

Theorem scalar_to_ext_eq : ∀ a b, scalar_to_ext a = scalar_to_ext b → a = b.
    intros a b eq.
    rewrite <- plus_0_nab_a_b.
    rewrite <- plus_0_nab_a_b in eq.
    rewrite <- scalar_to_ext_neg in eq.
    rewrite <- scalar_to_ext_plus in eq.
    remember (-a + b) as c; clear a b Heqc.
    unfold scalar_to_ext, to_ext, zero in eq; equiv_simpl in eq.
    rewrite plus_lid in eq.
    apply (ideal_neg ext_ideal) in eq.
    rewrite neg_neg in eq.
    destruct eq as [l eq].
    apply (scalar_to_tensor_eq V).
    unfold TAZ, UZ.
    rewrite (scalar_to_tensor_zero V).
    pose proof (scalar_to_tensor_grade V c) as c0.
    rewrite <- (grade_project_of_grade _ _ c0).
    rewrite eq.
    clear eq c0.
    induction l as [|v l] using ulist_induction.
    -   rewrite ulist_image_end, ulist_sum_end.
        symmetry; apply grade_project_zero.
    -   rewrite ulist_image_add, ulist_sum_add.
        rewrite grade_project_plus.
        rewrite <- IHl; clear IHl l.
        rewrite plus_rid.
        destruct v as [[v1 v2] [v3 [v v3_eq]]]; cbn.
        subst v3.
        induction v1 as [|v11 v12 i iv11 i_z] using grade_induction.
        +   do 2 rewrite mult_lanni.
            symmetry; apply grade_project_zero.
        +   do 2 rewrite rdist.
            rewrite grade_project_plus.
            rewrite <- IHv1; clear IHv1 v12 i_z.
            rewrite plus_rid.
            induction v2 as [|v21 v22 j jv12 j_z] using grade_induction.
            *   rewrite mult_ranni.
                symmetry; apply grade_project_zero.
            *   rewrite ldist.
                rewrite grade_project_plus.
                rewrite <- IHv2; clear IHv2 v22 j_z.
                rewrite plus_rid.
                assert (of_grade (i + 2 + j)
                    (v11 * (vector_to_tensor v * vector_to_tensor v) * v21))
                    as ij.
                {
                    apply of_grade_mult; [>|exact jv12].
                    apply of_grade_mult; [>exact iv11|].
                    apply of_grade_mult; apply vector_to_tensor_grade.
                }
                assert (i + 2 + j ≠ 0 ) as neq.
                {
                    intros contr.
                    rewrite (plus_comm i 2) in contr.
                    rewrite <- plus_assoc in contr.
                    inversion contr.
                }
                rewrite (grade_project_of_grade_neq _ _ _ ij neq).
                reflexivity.
Qed.

Theorem vector_to_ext_eq : ∀ a b, vector_to_ext a = vector_to_ext b → a = b.
    intros a b eq.
    rewrite <- plus_0_nab_a_b.
    rewrite <- plus_0_nab_a_b in eq.
    rewrite <- vector_to_ext_neg in eq.
    rewrite <- vector_to_ext_plus in eq.
    remember (-a + b) as c; clear a b Heqc.
    unfold vector_to_ext, to_ext, zero in eq; equiv_simpl in eq.
    rewrite plus_lid in eq.
    apply (ideal_neg ext_ideal) in eq.
    rewrite neg_neg in eq.
    destruct eq as [l eq].
    apply (vector_to_tensor_eq V).
    unfold TAZ, VZ.
    rewrite (vector_to_tensor_zero V).
    pose proof (vector_to_tensor_grade V c) as c0.
    rewrite <- (grade_project_of_grade _ _ c0).
    rewrite eq.
    clear eq c0.
    induction l as [|v l] using ulist_induction.
    -   rewrite ulist_image_end, ulist_sum_end.
        symmetry; apply grade_project_zero.
    -   rewrite ulist_image_add, ulist_sum_add.
        rewrite grade_project_plus.
        rewrite <- IHl; clear IHl l.
        rewrite plus_rid.
        destruct v as [[v1 v2] [v3 [v v3_eq]]]; cbn.
        subst v3.
        induction v1 as [|v11 v12 i iv11 i_z] using grade_induction.
        +   do 2 rewrite mult_lanni.
            symmetry; apply grade_project_zero.
        +   do 2 rewrite rdist.
            rewrite grade_project_plus.
            rewrite <- IHv1; clear IHv1 v12 i_z.
            rewrite plus_rid.
            induction v2 as [|v21 v22 j jv12 j_z] using grade_induction.
            *   rewrite mult_ranni.
                symmetry; apply grade_project_zero.
            *   rewrite ldist.
                rewrite grade_project_plus.
                rewrite <- IHv2; clear IHv2 v22 j_z.
                rewrite plus_rid.
                assert (of_grade (i + 2 + j)
                    (v11 * (vector_to_tensor v * vector_to_tensor v) * v21))
                    as ij.
                {
                    apply of_grade_mult; [>|exact jv12].
                    apply of_grade_mult; [>exact iv11|].
                    apply of_grade_mult; apply vector_to_tensor_grade.
                }
                assert (i + 2 + j ≠ 1) as neq.
                {
                    intros contr.
                    rewrite (plus_comm i 2) in contr.
                    rewrite <- plus_assoc in contr.
                    inversion contr.
                }
                rewrite (grade_project_of_grade_neq _ _ _ ij neq).
                reflexivity.
Qed.

End ExteriorConstruct.
