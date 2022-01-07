Require Import init.

Require Import module_category.
Require Import algebra_category.
Require Import tensor_algebra.
Require Import linear_quadratic.

Require Import ring_ideal.

Require Import set.
Require Import unordered_list.

Section GeometricConstruct.

Context {F : CRing} {V : Module F}.

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

Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UR UMC UMO VP VZ VN VPA VPC
    VPZ VPN VSM VSMO VSMR TAP TAZ TAN TAPA TAPC TAPZ TAPN TASM TASMO TASMC TASL
    TASR TASLM TASRM TAM TAO TAL TAR TAMA TAML TAMR.

Context (Q : set_type (quadratic_form (cring_U F) (module_V V))).

Definition ga_ideal_base (x : algebra_V (tensor_algebra V)) :=
    ∃ v, x = vector_to_tensor v * vector_to_tensor v - [Q|] v · 1.

Definition ga_ideal := ideal_generated_by ga_ideal_base.

Definition ga := quotient_ring ga_ideal.
Definition ga_plus := quotient_ring_plus ga_ideal.
Definition ga_plus_assoc := quotient_ring_plus_assoc ga_ideal.
Definition ga_plus_comm := quotient_ring_plus_comm ga_ideal.
Definition ga_zero := quotient_ring_zero ga_ideal.
Definition ga_plus_lid := quotient_ring_plus_lid ga_ideal.
Definition ga_neg := quotient_ring_neg ga_ideal.
Definition ga_plus_linv := quotient_ring_plus_linv ga_ideal.
Definition ga_mult := quotient_ring_mult ga_ideal.
Definition ga_ldist := quotient_ring_ldist ga_ideal.
Definition ga_rdist := quotient_ring_rdist ga_ideal.
Definition ga_mult_assoc := quotient_ring_mult_assoc ga_ideal.
Definition ga_one := quotient_ring_one ga_ideal.
Definition ga_mult_lid := quotient_ring_mult_lid ga_ideal.
Definition ga_mult_rid := quotient_ring_mult_rid ga_ideal.

Existing Instances ga_plus ga_plus_assoc ga_plus_comm ga_zero ga_plus_lid ga_neg
    ga_plus_linv ga_mult ga_ldist ga_rdist ga_mult_assoc ga_one ga_mult_lid
    ga_mult_rid.

Lemma ga_scalar_wd : ∀ u v c, eq_equal (ideal_equiv ga_ideal) u v →
        eq_equal (ideal_equiv ga_ideal) (c · u) (c · v).
    cbn.
    change (ideal_generated_by_set ga_ideal_base) with (ideal_set ga_ideal).
    intros u v c eq.
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    rewrite <- (scalar_to_tensor_scalar V).
    apply (ideal_lmult ga_ideal).
    exact eq.
Qed.

Instance ga_scalar : ScalarMult (cring_U F) ga := {
    scalar_mult := binary_rself_op ga_scalar_wd
}.

Program Instance ga_scalar_id : ScalarId (cring_U F) ga.
Next Obligation.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_id.
Qed.

Program Instance ga_scalar_ldist : ScalarLdist (cring_U F) ga.
Next Obligation.
    equiv_get_value u v.
    unfold scalar_mult, plus; equiv_simpl.
    apply f_equal.
    apply scalar_ldist.
Qed.

Program Instance ga_scalar_rdist : ScalarRdist (cring_U F) ga.
Next Obligation.
    equiv_get_value v.
    unfold scalar_mult, plus at 2; equiv_simpl.
    apply f_equal.
    apply scalar_rdist.
Qed.

Program Instance ga_scalar_comp : ScalarComp (cring_U F) ga.
Next Obligation.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_comp.
Qed.

Program Instance ga_scalar_lmult : ScalarLMult (cring_U F) ga.
Next Obligation.
    equiv_get_value u v.
    unfold scalar_mult, mult; equiv_simpl.
    apply f_equal.
    apply scalar_lmult.
Qed.

Program Instance ga_scalar_rmult : ScalarRMult (cring_U F) ga.
Next Obligation.
    equiv_get_value u v.
    unfold scalar_mult, mult; equiv_simpl.
    apply f_equal.
    apply scalar_rmult.
Qed.

Definition geometric_algebra := make_algebra F
    (make_module F
        ga
        ga_plus
        ga_zero
        ga_neg
        ga_plus_assoc
        ga_plus_comm
        ga_plus_lid
        ga_plus_linv
        ga_scalar
        ga_scalar_id
        ga_scalar_ldist
        ga_scalar_rdist
        ga_scalar_comp
    )
    ga_mult
    ga_ldist
    ga_rdist
    ga_mult_assoc
    ga_one
    ga_mult_lid
    ga_mult_rid
    ga_scalar_lmult
    ga_scalar_rmult.

Definition to_ga v := to_equiv_type (ideal_equiv ga_ideal) v.

Theorem to_ga_plus : ∀ u v, to_ga (u + v) = to_ga u + to_ga v.
    intros u v.
    unfold to_ga, plus at 2; equiv_simpl.
    rewrite plus_rinv.
    exact (ideal_zero ga_ideal).
Qed.

Theorem to_ga_mult : ∀ u v, to_ga (u * v) = to_ga u * to_ga v.
    intros u v.
    unfold to_ga, mult at 2; equiv_simpl.
    rewrite plus_rinv.
    exact (ideal_zero ga_ideal).
Qed.

Theorem to_ga_scalar : ∀ a v, to_ga (a · v) = a · to_ga v.
    intros a v.
    unfold to_ga, scalar_mult at 2; equiv_simpl.
    rewrite plus_rinv.
    exact (ideal_zero ga_ideal).
Qed.

Theorem to_ga_zero : to_ga 0 = 0.
    reflexivity.
Qed.

Definition vector_to_ga v := to_ga (vector_to_tensor v).

Theorem vector_to_ga_plus :
        ∀ u v, vector_to_ga (u + v) = vector_to_ga u + vector_to_ga v.
    intros u v.
    unfold vector_to_ga.
    rewrite (vector_to_tensor_plus V).
    apply to_ga_plus.
Qed.

Theorem vector_to_ga_scalar : ∀ a v, vector_to_ga (a · v) = a · vector_to_ga v.
    intros a v.
    unfold vector_to_ga.
    rewrite (vector_to_tensor_scalar V).
    apply to_ga_scalar.
Qed.

Theorem vector_to_ga_zero : vector_to_ga 0 = 0.
    unfold vector_to_ga.
    unfold VZ.
    rewrite (vector_to_tensor_zero V).
    apply to_ga_zero.
Qed.

Theorem vector_to_ga_neg : ∀ v, vector_to_ga (-v) = -vector_to_ga v.
    intros v.
    rewrite <- scalar_neg_one.
    rewrite vector_to_ga_scalar.
    apply scalar_neg_one.
Qed.

Definition scalar_to_ga a := to_ga (scalar_to_tensor V a).

Theorem scalar_to_ga_plus : ∀ a b,
        scalar_to_ga (a + b) = scalar_to_ga a + scalar_to_ga b.
    intros a b.
    unfold scalar_to_ga.
    rewrite (scalar_to_tensor_plus V).
    apply to_ga_plus.
Qed.

Theorem scalar_to_ga_zero : scalar_to_ga 0 = 0.
    unfold scalar_to_ga.
    unfold UZ.
    rewrite (scalar_to_tensor_zero V).
    apply to_ga_zero.
Qed.

Theorem scalar_to_ga_mult : ∀ a b,
        scalar_to_ga (a * b) = scalar_to_ga a * scalar_to_ga b.
    intros a b.
    unfold scalar_to_ga.
    rewrite (scalar_to_tensor_mult V).
    apply to_ga_mult.
Qed.

Theorem scalar_to_ga_scalar : ∀ a A, scalar_to_ga a * A = a · A.
    intros a A.
    equiv_get_value A.
    unfold scalar_to_ga, to_ga, mult, scalar_mult; equiv_simpl.
    rewrite (scalar_to_tensor_scalar V).
    rewrite plus_rinv.
    exact (ideal_zero ga_ideal).
Qed.

Theorem scalar_to_ga_neg : ∀ a, scalar_to_ga (-a) = -scalar_to_ga a.
    intros a.
    rewrite <- mult_neg_one.
    rewrite scalar_to_ga_mult.
    rewrite scalar_to_ga_scalar.
    apply scalar_neg_one.
Qed.

Theorem scalar_to_ga_one : scalar_to_ga 1 = 1.
    unfold scalar_to_ga.
    unfold UO.
    rewrite (scalar_to_tensor_one V).
    reflexivity.
Qed.

Theorem scalar_to_ga_comm : ∀ a A, scalar_to_ga a * A = A * scalar_to_ga a.
    intros a A.
    equiv_get_value A.
    unfold scalar_to_ga, to_ga, mult; equiv_simpl.
    rewrite (scalar_to_tensor_comm V).
    rewrite plus_rinv.
    exact (ideal_zero ga_ideal).
Qed.

Theorem scalar_to_ga_one_scalar : ∀ a, scalar_to_ga a = a · 1.
    intros a.
    rewrite <- (mult_rid (scalar_to_ga a)).
    apply scalar_to_ga_scalar.
Qed.

Theorem ga_contract :
        ∀ v, vector_to_ga v * vector_to_ga v = scalar_to_ga ([Q|] v).
    intros v.
    unfold vector_to_ga, scalar_to_ga, to_ga, mult; equiv_simpl.
    assert (ga_ideal_base (vector_to_tensor v * vector_to_tensor v -
        scalar_to_tensor V ([Q|] v))) as v2_in.
    {
        exists v.
        rewrite <- (scalar_to_tensor_scalar V).
        rewrite mult_rid.
        reflexivity.
    }
    exists (((1, 1), [_|v2_in]) ::: ulist_end).
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ulist_image_end, ulist_sum_end.
    rewrite plus_rid, mult_lid, mult_rid.
    reflexivity.
Qed.

End GeometricConstruct.
