Require Import init.

Require Export module_category.
Require Export algebra_category.
Require Import tensor_algebra.
Require Export linear_bilinear_form.

Require Import ring_ideal.

Require Export set.
Require Export unordered_list.

Declare Scope geo_scope.
Delimit Scope geo_scope with geo.

(* begin hide *)
Section GeometricConstruct.

(* end hide *)
Context {F : CRingObj} {V : ModuleObj F}.
(* begin hide *)

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

Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UR UMC UMO.
Existing Instances VP VZ VN VPA VPC VPZ VPN VSM VSMO VSMR.

(* end hide *)
Context (B : set_type bilinear_form).

(* begin hide *)
Existing Instances TAP TAZ TAN TAPA TAPC TAPZ TAPN TASM TASMO TASMC TASL TASR
    TASLM TASRM TAM TAO TAL TAR TAMA TAML TAMR.

(* end hide *)
Definition geo_ideal_base (x : algebra_V (tensor_algebra V)) :=
    ∃ v, x = vector_to_tensor v * vector_to_tensor v - [B|] v v · 1.

Definition geo_ideal := ideal_generated_by geo_ideal_base.

Definition geo := quotient_ring geo_ideal.
Definition geo_plus := quotient_ring_plus geo_ideal.
Definition geo_plus_assoc := quotient_ring_plus_assoc geo_ideal.
Definition geo_plus_comm := quotient_ring_plus_comm geo_ideal.
Definition geo_zero := quotient_ring_zero geo_ideal.
Definition geo_plus_lid := quotient_ring_plus_lid geo_ideal.
Definition geo_neg := quotient_ring_neg geo_ideal.
Definition geo_plus_linv := quotient_ring_plus_linv geo_ideal.
Definition geo_mult := quotient_ring_mult geo_ideal.
Definition geo_ldist := quotient_ring_ldist geo_ideal.
Definition geo_rdist := quotient_ring_rdist geo_ideal.
Definition geo_mult_assoc := quotient_ring_mult_assoc geo_ideal.
Definition geo_one := quotient_ring_one geo_ideal.
Definition geo_mult_lid := quotient_ring_mult_lid geo_ideal.
Definition geo_mult_rid := quotient_ring_mult_rid geo_ideal.

(* begin hide *)
Existing Instances geo_plus geo_plus_assoc geo_plus_comm geo_zero geo_plus_lid
    geo_neg geo_plus_linv geo_mult geo_ldist geo_rdist geo_mult_assoc geo_one
    geo_mult_lid geo_mult_rid.

(* end hide *)
Lemma geo_scalar_wd : ∀ c u v, eq_equal (ideal_equiv geo_ideal) u v →
    eq_equal (ideal_equiv geo_ideal) (c · u) (c · v).
Proof.
    cbn.
    change (ideal_generated_by_set geo_ideal_base) with (ideal_set geo_ideal).
    intros c u v eq.
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    rewrite <- (scalar_to_tensor_scalar V).
    apply (ideal_lmult geo_ideal).
    exact eq.
Qed.

Instance geo_scalar : ScalarMult (cring_U F) geo := {
    scalar_mult c := unary_op (unary_self_wd (geo_scalar_wd c))
}.

Program Instance geo_scalar_id : ScalarId (cring_U F) geo.
Next Obligation.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_id.
Qed.

Program Instance geo_scalar_ldist : ScalarLdist (cring_U F) geo.
Next Obligation.
    equiv_get_value u v.
    unfold scalar_mult, plus; equiv_simpl.
    apply f_equal.
    apply scalar_ldist.
Qed.

Program Instance geo_scalar_rdist : ScalarRdist (cring_U F) geo.
Next Obligation.
    equiv_get_value v.
    unfold scalar_mult, plus at 2; equiv_simpl.
    apply f_equal.
    apply scalar_rdist.
Qed.

Program Instance geo_scalar_comp : ScalarComp (cring_U F) geo.
Next Obligation.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_comp.
Qed.

Program Instance geo_scalar_lmult : ScalarLMult (cring_U F) geo.
Next Obligation.
    equiv_get_value u v.
    unfold scalar_mult, mult; equiv_simpl.
    apply f_equal.
    apply scalar_lmult.
Qed.

Program Instance geo_scalar_rmult : ScalarRMult (cring_U F) geo.
Next Obligation.
    equiv_get_value u v.
    unfold scalar_mult, mult; equiv_simpl.
    apply f_equal.
    apply scalar_rmult.
Qed.

Definition geometric_algebra := make_algebra F
    (make_module F
        geo
        geo_plus
        geo_zero
        geo_neg
        geo_plus_assoc
        geo_plus_comm
        geo_plus_lid
        geo_plus_linv
        geo_scalar
        geo_scalar_id
        geo_scalar_ldist
        geo_scalar_rdist
        geo_scalar_comp
    )
    geo_mult
    geo_ldist
    geo_rdist
    geo_mult_assoc
    geo_one
    geo_mult_lid
    geo_mult_rid
    geo_scalar_lmult
    geo_scalar_rmult.

Definition tensor_to_geo v := to_equiv (ideal_equiv geo_ideal) v : geo.

Theorem tensor_to_geo_plus : ∀ u v, tensor_to_geo (u + v) = tensor_to_geo u + tensor_to_geo v.
Proof.
    intros u v.
    unfold tensor_to_geo, plus at 2; equiv_simpl.
    apply equiv_eq; cbn.
    rewrite plus_rinv.
    exact (ideal_zero geo_ideal).
Qed.

Theorem tensor_to_geo_mult : ∀ u v, tensor_to_geo (u * v) = tensor_to_geo u * tensor_to_geo v.
Proof.
    intros u v.
    unfold tensor_to_geo, mult at 2; equiv_simpl.
    apply equiv_eq; cbn.
    rewrite plus_rinv.
    exact (ideal_zero geo_ideal).
Qed.

Theorem tensor_to_geo_scalar : ∀ a v, tensor_to_geo (a · v) = a · tensor_to_geo v.
Proof.
    intros a v.
    unfold tensor_to_geo, scalar_mult at 2; equiv_simpl.
    apply equiv_eq; cbn.
    rewrite plus_rinv.
    exact (ideal_zero geo_ideal).
Qed.

Theorem tensor_to_geo_zero : tensor_to_geo 0 = 0.
Proof.
    reflexivity.
Qed.

Definition vector_to_geo v := tensor_to_geo (vector_to_tensor v).
Local Notation "'φ'" := vector_to_geo.

Theorem vector_to_geo_plus : ∀ u v, φ (u + v) = φ u + φ v.
Proof.
    intros u v.
    unfold vector_to_geo.
    rewrite (vector_to_tensor_plus V).
    apply tensor_to_geo_plus.
Qed.

Theorem vector_to_geo_scalar : ∀ a v, φ (a · v) = a · φ v.
Proof.
    intros a v.
    unfold vector_to_geo.
    rewrite (vector_to_tensor_scalar V).
    apply tensor_to_geo_scalar.
Qed.

Theorem vector_to_geo_zero : φ 0 = 0.
Proof.
    unfold vector_to_geo.
    rewrite vector_to_tensor_zero.
    apply tensor_to_geo_zero.
Qed.

Theorem vector_to_geo_neg : ∀ v, φ (-v) = -φ v.
Proof.
    intros v.
    rewrite <- scalar_neg_one.
    rewrite vector_to_geo_scalar.
    apply scalar_neg_one.
Qed.

Definition scalar_to_geo a := tensor_to_geo (scalar_to_tensor V a).
Local Notation "'σ'" := scalar_to_geo.

Theorem scalar_to_geo_plus : ∀ a b, σ (a + b) = σ a + σ b.
Proof.
    intros a b.
    unfold scalar_to_geo.
    rewrite (scalar_to_tensor_plus V).
    apply tensor_to_geo_plus.
Qed.

Theorem scalar_to_geo_zero : σ 0 = 0.
Proof.
    unfold scalar_to_geo.
    rewrite scalar_to_tensor_zero.
    apply tensor_to_geo_zero.
Qed.

Theorem scalar_to_geo_mult : ∀ a b, σ (a * b) = σ a * σ b.
Proof.
    intros a b.
    unfold scalar_to_geo.
    rewrite scalar_to_tensor_mult.
    apply tensor_to_geo_mult.
Qed.

Theorem scalar_to_geo_scalar : ∀ a A, σ a * A = a · A.
Proof.
    intros a A.
    equiv_get_value A.
    unfold scalar_to_geo, tensor_to_geo, mult, scalar_mult; equiv_simpl.
    apply equiv_eq; cbn.
    rewrite scalar_to_tensor_scalar.
    rewrite plus_rinv.
    exact (ideal_zero geo_ideal).
Qed.

Theorem scalar_to_geo_neg : ∀ a, σ (-a) = -σ a.
Proof.
    intros a.
    rewrite <- mult_neg_one.
    rewrite scalar_to_geo_mult.
    rewrite scalar_to_geo_scalar.
    apply scalar_neg_one.
Qed.

Theorem scalar_to_geo_one : σ 1 = 1.
Proof.
    unfold scalar_to_geo.
    rewrite scalar_to_tensor_one.
    reflexivity.
Qed.

Theorem scalar_to_geo_comm : ∀ a A, σ a * A = A * σ a.
Proof.
    intros a A.
    equiv_get_value A.
    unfold scalar_to_geo, tensor_to_geo, mult; equiv_simpl.
    apply equiv_eq; cbn.
    rewrite scalar_to_tensor_comm.
    rewrite plus_rinv.
    exact (ideal_zero geo_ideal).
Qed.

Theorem scalar_to_geo_one_scalar : ∀ a, σ a = a · 1.
Proof.
    intros a.
    rewrite <- (mult_rid (σ a)).
    apply scalar_to_geo_scalar.
Qed.

Theorem geo_contract : ∀ v, φ v * φ v = [B|] v v · 1.
Proof.
    intros v.
    rewrite <- scalar_to_geo_one_scalar.
    unfold vector_to_geo, scalar_to_geo, tensor_to_geo, mult, scalar_mult, one;
        equiv_simpl.
    apply equiv_eq; cbn.
    assert (geo_ideal_base (vector_to_tensor v * vector_to_tensor v -
        scalar_to_tensor V ([B|] v v))) as v2_in.
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

Theorem geo_sum : ∀ x, ∃ l : ulist (cring_U F * list (module_V V)),
    x = ulist_sum (ulist_image l (λ p, fst p · list_prod
        (list_image (snd p) (λ v, φ v)))).
Proof.
    intros x.
    equiv_get_value x.
    change (to_equiv _ x) with (tensor_to_geo x).
    pose proof (tensor_sum V x) as [l l_eq]; subst x.
    exists l.
    induction l using ulist_induction.
    {
        do 2 rewrite ulist_image_end, ulist_sum_end.
        apply tensor_to_geo_zero.
    }
    do 2 rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite tensor_to_geo_plus.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    destruct a as [a l]; cbn.
    rewrite tensor_to_geo_scalar.
    apply f_equal; clear a.
    induction l.
    {
        cbn.
        reflexivity.
    }
    cbn.
    rewrite tensor_to_geo_mult.
    rewrite IHl; clear IHl.
    reflexivity.
Qed.
(* begin hide *)

End GeometricConstruct.
(* end hide *)
