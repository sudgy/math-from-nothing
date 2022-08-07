Require Import init.

Require Import tensor_product_universal.
Require Import tensor_product_isomorphisms.
Require Import tensor_power_base.
Require Export tensor_algebra_base.
Require Import tensor_algebra_mult.
Require Import module_category.
Require Import algebra_category.
Require Import linear_grade.

Require Import set.
Require Import plus_sum.

(** This file constructs the canonical injection of vectors into the tensor
algebra and the basic facts about it.
*)

(* begin hide *)
Section TensorAlgebraObj.

(* end hide *)
Context {F : CRingObj} (V : ModuleObj F).

(* begin hide *)
Let U := cring_U F.
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Let VP := module_plus V.
Let VZ := module_zero V.
Let VN := module_neg V.
Let VPC := module_plus_comm V.
Let VPA := module_plus_assoc V.
Let VPZ := module_plus_lid V.
Let VPN := module_plus_linv V.
Let VSM := module_scalar V.
Let VSMC := module_scalar_comp V.
Let VSMO := module_scalar_id V.
Let VSML := module_scalar_ldist V.
Let VSMR := module_scalar_rdist V.
Let TP k := module_plus (tensor_power V k).
Let TZ k := module_zero (tensor_power V k).
Let TN k := module_neg (tensor_power V k).
Let TPC k := module_plus_comm (tensor_power V k).
Let TPA k := module_plus_assoc (tensor_power V k).
Let TPZ k := module_plus_lid (tensor_power V k).
Let TPN k := module_plus_linv (tensor_power V k).
Let TSM k := module_scalar (tensor_power V k).
Let TSMC k := module_scalar_comp (tensor_power V k).
Let TSMO k := module_scalar_id (tensor_power V k).
Let TSML k := module_scalar_ldist (tensor_power V k).
Let TSMR k := module_scalar_rdist (tensor_power V k).
Let TAP := tensor_algebra_plus V.
Let TAZ := tensor_algebra_zero V.
Let TAN := tensor_algebra_neg V.
Let TAPC := tensor_algebra_plus_comm V.
Let TAPA := tensor_algebra_plus_assoc V.
Let TAPZ := tensor_algebra_plus_lid V.
Let TAPN := tensor_algebra_plus_linv V.
Let TASM := tensor_algebra_scalar_mult V.
Let TASMC := tensor_algebra_scalar_comp V.
Let TASMO := tensor_algebra_scalar_id V.
Let TASML := tensor_algebra_scalar_ldist V.
Let TASMR := tensor_algebra_scalar_rdist V.
Let TAG := tensor_grade V.
Let TAM := tensor_mult_class V.
Let TAML := tensor_mult_ldist V.
Let TAMR := tensor_mult_rdist V.
Let TAMA := tensor_mult_assoc V.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP VZ VN VPC
    VPA VPZ VPN VSM VSMC VSMO VSML VSMR TP TZ TN TPC TPA TPZ TPN TSM TSMC TSMO
    TSML TSMR TAP TAZ TAN TAPC TAPA TAPZ TAPN TASM TASMC TASMO TASML TASMR TAG
    TAM TAML TAMR TAMA.
(* end hide *)
Let k_tensor k := module_V (tensor_power V k).

Definition vector_to_tensor v := power_to_tensor V (k := 1)
    (tensor_mult V (cring_module F) v 1).

Theorem vector_to_tensor_eq : ∀ u v,
    vector_to_tensor u = vector_to_tensor v → u = v.
Proof.
    intros u v eq.
    unfold vector_to_tensor in eq.
    apply power_to_tensor_eq in eq.
    apply (f_equal (tensor_product_rid_f V)) in eq.
    do 2 rewrite tensor_product_rid_eq in eq.
    pose (X := module_scalar_id V).
    do 2 rewrite scalar_id in eq.
    exact eq.
Qed.

Theorem vector_to_tensor_plus : ∀ u v,
    vector_to_tensor (u + v) = vector_to_tensor u + vector_to_tensor v.
Proof.
    intros u v.
    unfold vector_to_tensor.
    rewrite (tensor_rdist V).
    rewrite (power_to_tensor_plus V).
    reflexivity.
Qed.

Theorem vector_to_tensor_scalar : ∀ α v,
    vector_to_tensor (α · v) = α · vector_to_tensor v.
Proof.
    intros α v.
    unfold vector_to_tensor.
    rewrite (tensor_lscalar V).
    rewrite (power_to_tensor_scalar V).
    reflexivity.
Qed.

Theorem vector_to_tensor_zero : vector_to_tensor 0 = 0.
Proof.
    rewrite <- (scalar_lanni 0).
    rewrite vector_to_tensor_scalar.
    rewrite scalar_lanni.
    reflexivity.
Qed.

Theorem vector_to_tensor_homogeneous : ∀ v, homogeneous (vector_to_tensor v).
Proof.
    intros v.
    exists 1, (tensor_mult V (cring_module F) v 1).
    reflexivity.
Qed.
(* begin hide *)

End TensorAlgebraObj.
(* end hide *)
