Require Import init.

Require Import tensor_algebra_defs.
Require Export tensor_algebra_base.
Require Import linear_unital_zero.
Require Import set.
Require Import list.

Section TensorAlgebraInclusions.

Context {F : CRingObj} (V : ModuleObj F).
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
Let VPA := module_plus_assoc V.
Let VPC := module_plus_comm V.
Let VPZ := module_plus_lid V.
Let VPN := module_plus_linv V.
Let VSM := module_scalar V.
Let VSMO := module_scalar_id V.
Let VSML := module_scalar_ldist V.
Let VSMR := module_scalar_rdist V.
Let VSMC := module_scalar_comp V.
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

Local Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP VZ VN
    VPA VPC VPZ VPN VSM VSMO VSMR TAP TAZ TAN TAPA TAPC TAPZ TAPN TASM TASMO
    TASMC TASL TASR TASLM TASRM TAM TAO TAL TAR TAMA TAML TAMR.

Let UVAP := algebra_plus (unital_zero_algebra V).
Let UVAZ := algebra_zero (unital_zero_algebra V).
Let UVAN := algebra_neg (unital_zero_algebra V).
Let UVAPA := algebra_plus_assoc (unital_zero_algebra V).
Let UVAPC := algebra_plus_comm (unital_zero_algebra V).
Let UVAPZ := algebra_plus_lid (unital_zero_algebra V).
Let UVAPN := algebra_plus_linv (unital_zero_algebra V).
Let UVASM := algebra_scalar (unital_zero_algebra V).
Let UVASMO := algebra_scalar_id (unital_zero_algebra V).
Let UVASMC := algebra_scalar_comp (unital_zero_algebra V).
Let UVASL := algebra_scalar_ldist (unital_zero_algebra V).
Let UVASR := algebra_scalar_rdist (unital_zero_algebra V).
Let UVASLM := algebra_scalar_lmult (unital_zero_algebra V).
Let UVASRM := algebra_scalar_rmult (unital_zero_algebra V).
Let UVAM := algebra_mult (unital_zero_algebra V).
Let UVAO := algebra_one (unital_zero_algebra V).
Let UVAL := algebra_ldist (unital_zero_algebra V).
Let UVAR := algebra_rdist (unital_zero_algebra V).
Let UVAMA := algebra_mult_assoc (unital_zero_algebra V).
Let UVAML := algebra_mult_lid (unital_zero_algebra V).
Let UVAMR := algebra_mult_rid (unital_zero_algebra V).

Local Existing Instances UVAP UVAZ UVAN UVAPA UVAPC UVAPZ UVAPN UVASM UVASMO
    UVASMC UVASL UVASR UVASLM UVASRM UVAM UVAO UVAL UVAR UVAMA UVAML UVAMR.

Let to_uz (v : module_V V) : algebra_V (unital_zero_algebra V) := (0, v).

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

Let to_uz_homo := make_module_homomorphism
    F
    V
    (algebra_module (unital_zero_algebra V))
    to_uz
    to_uz_plus
    to_uz_scalar.

Let to_uz_base := make_to_algebra
    V
    (unital_zero_algebra V)
    to_uz_homo.

Let tensor_to_uz_base := ex_singleton (tensor_algebra_universal V to_uz_base).
Let tensor_to_uz_homo := [tensor_to_uz_base|].
Let tensor_to_uz := algebra_homo_f tensor_to_uz_homo.

Theorem vector_to_tensor_eq : ∀ a b : module_V V,
    vector_to_tensor a = vector_to_tensor b → a = b.
Proof.
    intros a b eq.
    apply (f_equal tensor_to_uz) in eq.
    pose proof [|tensor_to_uz_base] as to_uz_eq.
    unfold to_algebra_set in to_uz_eq; cbn in to_uz_eq.
    unfold tensor_to_uz in eq.
    do 2 rewrite to_uz_eq in eq.
    inversion eq.
    reflexivity.
Qed.

Theorem scalar_to_tensor_eq : ∀ a b : U,
    scalar_to_tensor V a = scalar_to_tensor V b → a = b.
Proof.
    intros a b eq.
    apply (f_equal tensor_to_uz) in eq.
    unfold scalar_to_tensor in eq.
    unfold tensor_to_uz in eq.
    do 2 rewrite algebra_homo_scalar in eq.
    rewrite algebra_homo_one in eq.
    unfold one, scalar_mult in eq; cbn in eq.
    unfold scalar_mult at 1 3 in eq; cbn in eq.
    do 2 rewrite mult_rid in eq.
    inversion eq.
    reflexivity.
Qed.

End TensorAlgebraInclusions.
