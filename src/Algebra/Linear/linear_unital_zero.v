Require Import init.

Require Export algebra_category.
Require Import linear_sum.

Section UnitalZeroAlgebra.

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
Local Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP VZ VN
    VPA VPC VPZ VPN VSM VSMO VSML VSMR VSMC.

Let UV_module := direct_sum (cring_module F) V.
Let UV := module_V UV_module.
Let UVP := module_plus UV_module.
Let UVZ := module_zero UV_module.
Let UVN := module_neg UV_module.
Let UVPA := module_plus_assoc UV_module.
Let UVPC := module_plus_comm UV_module.
Let UVPZ := module_plus_lid UV_module.
Let UVPN := module_plus_linv UV_module.
Let UVSM := module_scalar UV_module.
Let UVSMO := module_scalar_id UV_module.
Let UVSML := module_scalar_ldist UV_module.
Let UVSMR := module_scalar_rdist UV_module.
Local Existing Instances UVP UVZ UVN UVPA UVPC UVPZ UVPN UVSM UVSMO UVSML UVSMR.

Local Instance unital_zero_mult : Mult UV := {
    mult a b := (fst a * fst b, fst a · snd b + fst b · snd a)
}.

Local Instance unital_zero_mult_assoc : MultAssoc UV.
Proof.
    split.
    intros [a1 a2] [b1 b2] [c1 c2].
    unfold mult; cbn.
    rewrite mult_assoc.
    do 2 rewrite scalar_ldist.
    do 4 rewrite scalar_comp.
    rewrite plus_assoc.
    rewrite (mult_comm a1 c1).
    rewrite (mult_comm b1 c1).
    reflexivity.
Qed.

Local Instance unital_zero_mult_comm : MultComm UV.
Proof.
    split.
    intros [a1 a2] [b1 b2].
    unfold mult; cbn.
    rewrite plus_comm.
    rewrite mult_comm.
    reflexivity.
Qed.

Local Instance unital_zero_ldist : Ldist UV.
Proof.
    split.
    intros [a1 a2] [b1 b2] [c1 c2].
    unfold mult; cbn.
    unfold plus at 1 3 4 5; cbn.
    rewrite ldist, scalar_ldist, scalar_rdist.
    apply f_equal.
    apply plus_4.
Qed.

Local Instance unital_zero_one : One UV := {
    one := (1, 0)
}.

Local Instance unital_zero_mult_lid : MultLid UV.
Proof.
    split.
    intros [a1 a2].
    unfold one, mult; cbn.
    rewrite mult_lid, scalar_id.
    rewrite scalar_ranni, plus_rid.
    reflexivity.
Qed.

Local Instance unital_zero_scalar_lmult : ScalarLMult U UV.
Proof.
    split.
    intros a [u1 u2] [v1 v2].
    unfold scalar_mult, mult; cbn.
    unfold scalar_mult at 1 3 6; cbn.
    rewrite mult_assoc.
    rewrite scalar_ldist.
    do 3 rewrite scalar_comp.
    rewrite (mult_comm a v1).
    reflexivity.
Qed.

Local Instance unital_zero_scalar_rmult : ScalarRMult U UV.
Proof.
    split.
    intros a u v.
    do 2 rewrite (mult_comm u).
    apply scalar_lmult.
Qed.

Definition unital_zero_algebra := make_algebra F UV_module
    unital_zero_mult
    unital_zero_ldist
    ldist_rdist
    unital_zero_mult_assoc
    unital_zero_one
    unital_zero_mult_lid
    mult_lid_rid
    unital_zero_scalar_lmult
    unital_zero_scalar_rmult.

End UnitalZeroAlgebra.
