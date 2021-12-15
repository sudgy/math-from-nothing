Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_algebra_grade.
Require Import tensor_algebra_mult1.
Require Import tensor_algebra_mult2.
Require Import tensor_power.
Require Import tensor_product_isomorphisms.
Require Import module_category.
Require Import algebra_category.

Require Import list.
Require Import set.
Require Import plus_sum.

(** This file contains facts about scalars in the tensor algebra, such as the
canonical injection and a few more facts about multiplication relating to
scalars.
*)

(* begin hide *)
Section TensorAlgebra.

Context {F : CRing} (V : Module F).

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
Let TAM := tensor_mult V.
Let TAML := tensor_mult_ldist V.
Let TAMR := tensor_mult_rdist V.
Let TAMA := tensor_mult_assoc V.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD TP TZ TN TPC
    TPA TPZ TPN TSM TSMC TSMO TSML TSMR TAP TAZ TAN TAPC TAPA TAPZ TAPN TASM
    TASMC TASMO TASML TASMR TAM TAML TAMR TAMA.
(* end hide *)
Let k_tensor k := module_V (tensor_power V k).

Definition scalar_to_tensor α := power_to_tensor V (k := 0) α.

Theorem scalar_to_tensor_eq : ∀ α β,
        scalar_to_tensor α = scalar_to_tensor β → α = β.
    intros α β eq.
    unfold scalar_to_tensor in eq.
    apply power_to_tensor_eq in eq.
    exact eq.
Qed.

Theorem scalar_to_tensor_plus : ∀ α β,
        scalar_to_tensor α + scalar_to_tensor β =
        scalar_to_tensor (α + β).
    intros α β.
    unfold scalar_to_tensor.
    rewrite (power_to_tensor_plus V).
    reflexivity.
Qed.

Theorem scalar_to_tensor_zero : scalar_to_tensor 0 = 0.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros x.
    unfold power_to_tensor_base.
    destruct (strong_excluded_middle (0 = x)) as [x_z|x_nz].
    -   subst.
        cbn.
        reflexivity.
    -   reflexivity.
Qed.

Theorem scalar_to_tensor_homogeneous : ∀ α,
        homogeneous_tensor V (scalar_to_tensor α).
    intros α.
    exists 0, α.
    reflexivity.
Qed.

Theorem scalar_to_tensor_decompose : ∀ α, 0 ≠ α →
        tensor_decompose_grade V (scalar_to_tensor α) =
        [_|scalar_to_tensor_homogeneous α] :: list_end.
    intros α α_neq.
    unfold tensor_decompose_grade.
    assert (tensor_max_nz V (scalar_to_tensor α) = 1) as nz_eq.
    {
        remember (tensor_max_nz V (scalar_to_tensor α)) as n.
        assert (0 < n) as ltq.
        {
            rewrite Heqn.
            apply tensor_max_nz_leq.
            intros contr.
            cbn in contr.
            unfold power_to_tensor_base in contr.
            destruct (strong_excluded_middle (0 = 0)) as [eq|neq];
                try contradiction.
            destruct eq; cbn in contr.
            contradiction.
        }
        nat_destruct n.
        -   destruct ltq; contradiction.
        -   pose proof (tensor_max_nz_least V _ _ Heqn) as neq.
            symmetry; classic_contradiction contr.
            apply neq; clear neq.
            cbn.
            unfold power_to_tensor_base; cbn.
            destruct (strong_excluded_middle (0 = n)) as [eq|neq].
            +   exfalso.
                subst n.
                contradiction.
            +   reflexivity.
    }
    rewrite nz_eq.
    unfold one; cbn.
    apply f_equal2.
    2: reflexivity.
    apply set_type_eq; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    unfold power_to_tensor_base.
    change nat_zero with (zero (U := nat)).
    case_if; reflexivity.
Qed.

Theorem scalar_to_tensor_mult : ∀ α β,
        scalar_to_tensor α * scalar_to_tensor β =
        scalar_to_tensor (α * β).
    intros α β.
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst α.
        rewrite scalar_to_tensor_zero.
        do 2 rewrite mult_lanni.
        rewrite scalar_to_tensor_zero.
        reflexivity.
    }
    classic_case (0 = β) as [β_z|β_nz].
    {
        subst β.
        rewrite scalar_to_tensor_zero.
        do 2 rewrite mult_ranni.
        rewrite scalar_to_tensor_zero.
        reflexivity.
    }
    unfold mult at 1; cbn.
    rewrite scalar_to_tensor_decompose by exact α_nz.
    rewrite scalar_to_tensor_decompose by exact β_nz.
    cbn.
    rewrite plus_rid.
    unfold scalar_to_tensor.
    rewrite power_to_tensor_tm.
    unfold zero at 8; cbn.
    destruct (Logic.eq_sym (plus_lid_rid_ 0)); cbn.
    fold (tensor_product_comm_f (tensor_power V 0) (cring_module F)).
    rewrite tensor_product_comm_eq.
    fold (tensor_product_lid_f (tensor_power V 0)).
    rewrite (tensor_product_lid_eq (tensor_power V 0)).
    unfold scalar_mult; cbn.
    unfold zero; cbn.
    rewrite mult_comm.
    reflexivity.
Qed.

Theorem scalar_to_tensor_scalar : ∀ α (A : tensor_algebra_base V),
        scalar_to_tensor α * A = α · A.
    intros α A.
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst α.
        rewrite scalar_to_tensor_zero.
        rewrite mult_lanni.
        rewrite scalar_lanni.
        reflexivity.
    }
    rewrite (tensor_decompose_grade_eq V A).
    remember (tensor_decompose_grade V A) as al.
    clear Heqal A.
    induction al.
    {
        cbn.
        rewrite mult_ranni.
        rewrite scalar_ranni.
        reflexivity.
    }
    cbn.
    rewrite ldist.
    rewrite scalar_ldist.
    rewrite IHal; clear IHal.
    apply rplus; clear al.
    unfold mult at 1; cbn.
    rewrite scalar_to_tensor_decompose by exact α_nz.
    rewrite list_prod2_lconc.
    rewrite list_prod2_lend.
    cbn.
    rewrite plus_lid.
    rewrite (tensor_rmult_homogeneous V).
    destruct a as [a a_homo]; cbn.
    destruct a_homo as [k [A A_eq]].
    subst a.
    unfold scalar_to_tensor.
    rewrite (power_to_tensor_tm V).
    rewrite tensor_power_lscalar.
    unfold scalar_mult at 2; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros x.
    unfold power_to_tensor_base.
    assert (strong_excluded_middle (0 + k = x) =
            strong_excluded_middle (k = x)) as eq_eq.
    {
        destruct (strong_excluded_middle (0 + k = x)) as [eq1|neq1];
        destruct (strong_excluded_middle (k = x)) as [eq2|neq2].
        -   apply f_equal.
            apply proof_irrelevance.
        -   exfalso; rewrite plus_lid in eq1.
            contradiction.
        -   exfalso; rewrite plus_lid in neq1.
            contradiction.
        -   apply f_equal.
            apply proof_irrelevance.
    }
    rewrite eq_eq; clear eq_eq.
    destruct (strong_excluded_middle (k = x)) as [eq|neq].
    -   subst; cbn.
        reflexivity.
    -   rewrite scalar_ranni.
        reflexivity.
Qed.

Theorem scalar_to_tensor_comm : ∀ α (A : tensor_algebra_base V),
        scalar_to_tensor α * A = A * scalar_to_tensor α.
    intros α A.
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst α.
        rewrite scalar_to_tensor_zero.
        rewrite mult_lanni.
        rewrite mult_ranni.
        reflexivity.
    }
    rewrite (tensor_decompose_grade_eq V A).
    remember (tensor_decompose_grade V A) as al.
    clear Heqal A.
    induction al.
    {
        cbn.
        rewrite mult_lanni.
        rewrite mult_ranni.
        reflexivity.
    }
    cbn.
    rewrite ldist.
    rewrite rdist.
    rewrite IHal; clear IHal.
    apply rplus; clear al.
    unfold mult; cbn.
    rewrite scalar_to_tensor_decompose by exact α_nz.
    rewrite list_prod2_lconc.
    rewrite list_prod2_lend.
    rewrite list_prod2_rconc.
    rewrite list_prod2_rend.
    cbn.
    do 2 rewrite plus_lid.
    rewrite (tensor_lmult_homogeneous V).
    rewrite (tensor_rmult_homogeneous V).
    destruct a as [a a_homo]; cbn.
    destruct a_homo as [k [A A_eq]].
    subst a.
    unfold scalar_to_tensor.
    do 2 rewrite (power_to_tensor_tm V).
    rewrite tensor_power_lscalar.
    rewrite <- tensor_power_rscalar.
    symmetry.
    apply power_to_tensor_k_eq.
Qed.

Program Instance tensor_scalar_lmult : ScalarLMult U (tensor_algebra_base V).
Next Obligation.
    do 2 rewrite <- scalar_to_tensor_scalar.
    rewrite mult_assoc.
    reflexivity.
Qed.

Program Instance tensor_scalar_rmult : ScalarRMult U (tensor_algebra_base V).
Next Obligation.
    do 2 rewrite <- scalar_to_tensor_scalar.
    do 2 rewrite mult_assoc.
    rewrite (scalar_to_tensor_comm _ u).
    reflexivity.
Qed.

Instance tensor_one : One (tensor_algebra_base V) := {
    one := scalar_to_tensor 1
}.

Program Instance tensor_mult_lid : MultLid (tensor_algebra_base V).
Next Obligation.
    unfold one; cbn.
    rewrite scalar_to_tensor_scalar.
    apply scalar_id.
Qed.

Program Instance tensor_mult_rid : MultRid (tensor_algebra_base V).
Next Obligation.
    unfold one; cbn.
    rewrite <- scalar_to_tensor_comm.
    rewrite scalar_to_tensor_scalar.
    apply scalar_id.
Qed.
(* begin hide *)
End TensorAlgebra.
(* end hide *)

Definition tensor_algebra_object {F : CRing} (V : Module F) := make_algebra F
    (make_module F
        (tensor_algebra_base V)
        (tensor_algebra_plus V)
        (tensor_algebra_zero V)
        (tensor_algebra_neg V)
        (tensor_algebra_plus_assoc V)
        (tensor_algebra_plus_comm V)
        (tensor_algebra_plus_lid V)
        (tensor_algebra_plus_linv V)
        (tensor_algebra_scalar_mult V)
        (tensor_algebra_scalar_id V)
        (tensor_algebra_scalar_ldist V)
        (tensor_algebra_scalar_rdist V)
        (tensor_algebra_scalar_comp V)
    )
    (tensor_mult V)
    (tensor_mult_ldist V)
    (tensor_mult_rdist V)
    (tensor_mult_assoc V)
    (tensor_one V)
    (tensor_mult_lid V)
    (tensor_mult_rid V)
    (tensor_scalar_lmult V)
    (tensor_scalar_rmult V)
.
