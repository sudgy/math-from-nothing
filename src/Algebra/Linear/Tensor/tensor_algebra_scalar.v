Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_algebra_grade.
Require Import tensor_algebra_mult.
Require Import tensor_power_base.
Require Import tensor_product_isomorphisms.
Require Import module_category.
Require Import algebra_category.
Require Import linear_grade.

Require Import unordered_list.
Require Import set.
Require Import plus_sum.

(** This file contains facts about scalars in the tensor algebra, such as the
canonical injection and a few more facts about multiplication relating to
scalars.
*)

(* begin hide *)
Section TensorAlgebra.

(* end hide *)
Context {F : CRing} (V : Module F).

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
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD TP TZ TN TPC
    TPA TPZ TPN TSM TSMC TSMO TSML TSMR TAP TAZ TAN TAPC TAPA TAPZ TAPN TASM
    TASMC TASMO TASML TASMR TAG TAM TAML TAMR TAMA.
(* end hide *)
Let k_tensor k := module_V (tensor_power V k).

Definition scalar_to_tensor ?? := power_to_tensor V (k := 0) ??.

Theorem scalar_to_tensor_eq : ??? ?? ??,
        scalar_to_tensor ?? = scalar_to_tensor ?? ??? ?? = ??.
    intros ?? ?? eq.
    unfold scalar_to_tensor in eq.
    apply power_to_tensor_eq in eq.
    exact eq.
Qed.

Theorem scalar_to_tensor_plus : ??? ?? ??,
        scalar_to_tensor (?? + ??) =
        scalar_to_tensor ?? + scalar_to_tensor ??.
    intros ?? ??.
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

Theorem scalar_to_tensor_homogeneous : ??? ??, homogeneous (scalar_to_tensor ??).
    intros ??.
    exists 0, ??.
    reflexivity.
Qed.

Theorem scalar_to_tensor_mult : ??? ?? ??,
        scalar_to_tensor (?? * ??) =
        scalar_to_tensor ?? * scalar_to_tensor ??.
    intros ?? ??.
    assert (of_grade 0 (scalar_to_tensor ??)) as ??0.
    {
        exists ??.
        reflexivity.
    }
    assert (of_grade 0 (scalar_to_tensor ??)) as ??0.
    {
        exists ??.
        reflexivity.
    }
    rewrite (tensor_mult_homo _ _ _ _ _ ??0 ??0).
    rewrite power_to_tensor_tm.
    unfold zero at 9; cbn.
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

Theorem scalar_to_tensor_scalar : ??? ?? (A : tensor_algebra_base V),
        scalar_to_tensor ?? * A = ?? ?? A.
    intros ?? A.
    rewrite (grade_decomposition_eq A).
    remember (grade_decomposition A) as al.
    clear Heqal A.
    induction al using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_ranni.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite ldist.
    rewrite scalar_ldist.
    rewrite IHal; clear IHal.
    apply rplus; clear al.
    assert (of_grade 0 (scalar_to_tensor ??)) as ??0.
    {
        exists ??.
        reflexivity.
    }
    destruct a as [a [i ai]]; cbn.
    rewrite (tensor_mult_homo _ _ _ _ _ ??0 ai).
    pose proof ai as [a' a_eq].
    subst a; cbn.
    unfold scalar_to_tensor.
    rewrite power_to_tensor_tm.
    rewrite tensor_power_lscalar.
    apply power_to_tensor_scalar.
Qed.

Theorem scalar_to_tensor_comm : ??? ?? (A : tensor_algebra_base V),
        scalar_to_tensor ?? * A = A * scalar_to_tensor ??.
    intros ?? A.
    rewrite (grade_decomposition_eq A).
    remember (grade_decomposition A) as al.
    clear Heqal A.
    induction al using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_lanni.
        rewrite mult_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite ldist.
    rewrite rdist.
    rewrite IHal; clear IHal.
    apply rplus; clear al.
    assert (of_grade 0 (scalar_to_tensor ??)) as ??0.
    {
        exists ??.
        reflexivity.
    }
    destruct a as [a [i ai]]; cbn.
    rewrite (tensor_mult_homo _ _ _ _ _ ??0 ai).
    rewrite (tensor_mult_homo _ _ _ _ _ ai ??0).
    pose proof ai as [a' a_eq]; subst a.
    unfold scalar_to_tensor.
    do 2 rewrite power_to_tensor_tm.
    rewrite tensor_power_lscalar.
    rewrite <- tensor_power_rscalar.
    symmetry.
    apply power_to_tensor_k_eq.
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
    (tensor_mult_class V)
    (tensor_mult_ldist V)
    (tensor_mult_rdist V)
    (tensor_mult_assoc V)
    (tensor_one V)
    (tensor_mult_lid V)
    (tensor_mult_rid V)
    (tensor_scalar_lmult V)
    (tensor_scalar_rmult V)
.
