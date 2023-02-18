Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_power_base.
Require Import tensor_product_universal.
Require Import tensor_product_isomorphisms.
Require Import tensor_product_assoc.
Require Import module_category.
Require Import linear_grade.
Require Import linear_extend.

Require Import nat.
Require Import set.
Require Import unordered_list.
Require Import plus_sum.

(** This file contains the definition of multiplication on the tensor algebra,
and the proofs that it forms a rng.
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
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD TP TZ TN TPC
    TPA TPZ TPN TSM TSMC TSMO TSML TSMR TAP TAZ TAN TAPC TAPA TAPZ TAPN TASM
    TASMC TASMO TASML TASMR TAG.
(* end hide *)
Let k_tensor k := module_V (tensor_power V k).

Definition tensor_mult_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := power_to_tensor V (module_homo_f (tensor_power_mult V _ _)
        (tensor_mult _ _ (ex_val ai) (ex_val bj))).

Lemma power_to_tensor_tm :
    ∀ k1 k2 (A : k_tensor k1) (B : k_tensor k2) AH BH,
    tensor_mult_base k1 k2 (power_to_tensor V A) (power_to_tensor V B) AH BH
    = power_to_tensor V
        (module_homo_f (tensor_power_mult V _ _) (tensor_mult _ _ A B)).
Proof.
    intros k1 k2 A B Ak1 Bk2.
    unfold tensor_mult_base.
    rewrite_ex_val A' A'_eq.
    rewrite_ex_val B' B'_eq.
    apply power_to_tensor_eq in A'_eq.
    apply power_to_tensor_eq in B'_eq.
    subst A' B'.
    reflexivity.
Qed.

Theorem tensor_mult_base_ldist : bilinear_extend_ldist_base tensor_mult_base.
Proof.
    intros u' v' w' i j ui vj wj.
    pose proof ui as [u u_eq].
    pose proof vj as [v v_eq].
    pose proof wj as [w w_eq].
    subst u' v' w'.
    assert (of_grade j (power_to_tensor V (v + w))) as vwj.
    {
        rewrite power_to_tensor_plus.
        apply of_grade_plus; assumption.
    }
    rewrite (bilinear_extend_base_req _ _ _ _ _ _ _ _ vwj)
        by (symmetry; apply power_to_tensor_plus).
    do 3 rewrite power_to_tensor_tm.
    rewrite (tensor_ldist (tensor_power V i)).
    rewrite module_homo_plus.
    rewrite power_to_tensor_plus.
    reflexivity.
Qed.
Theorem tensor_mult_base_rdist : bilinear_extend_rdist_base tensor_mult_base.
Proof.
    intros u' v' w' i j ui vi wj.
    pose proof ui as [u u_eq].
    pose proof vi as [v v_eq].
    pose proof wj as [w w_eq].
    subst u' v' w'.
    assert (of_grade i (power_to_tensor V (u + v))) as uvi.
    {
        rewrite power_to_tensor_plus.
        apply of_grade_plus; assumption.
    }
    rewrite (bilinear_extend_base_leq _ _ _ _ _ _ _ uvi)
        by (symmetry; apply power_to_tensor_plus).
    do 3 rewrite power_to_tensor_tm.
    rewrite (tensor_rdist (tensor_power V i)).
    rewrite module_homo_plus.
    rewrite power_to_tensor_plus.
    reflexivity.
Qed.
Theorem tensor_mult_base_lscalar :
    bilinear_extend_lscalar_base tensor_mult_base.
Proof.
    intros a u' v' i j ui vj.
    pose proof ui as [u u_eq].
    pose proof vj as [v v_eq].
    subst u' v'.
    assert (of_grade i (power_to_tensor V (a · u))) as aui.
    {
        rewrite power_to_tensor_scalar.
        apply of_grade_scalar.
        exact ui.
    }
    rewrite (bilinear_extend_base_leq _ _ _ _ _ _ _ aui)
        by (symmetry; apply power_to_tensor_scalar).
    do 2 rewrite power_to_tensor_tm.
    rewrite (tensor_lscalar (tensor_power V i)).
    rewrite module_homo_scalar.
    rewrite power_to_tensor_scalar.
    reflexivity.
Qed.
Theorem tensor_mult_base_rscalar :
    bilinear_extend_rscalar_base tensor_mult_base.
Proof.
    intros a u' v' i j ui vj.
    pose proof ui as [u u_eq].
    pose proof vj as [v v_eq].
    subst u' v'.
    assert (of_grade j (power_to_tensor V (a · v))) as avj.
    {
        rewrite power_to_tensor_scalar.
        apply of_grade_scalar.
        exact vj.
    }
    rewrite (bilinear_extend_base_req _ _ _ _ _ _ _ _ avj)
        by (symmetry; apply power_to_tensor_scalar).
    do 2 rewrite power_to_tensor_tm.
    rewrite (tensor_rscalar (tensor_power V i)).
    rewrite module_homo_scalar.
    rewrite power_to_tensor_scalar.
    reflexivity.
Qed.

Instance tensor_mult_class : Mult (tensor_algebra_base V) := {
    mult A B := bilinear_extend tensor_mult_base A B
}.

(* begin show *)
Local Program Instance tensor_mult_ldist : Ldist (tensor_algebra_base V).
(* end show *)
Next Obligation.
    apply bilinear_extend_ldist.
    -   apply tensor_mult_base_ldist.
    -   apply tensor_mult_base_rscalar.
Qed.

(* begin show *)
Local Program Instance tensor_mult_rdist : Rdist (tensor_algebra_base V).
(* end show *)
Next Obligation.
    apply bilinear_extend_rdist.
    -   apply tensor_mult_base_rdist.
    -   apply tensor_mult_base_lscalar.
Qed.

(* begin show *)
Local Program Instance tensor_scalar_lmult : ScalarLMult U (tensor_algebra_base V).
(* end show *)
Next Obligation.
    apply bilinear_extend_lscalar.
    -   apply tensor_mult_base_rdist.
    -   apply tensor_mult_base_lscalar.
Qed.

(* begin show *)
Local Program Instance tensor_scalar_rmult : ScalarRMult U (tensor_algebra_base V).
(* end show *)
Next Obligation.
    apply bilinear_extend_rscalar.
    -   apply tensor_mult_base_ldist.
    -   apply tensor_mult_base_rscalar.
Qed.

Theorem tensor_mult_homo : ∀ i j u v H1 H2,
    u * v = tensor_mult_base i j u v H1 H2.
Proof.
    apply bilinear_extend_homo.
    -   apply tensor_mult_base_ldist.
    -   apply tensor_mult_base_rdist.
    -   apply tensor_mult_base_lscalar.
    -   apply tensor_mult_base_rscalar.
Qed.

Lemma tensor_mult_base_grade : ∀ u v i j H1 H2,
    of_grade (plus (U := nat) i j) (tensor_mult_base i j u v H1 H2).
Proof.
    intros u v i j ui vj.
    exists (module_homo_f (tensor_power_mult V _ _)
        (tensor_mult _ _ (ex_val ui) (ex_val vj))).
    reflexivity.
Qed.

Program Instance tensor_grade_mult : GradedAlgebraObj U (tensor_algebra_base V).
Next Obligation.
    rename H into ui, H0 into vj.
    rewrite (tensor_mult_homo i j u v ui vj).
    apply tensor_mult_base_grade.
Qed.

Program Instance tensor_mult_assoc : MultAssoc (tensor_algebra_base V).
Next Obligation.
    rewrite (grade_decomposition_eq a).
    rewrite (grade_decomposition_eq b).
    rewrite (grade_decomposition_eq c).
    rename a into A, b into B, c into C.
    remember (grade_decomposition A) as al.
    remember (grade_decomposition B) as bl.
    remember (grade_decomposition C) as cl.
    clear Heqal Heqbl Heqcl.
    induction cl as [|c cl] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite mult_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    do 3 rewrite ldist.
    rewrite IHcl; clear IHcl.
    apply rplus.
    clear cl.
    induction bl as [|b bl] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_lanni, mult_ranni.
        rewrite mult_lanni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite rdist.
    do 2 rewrite ldist.
    rewrite rdist.
    rewrite IHbl; clear IHbl.
    apply rplus.
    clear bl.
    induction al as [|a al] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite mult_lanni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite rdist.
    rewrite rdist.
    rewrite rdist.
    rewrite IHal; clear IHal.
    apply rplus.

    clear A B C al.
    destruct a as [a [i ai]]; cbn.
    destruct b as [b [j bj]]; cbn.
    destruct c as [c [k ck]]; cbn.
    rewrite (tensor_mult_homo j k b c bj ck).
    rewrite (tensor_mult_homo i j a b ai bj).
    pose proof (tensor_mult_base_grade _ _ _ _ bj ck) as bcjk.
    pose proof (tensor_mult_base_grade _ _ _ _ ai bj) as abij.
    rewrite (tensor_mult_homo _ _ _ _ ai bcjk).
    rewrite (tensor_mult_homo _ _ _ _ abij ck).
    rename a into a', b into b', c into c'.
    pose proof ai as [a a_eq].
    pose proof bj as [b b_eq].
    pose proof ck as [c c_eq].
    subst a' b' c'.

    pose proof (power_to_tensor_tm i j a b ai bj) as eq.
    assert (of_grade (i + j) (power_to_tensor V (module_homo_f
        (tensor_power_mult V i j) (tensor_mult _ _ a b)))) as abij'.
    {
        rewrite <- eq.
        exact abij.
    }
    rewrite (bilinear_extend_base_leq _ _ _ _ _ _ _ abij' _ eq); clear eq.
    pose proof (power_to_tensor_tm j k b c bj ck) as eq.
    assert (of_grade (j + k) (power_to_tensor V (module_homo_f
        (tensor_power_mult V j k) (tensor_mult _ _ b c)))) as bcjk'.
    {
        rewrite <- eq.
        exact bcjk.
    }
    rewrite (bilinear_extend_base_req _ _ _ _ _ _ _ _ bcjk' eq); clear eq.
    do 2 rewrite power_to_tensor_tm.
    rewrite <- tensor_power_mult_assoc.
    cbn in i, j, k.
    destruct (plus_assoc i j k); cbn.
    reflexivity.
Qed.
(* begin hide *)
End TensorAlgebraObj.
(* end hide *)
