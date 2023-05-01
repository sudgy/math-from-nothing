Require Import init.

Require Export tensor_algebra_traditional_base.
Require Import tensor_power_base.
Require Import tensor_product_universal.
Require Import tensor_product_isomorphisms.
Require Import tensor_product_assoc.
Require Import module_category.
Require Import linear_grade.
Require Import linear_extend.
Require Import linear_bilinear.

Require Import nat.
Require Import set.
Require Import unordered_list.

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

Definition tensor_mult_base i j (a : tensor_power V i) (b : tensor_power V j)
    := power_to_tensor V (tensor_power_mult V _ _ (tensor_mult _ _ a b))
    : tensor_algebra_base V.

Theorem tensor_mult_base_bilinear : ∀ i j, bilinear (tensor_mult_base i j).
Proof.
    intros i j.
    repeat split.
    -   intros a u v.
        unfold tensor_mult_base.
        rewrite tensor_lscalar.
        rewrite module_homo_scalar.
        apply power_to_tensor_scalar.
    -   intros a u v.
        unfold tensor_mult_base.
        rewrite tensor_rscalar.
        rewrite module_homo_scalar.
        apply power_to_tensor_scalar.
    -   intros u v w.
        unfold tensor_mult_base.
        rewrite tensor_rdist.
        rewrite module_homo_plus.
        apply power_to_tensor_plus.
    -   intros u v w.
        unfold tensor_mult_base.
        rewrite tensor_ldist.
        rewrite module_homo_plus.
        apply power_to_tensor_plus.
Qed.

Instance tensor_mult_class : Mult (tensor_algebra_base V) := {
    mult A B := bilinear_extend (λ i j, [_|tensor_mult_base_bilinear i j]) A B
}.

Local Program Instance tensor_mult_ldist : Ldist (tensor_algebra_base V).
Next Obligation.
    exact (bilinear_extend_ldist (λ i j, [_|tensor_mult_base_bilinear i j]) a b c).
Qed.

Local Program Instance tensor_mult_rdist : Rdist (tensor_algebra_base V).
Next Obligation.
    exact (bilinear_extend_rdist (λ i j, [_|tensor_mult_base_bilinear i j]) a b c).
Qed.

Local Program Instance tensor_scalar_lmult : ScalarLMult U (tensor_algebra_base V).
Next Obligation.
    exact (bilinear_extend_lscalar (λ i j, [_|tensor_mult_base_bilinear i j]) a u v).
Qed.

Local Program Instance tensor_scalar_rmult : ScalarRMult U (tensor_algebra_base V).
Next Obligation.
    exact (bilinear_extend_rscalar (λ i j, [_|tensor_mult_base_bilinear i j]) a u v).
Qed.

Theorem tensor_mult_homo : ∀ i j u v (H1 : of_grade i u) (H2 : of_grade j v),
    u * v = tensor_mult_base i j ([grade_to u|] i) ([grade_to v|] j).
Proof.
    intros i j u v iu jv.
    unfold mult; cbn.
    rewrite (bilinear_extend_homo _ i j u v iu jv).
    reflexivity.
Qed.

Lemma tensor_mult_base_grade : ∀ i j u v,
    of_grade (plus (U := nat) i j) (tensor_mult_base i j u v).
Proof.
    intros i j u v.
    apply of_grade_ex.
    exists (tensor_power_mult V _ _ (tensor_mult _ _ u v)).
    reflexivity.
Qed.

Program Instance tensor_mult_assoc : MultAssoc (tensor_algebra_base V).
Next Obligation.
    induction a as [|a a'] using grade_induction.
    {
        do 3 rewrite mult_lanni.
        reflexivity.
    }
    do 3 rewrite rdist.
    rewrite IHa.
    apply rplus.
    clear a' IHa.
    induction b as [|b b'] using grade_induction.
    {
        rewrite mult_lanni.
        do 2 rewrite mult_ranni.
        rewrite mult_lanni.
        reflexivity.
    }
    rewrite ldist.
    do 2 rewrite rdist.
    rewrite ldist.
    rewrite IHb.
    apply rplus.
    clear b' IHb.
    induction c as [|c c'] using grade_induction.
    {
        do 3 rewrite mult_ranni.
        reflexivity.
    }
    do 3 rewrite ldist.
    rewrite IHc.
    apply rplus.
    clear c' IHc.

    destruct a as [a [i ai]]; cbn.
    destruct b as [b [j bj]]; cbn.
    destruct c as [c [k ck]]; cbn.
    rewrite (tensor_mult_homo j k b c bj ck).
    rewrite (tensor_mult_homo i j a b ai bj).
    pose proof (tensor_mult_base_grade _ _ ([grade_to b|] j) ([grade_to c|] k))
        as bcjk.
    pose proof (tensor_mult_base_grade _ _ ([grade_to a|] i) ([grade_to b|] j))
        as abij.
    rewrite (tensor_mult_homo _ _ _ _ ai bcjk).
    rewrite (tensor_mult_homo _ _ _ _ abij ck).
    unfold tensor_mult_base; cbn.
    unfold grade_to; cbn.
    do 2 rewrite single_to_sum_module_base_eq.
    rewrite <- tensor_power_mult_assoc.
    cbn in i, j, k.
    destruct (plus_assoc i j k); cbn.
    reflexivity.
Qed.
(* begin hide *)
End TensorAlgebraObj.
(* end hide *)
