Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_algebra_grade.
Require Import tensor_power.
Require Import tensor_product_universal.
Require Import tensor_product_isomorphisms.
Require Import tensor_product_assoc.
Require Import module_category.
Require Import linear_grade.
Require Import linear_extend.

Require Import nat.
Require Import card.
Require Import set.
Require Import unordered_list.
Require Import plus_sum.

(** This file contains the definition of multiplication on the tensor algebra,
and the proofs that it forms a rng.
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
Let TAG := tensor_grade V.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD TP TZ TN TPC
    TPA TPZ TPN TSM TSMC TSMO TSML TSMR TAP TAZ TAN TAPC TAPA TAPZ TAPN TASM
    TASMC TASMO TASML TASMR TAG.
(* end hide *)
Let k_tensor k := module_V (tensor_power V k).

Definition tensor_mult_base (A' B' : set_type homogeneous)
    := power_to_tensor V (module_homo_f (tensor_power_mult V _ _)
        (tensor_mult _ _ (ex_val (ex_proof [|A']))
        (ex_val (ex_proof [|B'])))).

Lemma power_to_tensor_tm :
        ∀ k1 k2 (A : k_tensor k1) (B : k_tensor k2) AH BH,
        tensor_mult_base [power_to_tensor V A|AH] [power_to_tensor V B|BH] =
        power_to_tensor V (module_homo_f (tensor_power_mult V _ _) (tensor_mult _ _ A B)).
    intros k1 k2 A B A_homo B_homo.
    unfold tensor_mult_base.
    cbn.
    unfold ex_proof.
    pose (X := ex_to_type A_homo).
    change (ex_to_type A_homo) with X.
    destruct X as [k1' A_k1']; cbn.
    pose (X := ex_to_type B_homo).
    change (ex_to_type B_homo) with X.
    destruct X as [k2' B_k2']; cbn.
    rewrite_ex_val A' A'_eq.
    rewrite_ex_val B' B'_eq.
    classic_case (0 = power_to_tensor V A) as [A_z|A_nz].
    1: {
        rewrite <- A_z in A'_eq.
        unfold TAZ in *.
        rewrite <- (power_to_tensor_zero V k1) in A_z.
        apply power_to_tensor_eq in A_z.
        subst A.
        rewrite <- (power_to_tensor_zero V k1') in A'_eq.
        apply power_to_tensor_eq in A'_eq.
        subst A'.
        do 2 rewrite tensor_product_lanni.
        do 2 rewrite module_homo_zero.
        do 2 rewrite power_to_tensor_zero.
        reflexivity.
    }
    classic_case (0 = power_to_tensor V B) as [B_z|B_nz].
    1: {
        rewrite <- B_z in B'_eq.
        unfold TAZ in *.
        rewrite <- (power_to_tensor_zero V k2) in B_z.
        apply power_to_tensor_eq in B_z.
        subst B.
        rewrite <- (power_to_tensor_zero V k2') in B'_eq.
        apply power_to_tensor_eq in B'_eq.
        subst B'.
        do 2 rewrite tensor_product_ranni.
        do 2 rewrite module_homo_zero.
        do 2 rewrite power_to_tensor_zero.
        reflexivity.
    }
    assert (k1 = k1') as k1_eq.
    {
        change nat with grade_I in k1.
        apply (of_grade_unique _ k1 k1' A_nz).
        -   exists A.
            reflexivity.
        -   exact A_k1'.
    }
    assert (k2 = k2') as k2_eq.
    {
        change nat with grade_I in k2.
        apply (of_grade_unique _ k2 k2' B_nz).
        -   exists B.
            reflexivity.
        -   exact B_k2'.
    }
    subst k1' k2'.
    apply power_to_tensor_eq in A'_eq.
    apply power_to_tensor_eq in B'_eq.
    subst A' B'.
    reflexivity.
Qed.

Theorem tensor_mult_base_ldist : ∀ u v w i (H1 : of_grade i v) (H2 : of_grade i w),
        tensor_mult_base u [v + w|ex_intro _ i (of_grade_plus v w i H1 H2)] =
        tensor_mult_base u [v|ex_intro _ i H1] + tensor_mult_base u [w|ex_intro _ i H2].
    intros [u' u_homo] v' w' j vj wj.
    destruct u_homo as [i [u u_eq]].
    destruct vj as [v v_eq].
    destruct wj as [w w_eq].
    subst u' v' w'.
    assert (homogeneous (power_to_tensor V v + power_to_tensor V w)) as vw_homo.
    {
        exists j.
        apply of_grade_plus.
        -   exists v.
            reflexivity.
        -   exists w.
            reflexivity.
    }
    rewrite (proof_irrelevance _ vw_homo).
    assert (homogeneous (power_to_tensor V (v + w))) as vw_homo2.
    {
        exists j.
        exists (v + w).
        reflexivity.
    }
    assert ([_|vw_homo] = [_|vw_homo2]) as eq.
    {
        apply set_type_eq; cbn.
        apply power_to_tensor_plus.
    }
    unfold tensor_algebra_base in *.
    rewrite eq; clear eq.
    do 3 rewrite power_to_tensor_tm.
    rewrite (tensor_ldist (tensor_power V i)).
    rewrite module_homo_plus.
    rewrite <- power_to_tensor_plus.
    reflexivity.
Qed.
Theorem tensor_mult_base_rdist : ∀ u v w i (H1 : of_grade i u) (H2 : of_grade i v),
        tensor_mult_base [u + v|ex_intro _ i (of_grade_plus u v i H1 H2)] w =
        tensor_mult_base [u|ex_intro _ i H1] w + tensor_mult_base [v|ex_intro _ i H2] w.
    intros u' v' [w' w_homo] i ui vi.
    destruct w_homo as [j [w w_eq]].
    destruct ui as [u u_eq].
    destruct vi as [v v_eq].
    subst u' v' w'.
    assert (homogeneous (power_to_tensor V u + power_to_tensor V v)) as uv_homo.
    {
        exists i.
        apply of_grade_plus.
        -   exists u.
            reflexivity.
        -   exists v.
            reflexivity.
    }
    rewrite (proof_irrelevance _ uv_homo).
    assert (homogeneous (power_to_tensor V (u + v))) as uv_homo2.
    {
        exists i.
        exists (u + v).
        reflexivity.
    }
    assert ([_|uv_homo] = [_|uv_homo2]) as eq.
    {
        apply set_type_eq; cbn.
        apply power_to_tensor_plus.
    }
    unfold tensor_algebra_base in *.
    rewrite eq; clear eq.
    do 3 rewrite power_to_tensor_tm.
    rewrite (tensor_rdist (tensor_power V i)).
    rewrite module_homo_plus.
    rewrite <- power_to_tensor_plus.
    reflexivity.
Qed.
Theorem tensor_mult_base_lscalar : ∀ a u v i (H : of_grade i u),
        tensor_mult_base [a · u|ex_intro _ i (of_grade_scalar a u i H)] v =
        a · tensor_mult_base [u|ex_intro _ i H] v.
    intros a u' [v' v_homo] i ui.
    destruct v_homo as [j [v v_eq]].
    destruct ui as [u u_eq].
    subst u' v'.
    assert (homogeneous (a · power_to_tensor V u)) as au_homo.
    {
        exists i.
        apply of_grade_scalar.
        exists u.
        reflexivity.
    }
    rewrite (proof_irrelevance _ au_homo).
    assert (homogeneous (power_to_tensor V (a · u))) as au_homo2.
    {
        exists i.
        exists (a · u).
        reflexivity.
    }
    assert ([_|au_homo] = [_|au_homo2]) as eq.
    {
        apply set_type_eq; cbn.
        symmetry; apply power_to_tensor_scalar.
    }
    unfold tensor_algebra_base in *.
    rewrite eq; clear eq.
    do 2 rewrite power_to_tensor_tm.
    rewrite (tensor_lscalar (tensor_power V i)).
    rewrite module_homo_scalar.
    rewrite power_to_tensor_scalar.
    reflexivity.
Qed.
Theorem tensor_mult_base_rscalar : ∀ a u v i (H : of_grade i v),
        tensor_mult_base u [a · v|ex_intro _ i (of_grade_scalar a v i H)] =
        a · tensor_mult_base u [v|ex_intro _ i H].
    intros a [u' u_homo] v' j vj.
    destruct u_homo as [i [u u_eq]].
    destruct vj as [v v_eq].
    subst u' v'.
    assert (homogeneous (a · power_to_tensor V v)) as av_homo.
    {
        exists j.
        apply of_grade_scalar.
        exists v.
        reflexivity.
    }
    rewrite (proof_irrelevance _ av_homo).
    assert (homogeneous (power_to_tensor V (a · v))) as av_homo2.
    {
        exists j.
        exists (a · v).
        reflexivity.
    }
    assert ([_|av_homo] = [_|av_homo2]) as eq.
    {
        apply set_type_eq; cbn.
        symmetry; apply power_to_tensor_scalar.
    }
    unfold tensor_algebra_base in *.
    rewrite eq; clear eq.
    do 2 rewrite power_to_tensor_tm.
    rewrite (tensor_rscalar (tensor_power V i)).
    rewrite module_homo_scalar.
    rewrite power_to_tensor_scalar.
    reflexivity.
Qed.

Instance tensor_mult_class : Mult (tensor_algebra_base V) := {
    mult A B := bilinear_extend tensor_mult_base A B
}.

Local Program Instance tensor_mult_ldist : Ldist (tensor_algebra_base V).
Next Obligation.
    apply bilinear_extend_ldist.
    -   apply tensor_mult_base_ldist.
    -   apply tensor_mult_base_rscalar.
Qed.

Local Program Instance tensor_mult_rdist : Rdist (tensor_algebra_base V).
Next Obligation.
    apply bilinear_extend_rdist.
    -   apply tensor_mult_base_rdist.
    -   apply tensor_mult_base_lscalar.
Qed.

Local Program Instance tensor_scalar_lmult : ScalarLMult U (tensor_algebra_base V).
Next Obligation.
    apply bilinear_extend_lscalar.
    -   apply tensor_mult_base_rdist.
    -   apply tensor_mult_base_lscalar.
Qed.

Local Program Instance tensor_scalar_rmult : ScalarRMult U (tensor_algebra_base V).
Next Obligation.
    apply bilinear_extend_rscalar.
    -   apply tensor_mult_base_ldist.
    -   apply tensor_mult_base_rscalar.
Qed.

Theorem tensor_mult_homo : ∀ u v, [u|] * [v|] = tensor_mult_base u v.
    apply bilinear_extend_homo.
    -   apply tensor_mult_base_lscalar.
    -   apply tensor_mult_base_rscalar.
Qed.

Lemma tensor_mult_base_grade : ∀ u v i j H1 H2,
        of_grade i u → of_grade j v →
        of_grade (plus (U := nat) i j) (tensor_mult_base [u|H1] [v|H2]).
    intros u v i j u_homo v_homo ui vj.
    classic_case (0 = u) as [u_z|u_nz].
    1: {
        subst u.
        rewrite bilinear_extend_lanni_base by exact tensor_mult_base_lscalar.
        apply of_grade_zero.
    }
    classic_case (0 = v) as [v_z|v_nz].
    1: {
        subst v.
        rewrite bilinear_extend_ranni_base by exact tensor_mult_base_rscalar.
        apply of_grade_zero.
    }
    assert (i = ex_val u_homo) as i_eq.
    {
        rewrite_ex_val i' i'_eq.
        change nat with grade_I in i, j.
        apply (of_grade_unique u i i' u_nz).
        -   destruct ui as [u' u'_eq].
            rewrite <- u'_eq.
            exists u'; reflexivity.
        -   exact i'_eq.
    }
    assert (j = ex_val v_homo) as j_eq.
    {
        rewrite_ex_val j' j'_eq.
        change nat with grade_I in i, j.
        apply (of_grade_unique v j j' v_nz).
        -   destruct vj as [v' v'_eq].
            rewrite <- v'_eq.
            exists v'; reflexivity.
        -   exact j'_eq.
    }
    rewrite i_eq, j_eq.
    exists (module_homo_f (tensor_power_mult V _ _)
        (tensor_mult _ _ (ex_val (ex_proof u_homo)) (ex_val (ex_proof v_homo)))).
    reflexivity.
Qed.

Lemma tensor_mult_base_homo : ∀ u v, homogeneous (tensor_mult_base u v).
    intros [u [i ui]] [v [j vj]].
    exists (i + j).
    apply tensor_mult_base_grade.
    -   exact ui.
    -   exact vj.
Qed.

Program Instance tensor_grade_mult : GradedAlgebra U (tensor_algebra_base V).
Next Obligation.
    rename H into ui, H0 into vj.
    assert (homogeneous u) as u_homo by (exists i; exact ui).
    assert (homogeneous v) as v_homo by (exists j; exact vj).
    change u with [[u|u_homo]|].
    change v with [[v|v_homo]|].
    rewrite (tensor_mult_homo [u|u_homo] [v|v_homo]).
    apply tensor_mult_base_grade.
    -   exact ui.
    -   exact vj.
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
    do 2 rewrite tensor_mult_homo.
    pose proof (tensor_mult_base_homo b c) as bc_homo.
    pose proof (tensor_mult_base_homo a b) as ab_homo.
    change (tensor_mult_base b c) with [[_|bc_homo]|].
    change (tensor_mult_base a b) with [[_|ab_homo]|].
    do 2 rewrite tensor_mult_homo.
    clear A B C al.
    destruct a as [a a_homo]; cbn.
    destruct b as [b b_homo]; cbn.
    destruct c as [c c_homo]; cbn.
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    pose proof c_homo as [ck [C C_eq]].
    subst a b c.
    pose proof (power_to_tensor_tm _ _ B C b_homo c_homo) as eq.
    assert (homogeneous (power_to_tensor V (module_homo_f (tensor_power_mult V bk ck) (tensor_product_universal.tensor_mult _ _ B C))))
        as bc_homo2.
    {
        exists (bk + ck), (module_homo_f (tensor_power_mult V bk ck) (tensor_product_universal.tensor_mult _ _ B C)).
        reflexivity.
    }
    assert ([tensor_mult_base [_|b_homo] [_|c_homo] | bc_homo] = [_|bc_homo2]) as eq2.
    {
        apply set_type_eq; exact eq.
    }
    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
    rewrite eq2.
    rewrite power_to_tensor_tm.
    clear eq eq2 bc_homo bc_homo2.
    pose proof (power_to_tensor_tm _ _ A B a_homo b_homo) as eq.
    assert (homogeneous (power_to_tensor V (module_homo_f (tensor_power_mult V ak bk) (tensor_product_universal.tensor_mult _ _ A B))))
        as ab_homo2.
    {
        exists (ak + bk), (module_homo_f (tensor_power_mult V ak bk) (tensor_product_universal.tensor_mult _ _ A B)).
        reflexivity.
    }
    assert ([tensor_mult_base [_|a_homo] [_|b_homo] | ab_homo] = [_|ab_homo2]) as eq2.
    {
        apply set_type_eq; exact eq.
    }
    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
    rewrite eq2.
    rewrite power_to_tensor_tm.
    clear eq eq2 ab_homo ab_homo2 a_homo b_homo c_homo.
    rewrite <- tensor_power_mult_assoc.
    destruct (plus_assoc ak bk ck); cbn.
    destruct (nat_plus_assoc_ ak bk ck); cbn.
    reflexivity.
Qed.
(* begin hide *)
End TensorAlgebra.
(* end hide *)
