Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_algebra_grade.
Require Import tensor_algebra_mult1.
Require Import tensor_power.
Require Import tensor_product_universal.
Require Import tensor_product_isomorphisms.
Require Import tensor_product_assoc.
Require Import module_category.

Require Import nat.
Require Import card.
Require Import set.
Require Import list.
Require Import plus_sum.

(** This file contains the true definition of multiplication on the tensor
algebra, and the proofs that it forms a rng.
*)

(* begin hide *)
Section TensorAlgebra.

Context {F : CRing} (V : Module F).

Let U := cring_U.
Let UP := cring_plus.
Let UZ := cring_zero.
Let UN := cring_neg.
Let UPA := cring_plus_assoc.
Let UPC := cring_plus_comm.
Let UPZ := cring_plus_lid.
Let UPN := cring_plus_linv.
Let UM := cring_mult.
Let UO := cring_one.
Let UMA := cring_mult_assoc.
Let UMC := cring_mult_comm.
Let UMO := cring_mult_lid.
Let UMD := cring_ldist.
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
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD TP TZ TN TPC
    TPA TPZ TPN TSM TSMC TSMO TSML TSMR TAP TAZ TAN TAPC TAPA TAPZ TAPN TASM
    TASMC TASMO TASML TASMR.
(* end hide *)
Let k_tensor k := module_V (tensor_power V k).

Instance tensor_mult : Mult (tensor_algebra_base V) := {
    mult A B := list_sum (list_prod2 (tensor_mult_base V)
        (tensor_decompose_grade V A) (tensor_decompose_grade V B))
}.

Program Instance tensor_mult_ldist : Ldist (tensor_algebra_base V).
Next Obligation.
    unfold mult; cbn.
    remember (tensor_decompose_grade V a) as al.
    clear Heqal a.
    induction al as [|a al].
    {
        do 3 rewrite list_prod2_lend.
        cbn.
        rewrite plus_rid.
        reflexivity.
    }
    do 3 rewrite list_prod2_lconc.
    rewrite IHal; clear IHal.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    rewrite (plus_comm (list_sum (list_image (tensor_decompose_grade V b) _))).
    rewrite <- plus_assoc.
    apply lplus.
    rewrite (plus_comm (list_sum _)).
    apply set_type_eq.
    apply functional_ext.
    intros k.
    unfold plus at 2; cbn.
    do 3 rewrite (tensor_list_sum_k V).
    do 3 rewrite list_image_comp.
    pose (ak := ex_val [|a]).
    classic_case (k < ak) as [k_lt|k_ge].
    -   assert ((λ x, [(tensor_mult_base V) a x|] k) = (λ x, 0)) as eq.
        {
            apply functional_ext.
            intros x.
            unfold ak in k_lt; clear ak.
            rewrite_ex_val ak [a' a_eq].
            pose proof (power_to_tensor_grade V _ a') as ak_grade.
            rewrite <- a_eq in ak_grade.
            clear a' a_eq.
            destruct [|x] as [xk [x' x_eq]].
            pose proof (power_to_tensor_grade V _ x') as xk_grade.
            rewrite <- x_eq in xk_grade.
            clear x' x_eq.
            pose proof (tensor_mult_tm_grade V _ _ _ _ ak_grade xk_grade)
                as mult_grade.
            symmetry; apply (tensor_grade_zero_eq V _ (ak + xk)).
            -   exact mult_grade.
            -   intros contr.
                rewrite contr in k_lt.
                clear - k_lt.
                rewrite <- nle_lt in k_lt.
                apply k_lt.
                apply nat_le_self_rplus.
        }
        change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
        rewrite eq; clear eq.
        pose (z := 0 : k_tensor k).
        assert (∀ (l : list (set_type (homogeneous_tensor V))),
            list_sum (list_image l (λ x, z)) = z) as eq.
        {
            induction l.
            -   cbn.
                reflexivity.
            -   cbn.
                rewrite IHl.
                apply plus_rid.
        }
        do 3 rewrite eq.
        unfold z.
        rewrite plus_rid.
        reflexivity.
    -   rewrite nlt_le in k_ge.
        apply nat_le_ex in k_ge as [k' k_eq].
        subst k; rename k' into k.
        assert (tensor_grade V [a|] ak) as ak_grade.
        {
            unfold ak; clear ak.
            rewrite_ex_val ak [A a_eq].
            exists A.
            exact a_eq.
        }
        rewrite (tensor_sum_decompose_lmult V a) by exact ak_grade.
        rewrite (tensor_sum_decompose_lmult V a) by exact ak_grade.
        rewrite (tensor_sum_decompose_lmult V a) by exact ak_grade.
        remember (list_nth (tensor_decompose_grade V (b + c)) _ _) as bc'.
        remember (list_nth (tensor_decompose_grade V b) _ _) as b'.
        remember (list_nth (tensor_decompose_grade V c) _ _) as c'.
        assert ((tensor_mult_base V) a bc' = (tensor_mult_base V) a b' + (tensor_mult_base V) a c') as eq.
        {
            unfold tensor_mult_base.
            unfold ex_val in ak.
            unfold ex_proof.
            destruct (ex_to_type _) as [ak' C0]; cbn in *.
            destruct (ex_to_type _) as [bck C1]; cbn in *.
            destruct (ex_to_type _) as [bk C2]; cbn in *.
            destruct (ex_to_type _) as [ck C3]; cbn in *.
            rewrite_ex_val A a_eq.
            rewrite_ex_val BC bc_eq.
            rewrite_ex_val B b_eq.
            rewrite_ex_val C c_eq.
            clear C0 C1 C2 C3.
            subst.
            pose proof (tensor_decompose_plus_nth V) as tensor_decompose_plus_nth.
            rewrite tensor_decompose_plus_nth in bc_eq.
            change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
            classic_case (0 = B) as [B_z|B_nz].
            1: {
                subst.
                rewrite b_eq in bc_eq.
                unfold TZ in bc_eq; rewrite power_to_tensor_zero in bc_eq.
                rewrite plus_lid in bc_eq.
                rewrite c_eq in bc_eq.
                classic_case (0 = C) as [C_z|C_nz].
                -   subst.
                    rewrite (power_to_tensor_zero V) in bc_eq.
                    rewrite <- (power_to_tensor_zero V bck) in bc_eq.
                    apply power_to_tensor_eq in bc_eq.
                    subst BC.
                    do 3 rewrite (tensor_product_ranni (tensor_power V ak')).
                    do 3 rewrite module_homo_zero.
                    do 3 rewrite power_to_tensor_zero.
                    rewrite plus_rid.
                    reflexivity.
                -   pose proof (power_to_tensor_eq_grade V
                        _ _ _ _ C_nz bc_eq) as k_eq.
                    subst.
                    apply power_to_tensor_eq in bc_eq.
                    subst.
                    rewrite (tensor_product_ranni (tensor_power V ak')).
                    rewrite module_homo_zero.
                    rewrite power_to_tensor_zero.
                    rewrite plus_lid.
                    reflexivity.
            }
            classic_case (0 = C) as [C_z|C_nz].
            1: {
                subst.
                rewrite c_eq in bc_eq.
                rewrite (power_to_tensor_zero V) in bc_eq.
                rewrite plus_rid in bc_eq.
                rewrite b_eq in bc_eq.
                pose proof (power_to_tensor_eq_grade V
                    _ _ _ _ B_nz bc_eq) as k_eq.
                subst.
                apply power_to_tensor_eq in bc_eq.
                subst.
                rewrite (tensor_product_ranni (tensor_power V ak')).
                rewrite module_homo_zero.
                rewrite power_to_tensor_zero.
                rewrite plus_rid.
                reflexivity.
            }
            assert (bk = k) as bk_eq.
            {
                pose proof (tensor_decompose_nth_grade V b k) as eq.
                change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
                rewrite b_eq in eq.
                pose proof (power_to_tensor_grade V _ B) as B_grade.
                apply (tensor_grade_unique V (power_to_tensor V B));
                    try assumption.
                intros contr.
                apply B_nz.
                apply (power_to_tensor_eq V).
                rewrite (power_to_tensor_zero V).
                exact contr.
            }
            assert (ck = k) as ck_eq.
            {
                pose proof (tensor_decompose_nth_grade V c k) as eq.
                change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
                rewrite c_eq in eq.
                pose proof (power_to_tensor_grade V _ C) as C_grade.
                apply (tensor_grade_unique V (power_to_tensor V C));
                    try assumption.
                intros contr.
                apply C_nz.
                apply (power_to_tensor_eq V).
                rewrite (power_to_tensor_zero V).
                exact contr.
            }
            subst bk ck.
            pose proof (power_to_tensor_plus V) as stupid.
            rewrite stupid.
            classic_case (0 = BC) as [BC_z|BC_nz].
            1: {
                subst.
                rewrite b_eq, c_eq in bc_eq.
                rewrite stupid in bc_eq; clear stupid.
                rewrite (power_to_tensor_zero V) in bc_eq.
                rewrite <- (power_to_tensor_zero V k) in bc_eq.
                apply power_to_tensor_eq in bc_eq.
                rewrite <- module_homo_plus.
                rewrite <- (tensor_ldist (tensor_power V ak') (tensor_power V k)).
                rewrite bc_eq.
                do 2 rewrite (tensor_product_ranni (tensor_power V ak')).
                do 2 rewrite module_homo_zero.
                do 2 rewrite power_to_tensor_zero.
                reflexivity.
            }
            assert (bck = k) as bck_eq.
            {
                pose proof (tensor_decompose_nth_grade V (b + c) k) as eq.
                rewrite tensor_decompose_plus_nth in eq.
                change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
                rewrite bc_eq in eq.
                pose proof (power_to_tensor_grade V _ BC) as BC_grade.
                apply (tensor_grade_unique V (power_to_tensor V BC));
                    try assumption.
                intros contr.
                apply BC_nz.
                apply (power_to_tensor_eq V).
                rewrite (power_to_tensor_zero V).
                exact contr.
            }
            subst bck.
            apply f_equal.
            rewrite b_eq, c_eq in bc_eq.
            rewrite stupid in bc_eq.
            apply power_to_tensor_eq in bc_eq.
            rewrite <- bc_eq.
            rewrite <- module_homo_plus.
            apply f_equal.
            apply tensor_ldist.
        }
        rewrite eq.
        reflexivity.
Qed.

Program Instance tensor_mult_rdist : Rdist (tensor_algebra_base V).
Next Obligation.
    rename a into b, b into c, c into a.
    unfold mult; cbn.
    remember (tensor_decompose_grade V a) as al.
    clear Heqal a.
    induction al as [|a al].
    {
        do 3 rewrite list_prod2_rend.
        cbn.
        rewrite plus_rid.
        reflexivity.
    }
    do 3 rewrite list_prod2_rconc.
    rewrite IHal; clear IHal.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    rewrite (plus_comm (list_sum (list_image (tensor_decompose_grade V b) _))).
    rewrite <- plus_assoc.
    apply lplus.
    rewrite (plus_comm (list_sum _)).
    apply set_type_eq.
    apply functional_ext.
    intros k.
    unfold plus at 2; cbn.
    do 3 rewrite (tensor_list_sum_k V).
    do 3 rewrite list_image_comp.
    pose (ak := ex_val [|a]).
    classic_case (k < ak) as [k_lt|k_ge].
    -   assert ((λ x, [(tensor_mult_base V) x a|] k) = (λ x, 0)) as eq.
        {
            apply functional_ext.
            intros x.
            unfold ak in k_lt; clear ak.
            rewrite_ex_val ak [a' a_eq].
            pose proof (power_to_tensor_grade V _ a') as ak_grade.
            rewrite <- a_eq in ak_grade.
            clear a' a_eq.
            destruct [|x] as [xk [x' x_eq]].
            pose proof (power_to_tensor_grade V _ x') as xk_grade.
            rewrite <- x_eq in xk_grade.
            clear x' x_eq.
            pose proof (tensor_mult_tm_grade V _ _ _ _ xk_grade ak_grade)
                as mult_grade.
            symmetry; apply (tensor_grade_zero_eq V _ (xk + ak)).
            -   exact mult_grade.
            -   intros contr.
                rewrite contr in k_lt.
                clear - k_lt.
                rewrite <- nle_lt in k_lt.
                apply k_lt.
                apply nat_le_self_lplus.
        }
        change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
        rewrite eq; clear eq.
        pose (z := 0 : k_tensor k).
        assert (∀ (l : list (set_type (homogeneous_tensor V))),
            list_sum (list_image l (λ x, z)) = z) as eq.
        {
            induction l.
            -   cbn.
                reflexivity.
            -   cbn.
                rewrite IHl.
                apply plus_rid.
        }
        do 3 rewrite eq.
        unfold z.
        rewrite plus_rid.
        reflexivity.
    -   rewrite nlt_le in k_ge.
        apply nat_le_ex in k_ge as [k' k_eq].
        rewrite plus_comm in k_eq.
        subst k; rename k' into k.
        assert (tensor_grade V [a|] ak) as ak_grade.
        {
            unfold ak; clear ak.
            rewrite_ex_val ak [A a_eq].
            exists A.
            exact a_eq.
        }
        pose proof (tensor_sum_decompose_rmult V a) as tensor_sum_decompose_rmult.
        rewrite tensor_sum_decompose_rmult by exact ak_grade.
        rewrite tensor_sum_decompose_rmult by exact ak_grade.
        rewrite tensor_sum_decompose_rmult by exact ak_grade.
        remember (list_nth (tensor_decompose_grade V (b + c)) _ _) as bc'.
        remember (list_nth (tensor_decompose_grade V b) _ _) as b'.
        remember (list_nth (tensor_decompose_grade V c) _ _) as c'.
        assert ((tensor_mult_base V) bc' a = (tensor_mult_base V) b' a + (tensor_mult_base V) c' a) as eq.
        {
            unfold tensor_mult_base.
            unfold ex_val in ak.
            unfold ex_proof.
            clear tensor_sum_decompose_rmult.
            destruct (ex_to_type _) as [ak' C0]; cbn in *.
            destruct (ex_to_type _) as [bck C1]; cbn in *.
            destruct (ex_to_type _) as [bk C2]; cbn in *.
            destruct (ex_to_type _) as [ck C3]; cbn in *.
            rewrite_ex_val BC bc_eq.
            rewrite_ex_val A a_eq.
            rewrite_ex_val B b_eq.
            rewrite_ex_val C c_eq.
            clear C0 C1 C2 C3.
            subst.
            pose proof (tensor_decompose_plus_nth V) as tensor_decompose_plus_nth.
            rewrite tensor_decompose_plus_nth in bc_eq.
            change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
            classic_case (0 = B) as [B_z|B_nz].
            1: {
                subst.
                rewrite b_eq in bc_eq.
                rewrite (power_to_tensor_zero V) in bc_eq.
                rewrite plus_lid in bc_eq.
                rewrite c_eq in bc_eq.
                classic_case (0 = C) as [C_z|C_nz].
                -   subst.
                    rewrite (power_to_tensor_zero V) in bc_eq.
                    rewrite <- (power_to_tensor_zero V bck) in bc_eq.
                    apply power_to_tensor_eq in bc_eq.
                    subst BC.
                    rewrite tensor_product_lanni.
                    rewrite (tensor_product_lanni (tensor_power V bk)).
                    rewrite (tensor_product_lanni (tensor_power V ck)).
                    do 3 rewrite module_homo_zero.
                    do 3 rewrite power_to_tensor_zero.
                    rewrite plus_rid.
                    reflexivity.
                -   pose proof (power_to_tensor_eq_grade V
                        _ _ _ _ C_nz bc_eq) as k_eq.
                    subst.
                    apply power_to_tensor_eq in bc_eq.
                    subst.
                    rewrite (tensor_product_lanni (tensor_power V bk)).
                    rewrite module_homo_zero.
                    rewrite power_to_tensor_zero.
                    rewrite plus_lid.
                    reflexivity.
            }
            classic_case (0 = C) as [C_z|C_nz].
            1: {
                subst.
                rewrite c_eq in bc_eq.
                rewrite (power_to_tensor_zero V) in bc_eq.
                rewrite plus_rid in bc_eq.
                rewrite b_eq in bc_eq.
                pose proof (power_to_tensor_eq_grade V
                    _ _ _ _ B_nz bc_eq) as k_eq.
                subst.
                apply power_to_tensor_eq in bc_eq.
                subst.
                rewrite (tensor_product_lanni (tensor_power V ck)).
                rewrite module_homo_zero.
                rewrite power_to_tensor_zero.
                rewrite plus_rid.
                reflexivity.
            }
            assert (bk = k) as bk_eq.
            {
                pose proof (tensor_decompose_nth_grade V b k) as eq.
                change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
                rewrite b_eq in eq.
                pose proof (power_to_tensor_grade V _ B) as B_grade.
                apply (tensor_grade_unique V (power_to_tensor V B));
                    try assumption.
                intros contr.
                apply B_nz.
                apply (power_to_tensor_eq V).
                rewrite (power_to_tensor_zero V).
                exact contr.
            }
            assert (ck = k) as ck_eq.
            {
                pose proof (tensor_decompose_nth_grade V c k) as eq.
                change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
                rewrite c_eq in eq.
                pose proof (power_to_tensor_grade V _ C) as C_grade.
                apply (tensor_grade_unique V (power_to_tensor V C));
                    try assumption.
                intros contr.
                apply C_nz.
                apply (power_to_tensor_eq V).
                rewrite (power_to_tensor_zero V).
                exact contr.
            }
            subst bk ck.
            pose proof (power_to_tensor_plus V)
                as power_to_tensor_plus.
            rewrite power_to_tensor_plus.
            classic_case (0 = BC) as [BC_z|BC_nz].
            1: {
                subst.
                rewrite b_eq, c_eq in bc_eq.
                rewrite power_to_tensor_plus in bc_eq.
                rewrite (power_to_tensor_zero V) in bc_eq.
                rewrite <- (power_to_tensor_zero V k) in bc_eq.
                apply power_to_tensor_eq in bc_eq.
                rewrite <- module_homo_plus.
                rewrite <- (tensor_rdist (tensor_power V k) (tensor_power V ak')).
                rewrite bc_eq.
                rewrite (tensor_product_lanni).
                rewrite (tensor_product_lanni (tensor_power V bck)).
                do 2 rewrite module_homo_zero.
                do 2 rewrite power_to_tensor_zero.
                reflexivity.
            }
            assert (bck = k) as bck_eq.
            {
                pose proof (tensor_decompose_nth_grade V (b + c) k) as eq.
                rewrite tensor_decompose_plus_nth in eq.
                change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
                rewrite bc_eq in eq.
                pose proof (power_to_tensor_grade V _ BC) as BC_grade.
                apply (tensor_grade_unique V (power_to_tensor V BC));
                    try assumption.
                intros contr.
                apply BC_nz.
                apply (power_to_tensor_eq V).
                rewrite (power_to_tensor_zero V).
                exact contr.
            }
            subst bck.
            apply f_equal.
            rewrite b_eq, c_eq in bc_eq.
            rewrite power_to_tensor_plus in bc_eq.
            apply power_to_tensor_eq in bc_eq.
            rewrite <- bc_eq.
            rewrite <- module_homo_plus.
            apply f_equal.
            apply tensor_rdist.
        }
        rewrite eq.
        reflexivity.
Qed.

Program Instance tensor_mult_assoc : MultAssoc (tensor_algebra_base V).
Next Obligation.
    rewrite (tensor_decompose_grade_eq V a).
    rewrite (tensor_decompose_grade_eq V b).
    rewrite (tensor_decompose_grade_eq V c).
    rename a into A, b into B, c into C.
    remember (tensor_decompose_grade V A) as al.
    remember (tensor_decompose_grade V B) as bl.
    remember (tensor_decompose_grade V C) as cl.
    clear Heqal Heqbl Heqcl.
    induction cl as [|c cl].
    {
        cbn.
        do 3 rewrite mult_ranni.
        reflexivity.
    }
    cbn.
    do 3 rewrite ldist.
    rewrite IHcl; clear IHcl.
    apply rplus.
    clear cl.
    induction bl as [|b bl].
    {
        cbn.
        rewrite mult_lanni, mult_ranni.
        rewrite mult_ranni, mult_lanni.
        reflexivity.
    }
    cbn.
    rewrite rdist.
    do 2 rewrite ldist.
    rewrite rdist.
    rewrite IHbl; clear IHbl.
    apply rplus.
    clear bl.
    induction al as [|a al].
    {
        cbn.
        do 3 rewrite mult_lanni.
        reflexivity.
    }
    cbn.
    rewrite rdist.
    rewrite rdist.
    rewrite rdist.
    rewrite IHal; clear IHal.
    apply rplus.
    unfold mult; cbn.
Local Arguments list_prod2: simpl never.
    do 3 rewrite (tensor_lmult_homogeneous2 V).
    do 3 rewrite (tensor_rmult_homogeneous2 V).
    do 3 rewrite list_prod2_lconc.
    do 3 rewrite list_prod2_lend.
    cbn.
    do 3 rewrite plus_lid.
    do 2 rewrite plus_rid.
    assert (list_sum (list_image
        (tensor_decompose_grade V ((tensor_mult_base V) b c)) (λ x, (tensor_mult_base V) a x)) =
        list_sum (list_prod2 (tensor_mult_base V) (a :: list_end)
        (tensor_decompose_grade V ((tensor_mult_base V) b c)))) as eq.
    {
        rewrite list_prod2_lconc.
        rewrite list_prod2_lend.
        cbn; rewrite plus_lid.
        reflexivity.
    }
    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
    unfold TP, TZ, TAP, TAZ in *.
    rewrite eq; clear eq.
    pose proof (tensor_mult_homogeneous V a b) as ab_homo.
    pose proof (tensor_lmult_homogeneous2 V [_|ab_homo] (c :: list_end)) as eq.
    cbn in eq.
    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
    rewrite eq; clear eq.
    pose proof (tensor_mult_homogeneous V b c) as bc_homo.
    pose proof (tensor_rmult_homogeneous2 V (a :: list_end) [_|bc_homo]) as eq.
    cbn in eq.
    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
    rewrite eq; clear eq.
Local Arguments list_prod2: simpl nomatch.
    cbn.
    do 2 rewrite plus_rid.
    clear A B C al.
    destruct a as [a a_homo]; cbn.
    destruct b as [b b_homo]; cbn.
    destruct c as [c c_homo]; cbn.
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    pose proof c_homo as [ck [C C_eq]].
    subst a b c.
    pose proof (power_to_tensor_tm V _ _ B C b_homo c_homo) as eq.
    assert (homogeneous_tensor V (power_to_tensor V (module_homo_f (tensor_power_mult V bk ck) (tensor_product_universal.tensor_mult _ _ B C))))
        as bc_homo2.
    {
        exists (bk + ck), (module_homo_f (tensor_power_mult V bk ck) (tensor_product_universal.tensor_mult _ _ B C)).
        reflexivity.
    }
    assert ([(tensor_mult_base V) [_|b_homo] [_|c_homo] | bc_homo] = [_|bc_homo2]) as eq2.
    {
        apply set_type_eq; exact eq.
    }
    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
    rewrite eq2.
    rewrite (power_to_tensor_tm V).
    clear eq eq2 bc_homo bc_homo2.
    pose proof (power_to_tensor_tm V _ _ A B a_homo b_homo) as eq.
    assert (homogeneous_tensor V (power_to_tensor V (module_homo_f (tensor_power_mult V ak bk) (tensor_product_universal.tensor_mult _ _ A B))))
        as ab_homo2.
    {
        exists (ak + bk), (module_homo_f (tensor_power_mult V ak bk) (tensor_product_universal.tensor_mult _ _ A B)).
        reflexivity.
    }
    assert ([(tensor_mult_base V) [_|a_homo] [_|b_homo] | ab_homo] = [_|ab_homo2]) as eq2.
    {
        apply set_type_eq; exact eq.
    }
    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
    rewrite eq2.
    rewrite (power_to_tensor_tm V).
    clear eq eq2 ab_homo ab_homo2 a_homo b_homo c_homo.
    rewrite <- tensor_power_mult_assoc.
    destruct (plus_assoc ak bk ck); cbn.
    reflexivity.
Qed.
(* begin hide *)
End TensorAlgebra.
(* end hide *)
