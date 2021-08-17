Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_algebra_grade.
Require Import tensor_algebra_mult1.
Require Import linear_multilinear.
Require Import nat.
Require Import card.
Require Import set.
Require Import list.
Require Import plus_sum.

Section TensorAlgebra.

Variables U V : Type.

Context `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @Ldist U UP UM,
    @MultComm U UM,
    @MultAssoc U UM,
    @MultLid U UM UO,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM
}.

Let T1 := multilinear_plus U V 1.
Let T2 := multilinear_plus_comm U V 1.
Let T3 := multilinear_plus_assoc U V 1.
Let T4 := multilinear_zero U V 1.
Let T5 := multilinear_plus_lid U V 1.
Let T6 := multilinear_neg U V 1.
Let T7 := multilinear_plus_linv U V 1.
Let T8 := multilinear_scalar_mult U V 1.
Let T9 := multilinear_scalar_comp U V 1.
Let T10 := multilinear_scalar_id U V 1.
Let T11 := multilinear_scalar_ldist U V 1.
Let T12 := multilinear_scalar_rdist U V 1.
Existing Instances T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Let T13 := multilinear_plus U (multilinear_type U V 1).
Let T14 := multilinear_plus_comm U (multilinear_type U V 1).
Let T15 := multilinear_plus_assoc U (multilinear_type U V 1).
Let T16 := multilinear_zero U (multilinear_type U V 1).
Let T17 := multilinear_plus_lid U (multilinear_type U V 1).
Let T18 := multilinear_neg U (multilinear_type U V 1).
Let T19 := multilinear_plus_linv U (multilinear_type U V 1).
Let T20 := multilinear_scalar_mult U (multilinear_type U V 1).
Let T21 := multilinear_scalar_comp U (multilinear_type U V 1).
Let T22 := multilinear_scalar_id U (multilinear_type U V 1).
Let T23 := multilinear_scalar_ldist U (multilinear_type U V 1).
Let T24 := multilinear_scalar_rdist U (multilinear_type U V 1).
Let T25 := tensor_plus U V.
Let T26 := tensor_plus_comm U V.
Let T27 := tensor_plus_assoc U V.
Let T28 := tensor_zero U V.
Let T29 := tensor_plus_lid U V.
Let T30 := tensor_neg U V.
Let T31 := tensor_plus_linv U V.
Let T32 := tensor_scalar_mult U V.
Let T33 := tensor_scalar_comp U V.
Let T34 := tensor_scalar_id U V.
Let T35 := tensor_scalar_ldist U V.
Let T36 := tensor_scalar_rdist U V.
Existing Instances T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27
    T28 T29 T30 T31 T32 T33 T34 T35 T36.

Let multi_type k := multilinear_type U (multilinear_type U V 1) k.

Instance tensor_mult : Mult (tensor_algebra U V) := {
    mult A B := list_sum (list_prod2 (tensor_mult_base U V)
        (tensor_decompose_grade U V A) (tensor_decompose_grade U V B))
}.

Program Instance tensor_mult_ldist : Ldist (tensor_algebra U V).
Next Obligation.
    unfold mult; cbn.
    remember (tensor_decompose_grade U V a) as al.
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
    rewrite (plus_comm (list_sum (list_image (tensor_decompose_grade U V b) _))).
    rewrite <- plus_assoc.
    apply lplus.
    rewrite (plus_comm (list_sum _)).
    apply set_type_eq.
    apply functional_ext.
    intros k.
    unfold plus at 2; cbn.
    do 3 rewrite tensor_list_sum_k.
    do 3 rewrite list_image_comp.
    pose (ak := ex_val [|a]).
    classic_case (k < ak) as [k_lt|k_ge].
    -   assert ((λ x, [(tensor_mult_base U V) a x|] k) = (λ x, 0)) as eq.
        {
            apply functional_ext.
            intros x.
            unfold ak in k_lt; clear ak.
            rewrite_ex_val ak [a' a_eq].
            pose proof (multilinear_to_tensor_grade U V _ a') as ak_grade.
            rewrite <- a_eq in ak_grade.
            clear a' a_eq.
            destruct [|x] as [xk [x' x_eq]].
            pose proof (multilinear_to_tensor_grade U V _ x') as xk_grade.
            rewrite <- x_eq in xk_grade.
            clear x' x_eq.
            pose proof (tensor_mult_tm_grade U V _ _ _ _ ak_grade xk_grade)
                as mult_grade.
            symmetry; apply (tensor_grade_zero_eq U V _ (ak + xk)).
            -   exact mult_grade.
            -   intros contr.
                rewrite contr in k_lt.
                clear - k_lt.
                rewrite <- nle_lt in k_lt.
                apply k_lt.
                apply nat_le_self_rplus.
        }
        change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
        rewrite eq; clear eq.
        pose (z := 0 : multi_type k).
        assert (∀ (l : list (set_type (homogeneous_tensor U V))),
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
        assert (tensor_grade U V [a|] ak) as ak_grade.
        {
            unfold ak; clear ak.
            rewrite_ex_val ak [A a_eq].
            exists A.
            exact a_eq.
        }
        rewrite (tensor_sum_decompose_lmult U V a) by exact ak_grade.
        rewrite (tensor_sum_decompose_lmult U V a) by exact ak_grade.
        rewrite (tensor_sum_decompose_lmult U V a) by exact ak_grade.
        remember (list_nth (tensor_decompose_grade U V (b + c)) _ _) as bc'.
        remember (list_nth (tensor_decompose_grade U V b) _ _) as b'.
        remember (list_nth (tensor_decompose_grade U V c) _ _) as c'.
        assert ((tensor_mult_base U V) a bc' = (tensor_mult_base U V) a b' + (tensor_mult_base U V) a c') as eq.
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
            pose proof (tensor_decompose_plus_nth U V) as tensor_decompose_plus_nth.
            rewrite tensor_decompose_plus_nth in bc_eq.
            change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
            classic_case (0 = B) as [B_z|B_nz].
            1: {
                subst.
                rewrite b_eq in bc_eq.
                rewrite multilinear_to_tensor_zero in bc_eq.
                rewrite plus_lid in bc_eq.
                rewrite c_eq in bc_eq.
                classic_case (0 = C) as [C_z|C_nz].
                -   subst.
                    rewrite multilinear_to_tensor_zero in bc_eq.
                    rewrite <- (multilinear_to_tensor_zero U V bck) in bc_eq.
                    apply multilinear_to_tensor_eq in bc_eq.
                    subst BC.
                    unfold multi_type in *.
                    pose proof (multilinear_mult_ranni U (multilinear_type U V 1))
                        as multilinear_mult_ranni.
                    do 3 rewrite multilinear_mult_ranni.
                    do 3 rewrite multilinear_to_tensor_zero.
                    rewrite plus_rid.
                    reflexivity.
                -   pose proof (multilinear_to_tensor_eq_grade U V
                        _ _ _ _ C_nz bc_eq) as k_eq.
                    subst.
                    apply multilinear_to_tensor_eq in bc_eq.
                    subst.
                    unfold multi_type in *.
                    pose proof (multilinear_mult_ranni U (multilinear_type U V 1))
                        as multilinear_mult_ranni.
                    rewrite multilinear_mult_ranni.
                    rewrite multilinear_to_tensor_zero.
                    rewrite plus_lid.
                    reflexivity.
            }
            classic_case (0 = C) as [C_z|C_nz].
            1: {
                subst.
                rewrite c_eq in bc_eq.
                rewrite multilinear_to_tensor_zero in bc_eq.
                rewrite plus_rid in bc_eq.
                rewrite b_eq in bc_eq.
                pose proof (multilinear_to_tensor_eq_grade U V
                    _ _ _ _ B_nz bc_eq) as k_eq.
                subst.
                apply multilinear_to_tensor_eq in bc_eq.
                subst.
                unfold multi_type in *.
                pose proof (multilinear_mult_ranni U (multilinear_type U V 1))
                    as multilinear_mult_ranni.
                rewrite multilinear_mult_ranni.
                rewrite multilinear_to_tensor_zero.
                rewrite plus_rid.
                reflexivity.
            }
            assert (bk = k) as bk_eq.
            {
                pose proof (tensor_decompose_nth_grade U V b k) as eq.
                change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
                rewrite b_eq in eq.
                pose proof (multilinear_to_tensor_grade U V _ B) as B_grade.
                apply (tensor_grade_unique U V (multilinear_to_tensor U V B));
                    try assumption.
                intros contr.
                apply B_nz.
                apply (multilinear_to_tensor_eq U V).
                rewrite multilinear_to_tensor_zero.
                exact contr.
            }
            assert (ck = k) as ck_eq.
            {
                pose proof (tensor_decompose_nth_grade U V c k) as eq.
                change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
                rewrite c_eq in eq.
                pose proof (multilinear_to_tensor_grade U V _ C) as C_grade.
                apply (tensor_grade_unique U V (multilinear_to_tensor U V C));
                    try assumption.
                intros contr.
                apply C_nz.
                apply (multilinear_to_tensor_eq U V).
                rewrite multilinear_to_tensor_zero.
                exact contr.
            }
            subst bk ck.
            pose proof (multilinear_to_tensor_plus U V) as stupid.
            rewrite stupid.
            classic_case (0 = BC) as [BC_z|BC_nz].
            1: {
                subst.
                rewrite b_eq, c_eq in bc_eq.
                rewrite stupid in bc_eq; clear stupid.
                rewrite multilinear_to_tensor_zero in bc_eq.
                rewrite <- (multilinear_to_tensor_zero U V k) in bc_eq.
                apply multilinear_to_tensor_eq in bc_eq.
                unfold multi_type in *.
                unfold multilinear_type in *.
                rewrite <- multilinear_mult_ldist.
                unfold multi_type in *.
                unfold multilinear_type in *.
                rewrite bc_eq.
                pose proof (multilinear_mult_ranni U (multilinear_type U V 1))
                    as multilinear_mult_ranni.
                do 2 rewrite multilinear_mult_ranni.
                do 2 rewrite multilinear_to_tensor_zero.
                reflexivity.
            }
            assert (bck = k) as bck_eq.
            {
                pose proof (tensor_decompose_nth_grade U V (b + c) k) as eq.
                rewrite tensor_decompose_plus_nth in eq.
                change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
                rewrite bc_eq in eq.
                pose proof (multilinear_to_tensor_grade U V _ BC) as BC_grade.
                apply (tensor_grade_unique U V (multilinear_to_tensor U V BC));
                    try assumption.
                intros contr.
                apply BC_nz.
                apply (multilinear_to_tensor_eq U V).
                rewrite multilinear_to_tensor_zero.
                exact contr.
            }
            subst bck.
            apply f_equal.
            rewrite b_eq, c_eq in bc_eq.
            rewrite stupid in bc_eq.
            apply multilinear_to_tensor_eq in bc_eq.
            rewrite <- bc_eq.
            apply multilinear_mult_ldist.
        }
        rewrite eq.
        reflexivity.
Qed.

Program Instance tensor_mult_rdist : Rdist (tensor_algebra U V).
Next Obligation.
    rename a into b, b into c, c into a.
    unfold mult; cbn.
    remember (tensor_decompose_grade U V a) as al.
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
    rewrite (plus_comm (list_sum (list_image (tensor_decompose_grade U V b) _))).
    rewrite <- plus_assoc.
    apply lplus.
    rewrite (plus_comm (list_sum _)).
    apply set_type_eq.
    apply functional_ext.
    intros k.
    unfold plus at 2; cbn.
    do 3 rewrite tensor_list_sum_k.
    do 3 rewrite list_image_comp.
    pose (ak := ex_val [|a]).
    classic_case (k < ak) as [k_lt|k_ge].
    -   assert ((λ x, [(tensor_mult_base U V) x a|] k) = (λ x, 0)) as eq.
        {
            apply functional_ext.
            intros x.
            unfold ak in k_lt; clear ak.
            rewrite_ex_val ak [a' a_eq].
            pose proof (multilinear_to_tensor_grade U V _ a') as ak_grade.
            rewrite <- a_eq in ak_grade.
            clear a' a_eq.
            destruct [|x] as [xk [x' x_eq]].
            pose proof (multilinear_to_tensor_grade U V _ x') as xk_grade.
            rewrite <- x_eq in xk_grade.
            clear x' x_eq.
            pose proof (tensor_mult_tm_grade U V _ _ _ _ xk_grade ak_grade)
                as mult_grade.
            symmetry; apply (tensor_grade_zero_eq U V _ (xk + ak)).
            -   exact mult_grade.
            -   intros contr.
                rewrite contr in k_lt.
                clear - k_lt.
                rewrite <- nle_lt in k_lt.
                apply k_lt.
                apply nat_le_self_lplus.
        }
        change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
        rewrite eq; clear eq.
        pose (z := 0 : multi_type k).
        assert (∀ (l : list (set_type (homogeneous_tensor U V))),
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
        assert (tensor_grade U V [a|] ak) as ak_grade.
        {
            unfold ak; clear ak.
            rewrite_ex_val ak [A a_eq].
            exists A.
            exact a_eq.
        }
        pose proof (tensor_sum_decompose_rmult U V a) as tensor_sum_decompose_rmult.
        rewrite tensor_sum_decompose_rmult by exact ak_grade.
        rewrite tensor_sum_decompose_rmult by exact ak_grade.
        rewrite tensor_sum_decompose_rmult by exact ak_grade.
        remember (list_nth (tensor_decompose_grade U V (b + c)) _ _) as bc'.
        remember (list_nth (tensor_decompose_grade U V b) _ _) as b'.
        remember (list_nth (tensor_decompose_grade U V c) _ _) as c'.
        assert ((tensor_mult_base U V) bc' a = (tensor_mult_base U V) b' a + (tensor_mult_base U V) c' a) as eq.
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
            pose proof (tensor_decompose_plus_nth U V) as tensor_decompose_plus_nth.
            rewrite tensor_decompose_plus_nth in bc_eq.
            change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
            classic_case (0 = B) as [B_z|B_nz].
            1: {
                subst.
                rewrite b_eq in bc_eq.
                rewrite multilinear_to_tensor_zero in bc_eq.
                rewrite plus_lid in bc_eq.
                rewrite c_eq in bc_eq.
                classic_case (0 = C) as [C_z|C_nz].
                -   subst.
                    rewrite multilinear_to_tensor_zero in bc_eq.
                    rewrite <- (multilinear_to_tensor_zero U V bck) in bc_eq.
                    apply multilinear_to_tensor_eq in bc_eq.
                    subst BC.
                    unfold multi_type in *.
                    pose proof (multilinear_mult_lanni U (multilinear_type U V 1))
                        as multilinear_mult_lanni.
                    do 3 rewrite multilinear_mult_lanni.
                    do 3 rewrite multilinear_to_tensor_zero.
                    rewrite plus_rid.
                    reflexivity.
                -   pose proof (multilinear_to_tensor_eq_grade U V
                        _ _ _ _ C_nz bc_eq) as k_eq.
                    subst.
                    apply multilinear_to_tensor_eq in bc_eq.
                    subst.
                    unfold multi_type in *.
                    pose proof (multilinear_mult_lanni U (multilinear_type U V 1))
                        as multilinear_mult_lanni.
                    rewrite multilinear_mult_lanni.
                    rewrite multilinear_to_tensor_zero.
                    rewrite plus_lid.
                    reflexivity.
            }
            classic_case (0 = C) as [C_z|C_nz].
            1: {
                subst.
                rewrite c_eq in bc_eq.
                rewrite multilinear_to_tensor_zero in bc_eq.
                rewrite plus_rid in bc_eq.
                rewrite b_eq in bc_eq.
                pose proof (multilinear_to_tensor_eq_grade U V
                    _ _ _ _ B_nz bc_eq) as k_eq.
                subst.
                apply multilinear_to_tensor_eq in bc_eq.
                subst.
                unfold multi_type in *.
                pose proof (multilinear_mult_lanni U (multilinear_type U V 1))
                    as multilinear_mult_lanni.
                rewrite multilinear_mult_lanni.
                rewrite multilinear_to_tensor_zero.
                rewrite plus_rid.
                reflexivity.
            }
            assert (bk = k) as bk_eq.
            {
                pose proof (tensor_decompose_nth_grade U V b k) as eq.
                change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
                rewrite b_eq in eq.
                pose proof (multilinear_to_tensor_grade U V _ B) as B_grade.
                apply (tensor_grade_unique U V (multilinear_to_tensor U V B));
                    try assumption.
                intros contr.
                apply B_nz.
                apply (multilinear_to_tensor_eq U V).
                rewrite multilinear_to_tensor_zero.
                exact contr.
            }
            assert (ck = k) as ck_eq.
            {
                pose proof (tensor_decompose_nth_grade U V c k) as eq.
                change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
                rewrite c_eq in eq.
                pose proof (multilinear_to_tensor_grade U V _ C) as C_grade.
                apply (tensor_grade_unique U V (multilinear_to_tensor U V C));
                    try assumption.
                intros contr.
                apply C_nz.
                apply (multilinear_to_tensor_eq U V).
                rewrite multilinear_to_tensor_zero.
                exact contr.
            }
            subst bk ck.
            pose proof (multilinear_to_tensor_plus U V)
                as multilinear_to_tensor_plus.
            rewrite multilinear_to_tensor_plus.
            classic_case (0 = BC) as [BC_z|BC_nz].
            1: {
                subst.
                rewrite b_eq, c_eq in bc_eq.
                rewrite multilinear_to_tensor_plus in bc_eq.
                rewrite multilinear_to_tensor_zero in bc_eq.
                rewrite <- (multilinear_to_tensor_zero U V k) in bc_eq.
                apply multilinear_to_tensor_eq in bc_eq.
                unfold multi_type in *.
                unfold multilinear_type in *.
                rewrite <- multilinear_mult_rdist.
                unfold multi_type in *.
                unfold multilinear_type in *.
                rewrite bc_eq.
                pose proof (multilinear_mult_lanni U (multilinear_type U V 1))
                    as multilinear_mult_lanni.
                do 2 rewrite multilinear_mult_lanni.
                do 2 rewrite multilinear_to_tensor_zero.
                reflexivity.
            }
            assert (bck = k) as bck_eq.
            {
                pose proof (tensor_decompose_nth_grade U V (b + c) k) as eq.
                rewrite tensor_decompose_plus_nth in eq.
                change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
                rewrite bc_eq in eq.
                pose proof (multilinear_to_tensor_grade U V _ BC) as BC_grade.
                apply (tensor_grade_unique U V (multilinear_to_tensor U V BC));
                    try assumption.
                intros contr.
                apply BC_nz.
                apply (multilinear_to_tensor_eq U V).
                rewrite multilinear_to_tensor_zero.
                exact contr.
            }
            subst bck.
            apply f_equal.
            rewrite b_eq, c_eq in bc_eq.
            rewrite multilinear_to_tensor_plus in bc_eq.
            apply multilinear_to_tensor_eq in bc_eq.
            rewrite <- bc_eq.
            apply multilinear_mult_rdist.
        }
        rewrite eq.
        reflexivity.
Qed.

Program Instance tensor_mult_assoc : MultAssoc (tensor_algebra U V).
Next Obligation.
    rewrite (tensor_decompose_grade_eq U V a).
    rewrite (tensor_decompose_grade_eq U V b).
    rewrite (tensor_decompose_grade_eq U V c).
    rename a into A, b into B, c into C.
    remember (tensor_decompose_grade U V A) as al.
    remember (tensor_decompose_grade U V B) as bl.
    remember (tensor_decompose_grade U V C) as cl.
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
    do 3 rewrite tensor_lmult_homogeneous2.
    fold (tensor_mult_base U V).
    do 3 rewrite tensor_rmult_homogeneous2.
    fold (tensor_mult_base U V).
    do 3 rewrite list_prod2_lconc.
    do 3 rewrite list_prod2_lend.
    cbn.
    do 3 rewrite plus_lid.
    do 2 rewrite plus_rid.
    assert (list_sum (list_image
        (tensor_decompose_grade U V ((tensor_mult_base U V) b c)) (λ x, (tensor_mult_base U V) a x)) =
        list_sum (list_prod2 (tensor_mult_base U V) (a :: list_end)
        (tensor_decompose_grade U V ((tensor_mult_base U V) b c)))) as eq.
    {
        rewrite list_prod2_lconc.
        rewrite list_prod2_lend.
        cbn; rewrite plus_lid.
        reflexivity.
    }
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    unfold T1, T8, T25, T28 in *.
    rewrite eq; clear eq.
    pose proof (tensor_mult_homogeneous U V a b) as ab_homo.
    pose proof (tensor_lmult_homogeneous2 U V [_|ab_homo] (c :: list_end)) as eq.
    cbn in eq.
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    rewrite eq; clear eq.
    pose proof (tensor_mult_homogeneous U V b c) as bc_homo.
    pose proof (tensor_rmult_homogeneous2 U V (a :: list_end) [_|bc_homo]) as eq.
    cbn in eq.
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    rewrite eq; clear eq.
Local Arguments list_prod2: simpl nomatch.
    cbn.
    (* TODO: Figure out why this takes so long *)
    do 2 rewrite plus_rid.
    clear A B C al.
    destruct a as [a a_homo]; cbn.
    destruct b as [b b_homo]; cbn.
    destruct c as [c c_homo]; cbn.
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    pose proof c_homo as [ck [C C_eq]].
    subst a b c.
    pose proof (multilinear_to_tensor_tm U V _ _ B C b_homo c_homo) as eq.
    assert (homogeneous_tensor U V (multilinear_to_tensor U V (multilinear_mult _ _ B C)))
        as bc_homo2.
    {
        exists (bk + ck), (multilinear_mult _ _ B C).
        reflexivity.
    }
    assert ([(tensor_mult_base U V) [_|b_homo] [_|c_homo] | bc_homo] = [_|bc_homo2]) as eq2.
    {
        apply set_type_eq; exact eq.
    }
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    rewrite eq2.
    rewrite multilinear_to_tensor_tm.
    clear eq eq2 bc_homo bc_homo2.
    pose proof (multilinear_to_tensor_tm U V _ _ A B a_homo b_homo) as eq.
    assert (homogeneous_tensor U V (multilinear_to_tensor U V (multilinear_mult _ _ A B)))
        as ab_homo2.
    {
        exists (ak + bk), (multilinear_mult _ _ A B).
        reflexivity.
    }
    assert ([(tensor_mult_base U V) [_|a_homo] [_|b_homo] | ab_homo] = [_|ab_homo2]) as eq2.
    {
        apply set_type_eq; exact eq.
    }
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    rewrite eq2.
    rewrite multilinear_to_tensor_tm.
    clear eq eq2 ab_homo ab_homo2 a_homo b_homo c_homo.
    rewrite multilinear_mult_assoc.
    symmetry.
    apply multilinear_to_tensor_k_eq.
Qed.

End TensorAlgebra.
