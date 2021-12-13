Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_algebra_grade.
Require Import tensor_product_universal.
Require Import tensor_power.
Require Import module_category.

Require Import nat.
Require Import card.
Require Import set.
Require Import list.
Require Import plus_sum.

(** This file contains the base definition of tensor multiplication and theorems
about it.  For the actual instance of Mult, see tensor_algebra_mult2.
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

Local Open Scope card_scope.
(* end hide *)
Let k_tensor k := module_V (tensor_power V k).

Definition tensor_mult_base (A' B' : set_type (homogeneous_tensor V))
    := power_to_tensor V (module_homo_f (tensor_power_mult V _ _)
        (tensor_mult _ _ (ex_val (ex_proof [|A']))
        (ex_val (ex_proof [|B'])))).

Lemma tensor_mult_tm_grade : ∀ A B k1 k2,
        tensor_grade V [A|] k1 → tensor_grade V [B|] k2 →
        tensor_grade V (tensor_mult_base A B) (k1 + k2).
    intros A B k1 k2 k1_grade k2_grade.
    unfold tensor_mult_base.
    unfold tensor_grade in *.
    destruct A as [A A_homo], B as [B B_homo]; cbn in *.
    unfold ex_proof.
    destruct (ex_to_type _) as [k1' C0]; cbn.
    destruct (ex_to_type _) as [k2' C1]; cbn.
    rewrite_ex_val A' A_eq.
    rewrite_ex_val B' B_eq.
    clear C0 C1.
    subst A B.
    rename A' into A, B' into B.
    destruct k1_grade as [A' A_eq].
    destruct k2_grade as [B' B_eq].
    classic_case (0 = A) as [A_z|A_nz].
    1: {
        subst.
        exists 0.
        rewrite (tensor_product_lanni (tensor_power V k1')).
        rewrite module_homo_zero.
        unfold TZ.
        do 2 rewrite power_to_tensor_zero.
        reflexivity.
    }
    classic_case (0 = B) as [B_z|B_nz].
    1: {
        subst.
        exists 0.
        rewrite (tensor_product_ranni (tensor_power V k1')).
        rewrite module_homo_zero.
        unfold TZ.
        do 2 rewrite power_to_tensor_zero.
        reflexivity.
    }
    apply power_to_tensor_eq_grade in A_eq; try assumption.
    apply power_to_tensor_eq_grade in B_eq; try assumption.
    subst.
    exists (module_homo_f (tensor_power_mult V _ _) (tensor_mult _ _ A B)).
    reflexivity.
Qed.

Lemma tensor_lmult_homogeneous : ∀ a b,
        list_sum (list_image (tensor_decompose_grade V [a|]) (λ x, tensor_mult_base x b)) =
        tensor_mult_base a b.
    intros a b.
    destruct a as [a a_homo].
    destruct b as [b b_homo].
    cbn.
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    subst a b.
    assert (list_image (tensor_decompose_grade V (power_to_tensor V A))
        (λ x, tensor_mult_base x [_|b_homo]) = func_to_list (λ n, If n = ak
            then tensor_mult_base [_|a_homo] [_|b_homo] else 0)
            (tensor_max_nz V (power_to_tensor V A))) as eq.
    {
        unfold tensor_decompose_grade.
        rewrite func_to_list_image.
        apply f_equal2.
        2: reflexivity.
        apply functional_ext.
        intros x.
        assert ([_|tensor_project_homogeneous V (power_to_tensor V A) x] =
            If x = ak then [_|a_homo] else [_|tensor_zero_homogeneous V]) as eq.
        {
            case_if.
            -   subst x.
                apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros x.
                unfold power_to_tensor_base.
                case_if; reflexivity.
            -   apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros y.
                unfold power_to_tensor_base.
                case_if; destruct (strong_excluded_middle (ak = y)) as [eq|neq].
                all: subst; cbn.
                1: contradiction.
                all: reflexivity.
        }
        rewrite eq; clear eq.
        case_if.
        1: reflexivity.
        unfold tensor_mult_base; cbn.
        unfold ex_proof at 1.
        destruct (ex_to_type _) as [zk C0]; cbn.
        rewrite_ex_val Z Z_eq.
        clear C0.
        rewrite <- (power_to_tensor_zero V zk) in Z_eq.
        apply power_to_tensor_eq in Z_eq.
        subst Z.
        rewrite tensor_product_lanni.
        rewrite module_homo_zero.
        apply power_to_tensor_zero.
    }
    rewrite eq; clear eq.
    classic_case (0 = A) as [A_z|A_nz].
    {
        subst A.
        assert (tensor_mult_base [_|a_homo] [_|b_homo] = 0) as eq.
        {
            unfold tensor_mult_base; cbn.
            unfold ex_proof.
            destruct (ex_to_type _) as [ak' C0]; cbn.
            destruct (ex_to_type _) as [bk' C1]; cbn.
            rewrite_ex_val A' A'_eq.
            rewrite_ex_val B' B'_eq.
            unfold TZ in A'_eq.
            rewrite power_to_tensor_zero in A'_eq.
            rewrite <- (power_to_tensor_zero V ak') in A'_eq.
            apply power_to_tensor_eq in A'_eq.
            subst A'.
            rewrite tensor_product_lanni.
            rewrite module_homo_zero.
            apply power_to_tensor_zero.
        }
        change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
        rewrite eq.
        unfold TZ; rewrite power_to_tensor_zero.
        change (set_type (tensor_finite V)) with (tensor_algebra_base V).
        remember (tensor_max_nz V 0) as n.
        clear Heqn.
        nat_induction n.
        -   unfold zero; cbn.
            reflexivity.
        -   cbn.
            unfold func_to_list in IHn.
            rewrite list_sum_plus.
            rewrite IHn.
            cbn.
            rewrite plus_lid, plus_rid.
            case_if; reflexivity.
    }
    apply list_sum_func_single.
    apply tensor_max_nz_leq.
    intros contr.
    cbn in contr.
    unfold power_to_tensor_base in contr.
    destruct (strong_excluded_middle (ak = ak)) as [eq|neq].
    2: contradiction.
    destruct eq; cbn in contr.
    contradiction.
Qed.
Lemma tensor_lmult_homogeneous2 : ∀ (a : set_type (homogeneous_tensor V)) bl,
        list_sum (list_prod2 tensor_mult_base (tensor_decompose_grade V [a|]) bl) =
        list_sum (list_prod2 tensor_mult_base (a :: list_end) bl).
    intros a bl.
    rewrite list_prod2_lconc.
    rewrite list_prod2_lend.
    cbn; rewrite plus_lid.
    induction bl as [|b bl].
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite list_sum_plus.
        rewrite IHbl; clear IHbl.
        apply rplus; clear bl.
        rewrite list_prod2_base_image.
        apply tensor_lmult_homogeneous.
Qed.
Lemma tensor_rmult_homogeneous : ∀ a b,
        list_sum (list_image (tensor_decompose_grade V [b|]) (λ x, tensor_mult_base a x)) =
        tensor_mult_base a b.
    intros a b.
    destruct a as [a a_homo].
    destruct b as [b b_homo].
    cbn.
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    subst a b.
    assert (list_image (tensor_decompose_grade V (power_to_tensor V B))
        (λ x, tensor_mult_base [_|a_homo] x) = func_to_list (λ n, If n = bk
            then tensor_mult_base [_|a_homo] [_|b_homo] else 0)
            (tensor_max_nz V (power_to_tensor V B))) as eq.
    {
        unfold tensor_decompose_grade.
        rewrite func_to_list_image.
        apply f_equal2.
        2: reflexivity.
        apply functional_ext.
        intros x.
        assert ([_|tensor_project_homogeneous V (power_to_tensor V B) x] =
            If x = bk then [_|b_homo] else [_|tensor_zero_homogeneous V]) as eq.
        {
            case_if.
            -   subst x.
                apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros x.
                unfold power_to_tensor_base.
                case_if; reflexivity.
            -   apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros y.
                unfold power_to_tensor_base.
                case_if; destruct (strong_excluded_middle (bk = y)) as [eq|neq].
                all: subst; cbn.
                1: contradiction.
                all: reflexivity.
        }
        rewrite eq; clear eq.
        case_if.
        1: reflexivity.
        unfold tensor_mult_base; cbn.
        unfold ex_proof at 2.
        remember (ex_to_type (tensor_zero_homogeneous V)) as z_ex.
        clear Heqz_ex.
        destruct (z_ex) as [zk C0]; cbn.
        rewrite_ex_val_with C0 Z Z_eq.
        clear C0.
        rewrite <- (power_to_tensor_zero V zk) in Z_eq.
        apply power_to_tensor_eq in Z_eq.
        subst Z.
        rewrite tensor_product_ranni.
        rewrite module_homo_zero.
        apply power_to_tensor_zero.
    }
    rewrite eq; clear eq.
    classic_case (0 = B) as [A_z|A_nz].
    {
        subst B.
        assert (tensor_mult_base [_|a_homo] [_|b_homo] = 0) as eq.
        {
            unfold tensor_mult_base; cbn.
            unfold ex_proof.
            destruct (ex_to_type _) as [ak' C0]; cbn.
            destruct (ex_to_type _) as [bk' C1]; cbn.
            rewrite_ex_val A' A'_eq.
            rewrite_ex_val B' B'_eq.
            unfold TZ in B'_eq; rewrite power_to_tensor_zero in B'_eq.
            rewrite <- (power_to_tensor_zero V bk') in B'_eq.
            apply power_to_tensor_eq in B'_eq.
            subst B'.
            rewrite tensor_product_ranni.
            rewrite module_homo_zero.
            apply power_to_tensor_zero.
        }
        change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
        rewrite eq.
        unfold TZ; rewrite power_to_tensor_zero.
        change (set_type (tensor_finite V)) with (tensor_algebra_base V).
        remember (tensor_max_nz V 0) as n.
        clear Heqn.
        nat_induction n.
        -   unfold zero; cbn.
            reflexivity.
        -   cbn.
            unfold func_to_list in IHn.
            rewrite list_sum_plus.
            rewrite IHn.
            cbn.
            rewrite plus_lid, plus_rid.
            case_if; reflexivity.
    }
    apply list_sum_func_single.
    apply tensor_max_nz_leq.
    intros contr.
    cbn in contr.
    unfold power_to_tensor_base in contr.
    destruct (strong_excluded_middle (bk = bk)) as [eq|neq].
    2: contradiction.
    destruct eq; cbn in contr.
    contradiction.
Qed.
Lemma tensor_rmult_homogeneous2 : ∀ al (b : set_type (homogeneous_tensor V)),
        list_sum (list_prod2 tensor_mult_base al (tensor_decompose_grade V [b|])) =
        list_sum (list_prod2 tensor_mult_base al (b :: list_end)).
    intros al b.
    rewrite list_prod2_rconc.
    rewrite list_prod2_rend.
    cbn; rewrite plus_lid.
    induction al as [|a al].
    -   rewrite list_prod2_lend.
        cbn.
        reflexivity.
    -   cbn.
        rewrite list_prod2_lconc.
        rewrite IHal; clear IHal.
        rewrite plus_comm.
        apply rplus; clear al.
        apply tensor_rmult_homogeneous.
Qed.

Lemma tensor_sum_decompose_lmult : ∀ a B ak k, tensor_grade V [a|] ak →
        list_sum (list_image (tensor_decompose_grade V B)
                             (λ x, [tensor_mult_base a x|] (ak + k)))
        = [tensor_mult_base a (list_nth (tensor_decompose_grade V B) k
            [_|tensor_zero_homogeneous V])|] (ak + k).
    intros a B ak k ak_grade.
    pose proof (tensor_decompose_nth V B k) as eq.
    assert (homogeneous_tensor V (power_to_tensor V ([B|] k))) as B_homo.
    {
        exists k, ([B|] k).
        reflexivity.
    }
    assert (list_nth (tensor_decompose_grade V B) k [0|tensor_zero_homogeneous V]
        = [_|B_homo]) as eq2.
    {
        apply set_type_eq; cbn.
        exact eq.
    }
    rewrite eq2.
    clear eq eq2.
    assert (list_image (tensor_decompose_grade V B) (λ x, [tensor_mult_base a x|] (ak + k)) =
        func_to_list (λ n, If n = k then [tensor_mult_base a [_|B_homo]|] (ak + k) else 0)
        (tensor_max_nz V B)) as eq.
    {
        unfold tensor_decompose_grade.
        rewrite func_to_list_image.
        apply f_equal2.
        2: reflexivity.
        apply functional_ext.
        intros x.
        case_if.
        -   subst x.
            assert ([_|tensor_project_homogeneous V B k] = [_|B_homo]) as eq.
            {
                apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros x.
                unfold power_to_tensor_base.
                case_if.
                -   subst.
                    cbn.
                    reflexivity.
                -   reflexivity.
            }
            rewrite eq.
            reflexivity.
        -   cbn.
            unfold ex_proof.
            destruct (ex_to_type _) as [ak' C0]; cbn.
            destruct (ex_to_type _) as [x' C1]; cbn.
            rewrite_ex_val A' A_eq.
            rewrite_ex_val B' B_eq.
            clear C0 C1.
            classic_case (0 = A') as [A_z|A_nz].
            {
                subst.
                rewrite (tensor_product_lanni (tensor_power V ak')).
                rewrite module_homo_zero.
                pose proof (power_to_tensor_zero V (ak' + x')) as eq.
                unfold power_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                rewrite eq.
                reflexivity.
            }
            classic_case (0 = B') as [B_z|B_nz].
            {
                subst.
                rewrite (tensor_product_ranni (tensor_power V ak')).
                rewrite module_homo_zero.
                pose proof (power_to_tensor_zero V (ak' + x')) as eq.
                unfold power_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                rewrite eq.
                reflexivity.
            }
            assert (ak = ak') as eq.
            {
                apply (tensor_grade_unique V (power_to_tensor V A')).
                -   intros contr.
                    pose proof (power_to_tensor_zero V ak') as eq.
                    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in eq.
                    rewrite <- eq in contr.
                    apply power_to_tensor_eq in contr.
                    contradiction.
                -   rewrite <- A_eq.
                    exact ak_grade.
                -   exists A'.
                    reflexivity.
            }
            assert (x = x') as eq2.
            {
                apply (tensor_grade_unique V (power_to_tensor V B')).
                -   intros contr.
                    pose proof (power_to_tensor_zero V x') as eq2.
                    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in eq2.
                    rewrite <- eq2 in contr.
                    apply power_to_tensor_eq in contr.
                    contradiction.
                -   rewrite <- B_eq.
                    apply tensor_project_grade.
                -   exists B'.
                    reflexivity.
            }
            subst ak' x'.
            unfold power_to_tensor_base.
            destruct (strong_excluded_middle (ak + x = ak + k)) as [eq|neq].
            +   exfalso.
                apply plus_lcancel in eq.
                contradiction.
            +   reflexivity.
    }
    rewrite eq; clear eq.
    classic_case (0 = [B|] k) as [B_z|B_nz].
    {
        assert ([power_to_tensor V ([B|] k) | B_homo]
            = [_|tensor_zero_homogeneous V]) as eq.
        {
            apply set_type_eq; cbn.
            rewrite <- B_z.
            apply power_to_tensor_zero.
        }
        rewrite eq; clear eq.
        assert ([tensor_mult_base a [_|tensor_zero_homogeneous V]|] (ak + k) = 0) as eq.
        {
            cbn.
            unfold ex_proof.
            destruct (ex_to_type _) as [ak' C0]; cbn.
            destruct (ex_to_type _) as [zk C1]; cbn.
            rewrite_ex_val A A_eq.
            rewrite_ex_val Z Z_eq.
            clear C0 C1.
            rewrite <- (power_to_tensor_zero V zk) in Z_eq.
            apply power_to_tensor_eq in Z_eq.
            subst Z.
            rewrite tensor_product_ranni.
            rewrite module_homo_zero.
            pose proof (power_to_tensor_zero V (ak' + zk)) as eq.
            apply eq_set_type in eq; cbn in eq.
            rewrite eq.
            reflexivity.
        }
        rewrite eq.
        remember (tensor_max_nz V B) as m.
        clear Heqm.
        rewrite func_to_list2_eq.
        unfold func_to_list2.
        remember (zero (U := nat)) as z.
        clear Heqz.
        revert z.
        nat_induction m.
        -   unfold zero; cbn.
            reflexivity.
        -   cbn.
            intros z.
            rewrite IHm.
            rewrite plus_rid.
            case_if; reflexivity.
    }
    apply list_sum_func_single.
    apply (tensor_max_nz_leq V _ _ B_nz).
Qed.
Lemma tensor_sum_decompose_rmult : ∀ a B ak k, tensor_grade V [a|] ak →
        list_sum (list_image (tensor_decompose_grade V B)
                             (λ x, [tensor_mult_base x a|] (k + ak)))
        = [tensor_mult_base (list_nth (tensor_decompose_grade V B) k
            [_|tensor_zero_homogeneous V]) a|] (k + ak).
    intros a B ak k ak_grade.
    pose proof (tensor_decompose_nth V B k) as eq.
    assert (homogeneous_tensor V (power_to_tensor V ([B|] k))) as B_homo.
    {
        exists k, ([B|] k).
        reflexivity.
    }
    assert (list_nth (tensor_decompose_grade V B) k [0|tensor_zero_homogeneous V]
        = [_|B_homo]) as eq2.
    {
        apply set_type_eq; cbn.
        exact eq.
    }
    rewrite eq2.
    clear eq eq2.
    assert (list_image (tensor_decompose_grade V B) (λ x, [tensor_mult_base x a|] (k + ak)) =
        func_to_list (λ n, If n = k then [tensor_mult_base [_|B_homo] a|] (k + ak) else 0)
        (tensor_max_nz V B)) as eq.
    {
        unfold tensor_decompose_grade.
        rewrite func_to_list_image.
        apply f_equal2.
        2: reflexivity.
        apply functional_ext.
        intros x.
        case_if.
        -   subst x.
            assert ([_|tensor_project_homogeneous V B k] = [_|B_homo]) as eq.
            {
                apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros x.
                unfold power_to_tensor_base.
                case_if.
                -   subst.
                    cbn.
                    reflexivity.
                -   reflexivity.
            }
            rewrite eq.
            reflexivity.
        -   cbn.
            unfold ex_proof.
            destruct (ex_to_type _) as [x' C1]; cbn.
            destruct (ex_to_type _) as [ak' C0]; cbn.
            rewrite_ex_val B' B_eq.
            rewrite_ex_val A' A_eq.
            clear C0 C1.
            classic_case (0 = A') as [A_z|A_nz].
            {
                subst.
                rewrite (tensor_product_ranni (tensor_power V x')).
                rewrite module_homo_zero.
                pose proof (power_to_tensor_zero V (x' + ak')) as eq.
                unfold power_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                rewrite eq.
                reflexivity.
            }
            classic_case (0 = B') as [B_z|B_nz].
            {
                subst.
                rewrite (tensor_product_lanni (tensor_power V x')).
                rewrite module_homo_zero.
                pose proof (power_to_tensor_zero V (x' + ak')) as eq.
                unfold power_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                rewrite eq.
                reflexivity.
            }
            assert (ak = ak') as eq.
            {
                apply (tensor_grade_unique V (power_to_tensor V A')).
                -   intros contr.
                    pose proof (power_to_tensor_zero V ak') as eq.
                    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in eq.
                    rewrite <- eq in contr.
                    apply power_to_tensor_eq in contr.
                    contradiction.
                -   rewrite <- A_eq.
                    exact ak_grade.
                -   exists A'.
                    reflexivity.
            }
            assert (x = x') as eq2.
            {
                apply (tensor_grade_unique V (power_to_tensor V B')).
                -   intros contr.
                    pose proof (power_to_tensor_zero V x') as eq2.
                    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in eq2.
                    rewrite <- eq2 in contr.
                    apply power_to_tensor_eq in contr.
                    contradiction.
                -   rewrite <- B_eq.
                    apply tensor_project_grade.
                -   exists B'.
                    reflexivity.
            }
            subst ak' x'.
            unfold power_to_tensor_base.
            destruct (strong_excluded_middle (x + ak = k + ak)) as [eq|neq].
            +   exfalso.
                apply plus_rcancel in eq.
                contradiction.
            +   reflexivity.
    }
    rewrite eq; clear eq.
    classic_case (0 = [B|] k) as [B_z|B_nz].
    {
        assert ([power_to_tensor V ([B|] k) | B_homo]
            = [_|tensor_zero_homogeneous V]) as eq.
        {
            apply set_type_eq; cbn.
            rewrite <- B_z.
            apply power_to_tensor_zero.
        }
        rewrite eq; clear eq.
        assert ([tensor_mult_base [_|tensor_zero_homogeneous V] a|] (k + ak) = 0) as eq.
        {
            cbn.
            unfold ex_proof.
            destruct (ex_to_type _) as [zk C1]; cbn.
            destruct (ex_to_type _) as [ak' C0]; cbn.
            rewrite_ex_val Z Z_eq.
            rewrite_ex_val A A_eq.
            clear C0 C1.
            rewrite <- (power_to_tensor_zero V zk) in Z_eq.
            apply power_to_tensor_eq in Z_eq.
            subst Z.
            rewrite tensor_product_lanni.
            rewrite module_homo_zero.
            pose proof (power_to_tensor_zero V (zk + ak')) as eq.
            apply eq_set_type in eq; cbn in eq.
            rewrite eq.
            reflexivity.
        }
        rewrite eq.
        remember (tensor_max_nz V B) as m.
        clear Heqm.
        rewrite func_to_list2_eq.
        unfold func_to_list2.
        remember (zero (U := nat)) as z.
        clear Heqz.
        revert z.
        nat_induction m.
        -   unfold zero; cbn.
            reflexivity.
        -   cbn.
            intros z.
            rewrite IHm.
            rewrite plus_rid.
            case_if; reflexivity.
    }
    apply list_sum_func_single.
    apply (tensor_max_nz_leq V _ _ B_nz).
Qed.

Lemma tensor_mult_homogeneous : ∀ a b, homogeneous_tensor V (tensor_mult_base a b).
    intros a b.
    unfold tensor_mult_base.
    unfold ex_proof.
    destruct (ex_to_type _) as [ak C0]; cbn.
    destruct (ex_to_type _) as [bk C1]; cbn.
    rewrite_ex_val A A_eq.
    rewrite_ex_val B B_eq.
    clear C0 C1.
    exists (ak + bk), (module_homo_f (tensor_power_mult V ak bk) (tensor_mult _ _ A B)).
    reflexivity.
Qed.

Lemma power_to_tensor_tm :
        ∀ k1 k2 (A : k_tensor k1) (B : k_tensor k2) AH BH,
        tensor_mult_base [power_to_tensor V A|AH] [power_to_tensor V B|BH] =
        power_to_tensor V (module_homo_f (tensor_power_mult V _ _) (tensor_mult _ _ A B)).
    intros k1 k2 A B AH BH.
    unfold tensor_mult_base; cbn.
    unfold ex_proof.
    destruct (ex_to_type _) as [ak C0]; cbn.
    destruct (ex_to_type _) as [bk C1]; cbn.
    rewrite_ex_val A' A'_eq.
    rewrite_ex_val B' B'_eq.
    classic_case (0 = A) as [A_z|A_nz].
    {
        subst A.
        rewrite (power_to_tensor_zero V) in A'_eq.
        rewrite <- (power_to_tensor_zero V ak) in A'_eq.
        apply power_to_tensor_eq in A'_eq.
        subst A'.
        rewrite tensor_product_lanni.
        rewrite (tensor_product_lanni (tensor_power V k1)).
        do 2 rewrite module_homo_zero.
        do 2 rewrite power_to_tensor_zero.
        reflexivity.
    }
    classic_case (0 = B) as [B_z|B_nz].
    {
        subst B.
        rewrite (power_to_tensor_zero V) in B'_eq.
        rewrite <- (power_to_tensor_zero V bk) in B'_eq.
        apply power_to_tensor_eq in B'_eq.
        subst B'.
        rewrite tensor_product_ranni.
        rewrite (tensor_product_ranni (tensor_power V k1)).
        do 2 rewrite module_homo_zero.
        do 2 rewrite power_to_tensor_zero.
        reflexivity.
    }
    pose proof (power_to_tensor_eq_grade V _ _ A A' A_nz A'_eq).
    pose proof (power_to_tensor_eq_grade V _ _ B B' B_nz B'_eq).
    subst ak bk.
    apply power_to_tensor_eq in A'_eq, B'_eq.
    subst A' B'.
    reflexivity.
Qed.
(* begin hide *)
End TensorAlgebra.
(* end hide *)
