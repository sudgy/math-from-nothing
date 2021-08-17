Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_algebra_grade.
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
Existing Instances T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24.
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
Existing Instances T25 T26 T27 T28 T29 T30 T31 T32 T33 T34 T35 T36.

Let multi_type k := multilinear_type U (multilinear_type U V 1) k.

Local Open Scope card_scope.

Definition tensor_mult_base (A' B' : set_type (homogeneous_tensor U V))
    := multilinear_to_tensor U V (multilinear_mult _ _
        (ex_val (ex_proof [|A']))
        (ex_val (ex_proof [|B']))).

Lemma tensor_mult_tm_grade : ∀ A B k1 k2,
        tensor_grade U V [A|] k1 → tensor_grade U V [B|] k2 →
        tensor_grade U V (tensor_mult_base A B) (k1 + k2).
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
        unfold multi_type in *.
        pose proof (multilinear_mult_lanni U (multilinear_type U V 1))
            as multilinear_mult_lanni.
        rewrite multilinear_mult_lanni.
        do 2 rewrite multilinear_to_tensor_zero.
        reflexivity.
    }
    classic_case (0 = B) as [B_z|B_nz].
    1: {
        subst.
        exists 0.
        unfold multi_type in *.
        pose proof (multilinear_mult_ranni U (multilinear_type U V 1))
            as multilinear_mult_ranni.
        rewrite multilinear_mult_ranni.
        do 2 rewrite multilinear_to_tensor_zero.
        reflexivity.
    }
    apply multilinear_to_tensor_eq_grade in A_eq; try assumption.
    apply multilinear_to_tensor_eq_grade in B_eq; try assumption.
    subst.
    exists (multilinear_mult _ _ A B).
    reflexivity.
Qed.

Lemma tensor_list_sum_k : ∀ (al : list (tensor_algebra U V)) k,
        [list_sum al|] k = list_sum (list_image al (λ a, [a|] k)).
    intros al k.
    induction al.
    -   cbn.
        reflexivity.
    -   cbn.
        unfold plus at 1; cbn.
        rewrite IHal.
        reflexivity.
Qed.

Lemma tensor_lmult_homogeneous : ∀ a b,
        list_sum (list_image (tensor_decompose_grade U V [a|]) (λ x, tensor_mult_base x b)) =
        tensor_mult_base a b.
    intros a b.
    destruct a as [a a_homo].
    destruct b as [b b_homo].
    cbn.
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    subst a b.
    assert (list_image (tensor_decompose_grade U V (multilinear_to_tensor U V A))
        (λ x, tensor_mult_base x [_|b_homo]) = func_to_list (λ n, If n = ak
            then tensor_mult_base [_|a_homo] [_|b_homo] else 0)
            (tensor_max_nz U V (multilinear_to_tensor U V A))) as eq.
    {
        unfold tensor_decompose_grade.
        rewrite func_to_list_image.
        apply f_equal2.
        2: reflexivity.
        apply functional_ext.
        intros x.
        assert ([_|tensor_project_homogeneous U V (multilinear_to_tensor U V A) x] =
            If x = ak then [_|a_homo] else [_|tensor_zero_homogeneous U V]) as eq.
        {
            case_if.
            -   subst x.
                apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros x.
                unfold multilinear_to_tensor_base.
                case_if; reflexivity.
            -   apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros y.
                unfold multilinear_to_tensor_base.
                case_if; destruct (strong_excluded_middle (y = ak)) as [eq|neq].
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
        rewrite <- (multilinear_to_tensor_zero U V zk) in Z_eq.
        apply multilinear_to_tensor_eq in Z_eq.
        subst Z.
        unfold multi_type in *.
        rewrite multilinear_mult_lanni.
        apply multilinear_to_tensor_zero.
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
            rewrite multilinear_to_tensor_zero in A'_eq.
            rewrite <- (multilinear_to_tensor_zero U V ak') in A'_eq.
            apply multilinear_to_tensor_eq in A'_eq.
            subst A'.
            unfold multi_type in *.
            rewrite multilinear_mult_lanni.
            apply multilinear_to_tensor_zero.
        }
        change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
        rewrite eq.
        rewrite multilinear_to_tensor_zero.
        change (set_type (tensor_finite U V)) with (tensor_algebra U V).
        remember (tensor_max_nz U V 0) as n.
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
    unfold multilinear_to_tensor_base in contr.
    destruct (strong_excluded_middle (ak = ak)) as [eq|neq].
    2: contradiction.
    unfold multilinear_type_k_eq, Logic.eq_rect_r, Logic.eq_rect in contr.
    destruct (Logic.eq_sym _).
    contradiction.
Qed.
Lemma tensor_lmult_homogeneous2 : ∀ (a : set_type (homogeneous_tensor U V)) bl,
        list_sum (list_prod2 tensor_mult_base (tensor_decompose_grade U V [a|]) bl) =
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
        list_sum (list_image (tensor_decompose_grade U V [b|]) (λ x, tensor_mult_base a x)) =
        tensor_mult_base a b.
    intros a b.
    destruct a as [a a_homo].
    destruct b as [b b_homo].
    cbn.
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    subst a b.
    assert (list_image (tensor_decompose_grade U V (multilinear_to_tensor U V B))
        (λ x, tensor_mult_base [_|a_homo] x) = func_to_list (λ n, If n = bk
            then tensor_mult_base [_|a_homo] [_|b_homo] else 0)
            (tensor_max_nz U V (multilinear_to_tensor U V B))) as eq.
    {
        unfold tensor_decompose_grade.
        rewrite func_to_list_image.
        apply f_equal2.
        2: reflexivity.
        apply functional_ext.
        intros x.
        assert ([_|tensor_project_homogeneous U V (multilinear_to_tensor U V B) x] =
            If x = bk then [_|b_homo] else [_|tensor_zero_homogeneous U V]) as eq.
        {
            case_if.
            -   subst x.
                apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros x.
                unfold multilinear_to_tensor_base.
                case_if; reflexivity.
            -   apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros y.
                unfold multilinear_to_tensor_base.
                case_if; destruct (strong_excluded_middle (y = bk)) as [eq|neq].
                all: subst; cbn.
                1: contradiction.
                all: reflexivity.
        }
        rewrite eq; clear eq.
        case_if.
        1: reflexivity.
        unfold tensor_mult_base; cbn.
        unfold ex_proof at 2.
        unfold multi_type.
        remember (ex_to_type (tensor_zero_homogeneous U V)) as z_ex.
        rewrite <- Heqz_ex; clear Heqz_ex.
        destruct (z_ex) as [zk C0]; cbn.
        rewrite_ex_val_with C0 Z Z_eq.
        clear C0.
        rewrite <- (multilinear_to_tensor_zero U V zk) in Z_eq.
        apply multilinear_to_tensor_eq in Z_eq.
        subst Z.
        unfold multi_type in *.
        rewrite multilinear_mult_ranni.
        apply multilinear_to_tensor_zero.
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
            rewrite multilinear_to_tensor_zero in B'_eq.
            rewrite <- (multilinear_to_tensor_zero U V bk') in B'_eq.
            apply multilinear_to_tensor_eq in B'_eq.
            subst B'.
            unfold multi_type in *.
            rewrite multilinear_mult_ranni.
            apply multilinear_to_tensor_zero.
        }
        change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
        rewrite eq.
        rewrite multilinear_to_tensor_zero.
        change (set_type (tensor_finite U V)) with (tensor_algebra U V).
        remember (tensor_max_nz U V 0) as n.
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
    unfold multilinear_to_tensor_base in contr.
    destruct (strong_excluded_middle (bk = bk)) as [eq|neq].
    2: contradiction.
    unfold multilinear_type_k_eq, Logic.eq_rect_r, Logic.eq_rect in contr.
    destruct (Logic.eq_sym _).
    contradiction.
Qed.
Lemma tensor_rmult_homogeneous2 : ∀ al (b : set_type (homogeneous_tensor U V)),
        list_sum (list_prod2 tensor_mult_base al (tensor_decompose_grade U V [b|])) =
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

Lemma tensor_sum_decompose_lmult : ∀ a B ak k, tensor_grade U V [a|] ak →
        list_sum (list_image (tensor_decompose_grade U V B)
                             (λ x, [tensor_mult_base a x|] (ak + k)))
        = [tensor_mult_base a (list_nth (tensor_decompose_grade U V B) k
            [_|tensor_zero_homogeneous U V])|] (ak + k).
    intros a B ak k ak_grade.
    pose proof (tensor_decompose_nth U V B k) as eq.
    assert (homogeneous_tensor U V (multilinear_to_tensor U V ([B|] k))) as B_homo.
    {
        exists k, ([B|] k).
        reflexivity.
    }
    assert (list_nth (tensor_decompose_grade U V B) k [0|tensor_zero_homogeneous U V]
        = [_|B_homo]) as eq2.
    {
        apply set_type_eq; cbn.
        exact eq.
    }
    rewrite eq2.
    clear eq eq2.
    assert (list_image (tensor_decompose_grade U V B) (λ x, [tensor_mult_base a x|] (ak + k)) =
        func_to_list (λ n, If n = k then [tensor_mult_base a [_|B_homo]|] (ak + k) else 0)
        (tensor_max_nz U V B)) as eq.
    {
        unfold tensor_decompose_grade.
        rewrite func_to_list_image.
        apply f_equal2.
        2: reflexivity.
        apply functional_ext.
        intros x.
        case_if.
        -   subst x.
            assert ([_|tensor_project_homogeneous U V B k] = [_|B_homo]) as eq.
            {
                apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros x.
                unfold multilinear_to_tensor_base.
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
                unfold multi_type in *.
                pose proof (multilinear_mult_lanni U (multilinear_type U V 1))
                    as multilinear_mult_lanni.
                rewrite multilinear_mult_lanni.
                pose proof (multilinear_to_tensor_zero U V (ak' + x')) as eq.
                unfold multilinear_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                unfold multi_type in eq.
                unfold multilinear_type in *.
                unfold T1, T8 in *.
                rewrite eq.
                reflexivity.
            }
            classic_case (0 = B') as [B_z|B_nz].
            {
                subst.
                unfold multi_type in *.
                pose proof (multilinear_mult_ranni U (multilinear_type U V 1))
                    as multilinear_mult_ranni.
                rewrite multilinear_mult_ranni.
                pose proof (multilinear_to_tensor_zero U V (ak' + x')) as eq.
                unfold multilinear_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                unfold multi_type in eq.
                unfold multilinear_type in *.
                unfold T1, T8 in *.
                rewrite eq.
                reflexivity.
            }
            assert (ak = ak') as eq.
            {
                apply (tensor_grade_unique U V (multilinear_to_tensor U V A')).
                -   intros contr.
                    pose proof (multilinear_to_tensor_zero U V ak') as eq.
                    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in eq.
                    rewrite <- eq in contr.
                    apply multilinear_to_tensor_eq in contr.
                    contradiction.
                -   rewrite <- A_eq.
                    exact ak_grade.
                -   exists A'.
                    reflexivity.
            }
            assert (x = x') as eq2.
            {
                apply (tensor_grade_unique U V (multilinear_to_tensor U V B')).
                -   intros contr.
                    pose proof (multilinear_to_tensor_zero U V x') as eq2.
                    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in eq2.
                    rewrite <- eq2 in contr.
                    apply multilinear_to_tensor_eq in contr.
                    contradiction.
                -   rewrite <- B_eq.
                    apply tensor_project_grade.
                -   exists B'.
                    reflexivity.
            }
            subst ak' x'.
            unfold multilinear_to_tensor_base.
            destruct (strong_excluded_middle (ak + k = ak + x)) as [eq|neq].
            +   exfalso.
                apply plus_lcancel in eq.
                symmetry in eq; contradiction.
            +   reflexivity.
    }
    rewrite eq; clear eq.
    classic_case (0 = [B|] k) as [B_z|B_nz].
    {
        assert ([multilinear_to_tensor U V ([B|] k) | B_homo]
            = [_|tensor_zero_homogeneous U V]) as eq.
        {
            apply set_type_eq; cbn.
            rewrite <- B_z.
            apply multilinear_to_tensor_zero.
        }
        rewrite eq; clear eq.
        assert ([tensor_mult_base a [_|tensor_zero_homogeneous U V]|] (ak + k) = 0) as eq.
        {
            cbn.
            unfold ex_proof.
            destruct (ex_to_type _) as [ak' C0]; cbn.
            destruct (ex_to_type _) as [zk C1]; cbn.
            rewrite_ex_val A A_eq.
            rewrite_ex_val Z Z_eq.
            clear C0 C1.
            rewrite <- (multilinear_to_tensor_zero U V zk) in Z_eq.
            apply multilinear_to_tensor_eq in Z_eq.
            subst Z.
            unfold multi_type in *.
            rewrite multilinear_mult_ranni.
            pose proof (multilinear_to_tensor_zero U V (ak' + zk)) as eq.
            apply eq_set_type in eq; cbn in eq.
            unfold multi_type in eq.
            unfold multilinear_type in *.
            rewrite eq.
            reflexivity.
        }
        rewrite eq.
        remember (tensor_max_nz U V B) as m.
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
    apply (tensor_max_nz_leq U V _ _ B_nz).
Qed.
Lemma tensor_sum_decompose_rmult : ∀ a B ak k, tensor_grade U V [a|] ak →
        list_sum (list_image (tensor_decompose_grade U V B)
                             (λ x, [tensor_mult_base x a|] (k + ak)))
        = [tensor_mult_base (list_nth (tensor_decompose_grade U V B) k
            [_|tensor_zero_homogeneous U V]) a|] (k + ak).
    intros a B ak k ak_grade.
    pose proof (tensor_decompose_nth U V B k) as eq.
    assert (homogeneous_tensor U V (multilinear_to_tensor U V ([B|] k))) as B_homo.
    {
        exists k, ([B|] k).
        reflexivity.
    }
    assert (list_nth (tensor_decompose_grade U V B) k [0|tensor_zero_homogeneous U V]
        = [_|B_homo]) as eq2.
    {
        apply set_type_eq; cbn.
        exact eq.
    }
    rewrite eq2.
    clear eq eq2.
    assert (list_image (tensor_decompose_grade U V B) (λ x, [tensor_mult_base x a|] (k + ak)) =
        func_to_list (λ n, If n = k then [tensor_mult_base [_|B_homo] a|] (k + ak) else 0)
        (tensor_max_nz U V B)) as eq.
    {
        unfold tensor_decompose_grade.
        rewrite func_to_list_image.
        apply f_equal2.
        2: reflexivity.
        apply functional_ext.
        intros x.
        case_if.
        -   subst x.
            assert ([_|tensor_project_homogeneous U V B k] = [_|B_homo]) as eq.
            {
                apply set_type_eq; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros x.
                unfold multilinear_to_tensor_base.
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
                unfold multi_type in *.
                pose proof (multilinear_mult_ranni U (multilinear_type U V 1))
                    as multilinear_mult_ranni.
                rewrite multilinear_mult_ranni.
                pose proof (multilinear_to_tensor_zero U V (x' + ak')) as eq.
                unfold multilinear_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                unfold multi_type in eq.
                unfold multilinear_type in *.
                unfold T1, T8 in *.
                rewrite eq.
                reflexivity.
            }
            classic_case (0 = B') as [B_z|B_nz].
            {
                subst.
                unfold multi_type in *.
                pose proof (multilinear_mult_lanni U (multilinear_type U V 1))
                    as multilinear_mult_lanni.
                rewrite multilinear_mult_lanni.
                pose proof (multilinear_to_tensor_zero U V (x' + ak')) as eq.
                unfold multilinear_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                unfold multi_type in eq.
                unfold multilinear_type in *.
                unfold T1, T8 in *.
                rewrite eq.
                reflexivity.
            }
            assert (ak = ak') as eq.
            {
                apply (tensor_grade_unique U V (multilinear_to_tensor U V A')).
                -   intros contr.
                    pose proof (multilinear_to_tensor_zero U V ak') as eq.
                    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in eq.
                    rewrite <- eq in contr.
                    apply multilinear_to_tensor_eq in contr.
                    contradiction.
                -   rewrite <- A_eq.
                    exact ak_grade.
                -   exists A'.
                    reflexivity.
            }
            assert (x = x') as eq2.
            {
                apply (tensor_grade_unique U V (multilinear_to_tensor U V B')).
                -   intros contr.
                    pose proof (multilinear_to_tensor_zero U V x') as eq2.
                    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in eq2.
                    rewrite <- eq2 in contr.
                    apply multilinear_to_tensor_eq in contr.
                    contradiction.
                -   rewrite <- B_eq.
                    apply tensor_project_grade.
                -   exists B'.
                    reflexivity.
            }
            subst ak' x'.
            unfold multilinear_to_tensor_base.
            destruct (strong_excluded_middle (k + ak = x + ak)) as [eq|neq].
            +   exfalso.
                apply plus_rcancel in eq.
                symmetry in eq; contradiction.
            +   reflexivity.
    }
    rewrite eq; clear eq.
    classic_case (0 = [B|] k) as [B_z|B_nz].
    {
        assert ([multilinear_to_tensor U V ([B|] k) | B_homo]
            = [_|tensor_zero_homogeneous U V]) as eq.
        {
            apply set_type_eq; cbn.
            rewrite <- B_z.
            apply multilinear_to_tensor_zero.
        }
        rewrite eq; clear eq.
        assert ([tensor_mult_base [_|tensor_zero_homogeneous U V] a|] (k + ak) = 0) as eq.
        {
            cbn.
            unfold ex_proof.
            destruct (ex_to_type _) as [zk C1]; cbn.
            destruct (ex_to_type _) as [ak' C0]; cbn.
            rewrite_ex_val Z Z_eq.
            rewrite_ex_val A A_eq.
            clear C0 C1.
            rewrite <- (multilinear_to_tensor_zero U V zk) in Z_eq.
            apply multilinear_to_tensor_eq in Z_eq.
            subst Z.
            unfold multi_type in *.
            rewrite multilinear_mult_lanni.
            pose proof (multilinear_to_tensor_zero U V (zk + ak')) as eq.
            apply eq_set_type in eq; cbn in eq.
            unfold multi_type in eq.
            unfold multilinear_type in *.
            rewrite eq.
            reflexivity.
        }
        rewrite eq.
        remember (tensor_max_nz U V B) as m.
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
    apply (tensor_max_nz_leq U V _ _ B_nz).
Qed.

Lemma tensor_decompose_plus_nth : ∀ a b n, let z := [_|tensor_zero_homogeneous U V]
        in [list_nth (tensor_decompose_grade U V (a + b)) n z|] =
        [list_nth (tensor_decompose_grade U V a) n z|] +
        [list_nth (tensor_decompose_grade U V b) n z|].
    intros a b n z.
    unfold z.
    do 3 rewrite tensor_decompose_nth.
    pose proof (multilinear_to_tensor_plus U V) as stupid.
    rewrite stupid.
    reflexivity.
Qed.

Lemma tensor_mult_homogeneous : ∀ a b, homogeneous_tensor U V (tensor_mult_base a b).
    intros a b.
    unfold tensor_mult_base.
    unfold ex_proof.
    destruct (ex_to_type _) as [ak C0]; cbn.
    destruct (ex_to_type _) as [bk C1]; cbn.
    rewrite_ex_val A A_eq.
    rewrite_ex_val B B_eq.
    clear C0 C1.
    exists (ak + bk), (multilinear_mult _ _ A B).
    reflexivity.
Qed.

Lemma multilinear_to_tensor_tm :
        ∀ k1 k2 (A : multi_type k1) (B : multi_type k2) AH BH,
        tensor_mult_base [multilinear_to_tensor U V A|AH] [multilinear_to_tensor U V B|BH] =
        multilinear_to_tensor U V (multilinear_mult _ _ A B).
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
        rewrite multilinear_to_tensor_zero in A'_eq.
        rewrite <- (multilinear_to_tensor_zero U V ak) in A'_eq.
        apply multilinear_to_tensor_eq in A'_eq.
        subst A'.
        unfold multi_type in *.
        pose proof (multilinear_mult_lanni U (multilinear_type U V 1))
            as multilinear_mult_lanni.
        do 2 rewrite multilinear_mult_lanni.
        do 2 rewrite multilinear_to_tensor_zero.
        reflexivity.
    }
    classic_case (0 = B) as [B_z|B_nz].
    {
        subst B.
        rewrite multilinear_to_tensor_zero in B'_eq.
        rewrite <- (multilinear_to_tensor_zero U V bk) in B'_eq.
        apply multilinear_to_tensor_eq in B'_eq.
        subst B'.
        unfold multi_type in *.
        pose proof (multilinear_mult_ranni U (multilinear_type U V 1))
            as multilinear_mult_ranni.
        do 2 rewrite multilinear_mult_ranni.
        do 2 rewrite multilinear_to_tensor_zero.
        reflexivity.
    }
    pose proof (multilinear_to_tensor_eq_grade U V _ _ A A' A_nz A'_eq).
    pose proof (multilinear_to_tensor_eq_grade U V _ _ B B' B_nz B'_eq).
    subst ak bk.
    apply multilinear_to_tensor_eq in A'_eq, B'_eq.
    subst A' B'.
    reflexivity.
Qed.

End TensorAlgebra.
