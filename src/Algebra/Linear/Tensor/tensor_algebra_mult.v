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

Existing Instance multilinear_plus.
Existing Instance multilinear_plus_comm.
Existing Instance multilinear_plus_assoc.
Existing Instance multilinear_zero.
Existing Instance multilinear_plus_lid.
Existing Instance multilinear_neg.
Existing Instance multilinear_plus_linv.
Existing Instance multilinear_scalar_mult.
Existing Instance multilinear_scalar_comp.
Existing Instance multilinear_scalar_id.
Existing Instance multilinear_scalar_ldist.
Existing Instance multilinear_scalar_rdist.
Existing Instance tensor_plus.
Existing Instance tensor_plus_comm.
Existing Instance tensor_plus_assoc.
Existing Instance tensor_zero.
Existing Instance tensor_plus_lid.
Existing Instance tensor_neg.
Existing Instance tensor_plus_linv.
Existing Instance tensor_scalar_mult.
Existing Instance tensor_scalar_comp.
Existing Instance tensor_scalar_id.
Existing Instance tensor_scalar_ldist.
Existing Instance tensor_scalar_rdist.

Let multi_type k := multilinear_type U (multilinear_type U V 1) k.

Local Open Scope card_scope.

Let tm (A' B' : set_type (homogeneous_tensor U V))
    := multilinear_to_tensor U V (multilinear_mult _ _
        (ex_val (ex_proof [|A']))
        (ex_val (ex_proof [|B']))).

Instance tensor_mult : Mult (tensor_algebra U V) := {
    mult A B := list_sum (list_prod2 tm
        (tensor_decompose_grade U V A) (tensor_decompose_grade U V B))
}.

Lemma tensor_mult_tm_grade : ∀ A B k1 k2,
        tensor_grade U V [A|] k1 → tensor_grade U V [B|] k2 →
        tensor_grade U V (tm A B) (k1 + k2).
    intros A B k1 k2 k1_grade k2_grade.
    unfold tm; clear tm.
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
        rewrite multilinear_mult_lanni.
        do 2 rewrite multilinear_to_tensor_zero.
        reflexivity.
    }
    classic_case (0 = B) as [B_z|B_nz].
    1: {
        subst.
        exists 0.
        unfold multi_type in *.
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
        list_sum (list_image (tensor_decompose_grade U V [a|]) (λ x, tm x b)) =
        tm a b.
    intros a b.
    destruct a as [a a_homo].
    destruct b as [b b_homo].
    cbn.
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    subst a b.
    assert (list_image (tensor_decompose_grade U V (multilinear_to_tensor U V A))
        (λ x, tm x [_|b_homo]) = func_to_list (λ n, If n = ak
            then tm [_|a_homo] [_|b_homo] else 0)
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
        unfold tm; cbn.
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
        assert (tm [_|a_homo] [_|b_homo] = 0) as eq.
        {
            unfold tm; cbn.
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
        list_sum (list_prod2 tm (tensor_decompose_grade U V [a|]) bl) =
        list_sum (list_prod2 tm (a :: list_end) bl).
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
        list_sum (list_image (tensor_decompose_grade U V [b|]) (λ x, tm a x)) =
        tm a b.
    intros a b.
    destruct a as [a a_homo].
    destruct b as [b b_homo].
    cbn.
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    subst a b.
    assert (list_image (tensor_decompose_grade U V (multilinear_to_tensor U V B))
        (λ x, tm [_|a_homo] x) = func_to_list (λ n, If n = bk
            then tm [_|a_homo] [_|b_homo] else 0)
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
        unfold tm; cbn.
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
        assert (tm [_|a_homo] [_|b_homo] = 0) as eq.
        {
            unfold tm; cbn.
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
        list_sum (list_prod2 tm al (tensor_decompose_grade U V [b|])) =
        list_sum (list_prod2 tm al (b :: list_end)).
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
                             (λ x, [tm a x|] (ak + k)))
        = [tm a (list_nth (tensor_decompose_grade U V B) k
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
    assert (list_image (tensor_decompose_grade U V B) (λ x, [tm a x|] (ak + k)) =
        func_to_list (λ n, If n = k then [tm a [_|B_homo]|] (ak + k) else 0)
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
                rewrite multilinear_mult_lanni.
                pose proof (multilinear_to_tensor_zero U V (ak' + x')) as eq.
                unfold multilinear_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                unfold multi_type in eq.
                unfold multilinear_type in *.
                rewrite eq.
                reflexivity.
            }
            classic_case (0 = B') as [B_z|B_nz].
            {
                subst.
                unfold multi_type in *.
                rewrite multilinear_mult_ranni.
                pose proof (multilinear_to_tensor_zero U V (ak' + x')) as eq.
                unfold multilinear_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                unfold multi_type in eq.
                unfold multilinear_type in *.
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
        assert ([tm a [_|tensor_zero_homogeneous U V]|] (ak + k) = 0) as eq.
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
        clear.
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
                             (λ x, [tm x a|] (k + ak)))
        = [tm (list_nth (tensor_decompose_grade U V B) k
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
    assert (list_image (tensor_decompose_grade U V B) (λ x, [tm x a|] (k + ak)) =
        func_to_list (λ n, If n = k then [tm [_|B_homo] a|] (k + ak) else 0)
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
                rewrite multilinear_mult_ranni.
                pose proof (multilinear_to_tensor_zero U V (x' + ak')) as eq.
                unfold multilinear_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                unfold multi_type in eq.
                unfold multilinear_type in *.
                rewrite eq.
                reflexivity.
            }
            classic_case (0 = B') as [B_z|B_nz].
            {
                subst.
                unfold multi_type in *.
                rewrite multilinear_mult_lanni.
                pose proof (multilinear_to_tensor_zero U V (x' + ak')) as eq.
                unfold multilinear_to_tensor in eq.
                apply eq_set_type in eq; cbn in eq.
                unfold multi_type in eq.
                unfold multilinear_type in *.
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
        assert ([tm [_|tensor_zero_homogeneous U V] a|] (k + ak) = 0) as eq.
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
        clear.
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
    -   assert ((λ x, [tm a x|] k) = (λ x, 0)) as eq.
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
            pose proof (tensor_mult_tm_grade _ _ _ _ ak_grade xk_grade)
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
        do 3 rewrite tensor_sum_decompose_lmult by exact ak_grade.
        remember (list_nth (tensor_decompose_grade U V (b + c)) _ _) as bc'.
        remember (list_nth (tensor_decompose_grade U V b) _ _) as b'.
        remember (list_nth (tensor_decompose_grade U V c) _ _) as c'.
        assert (tm a bc' = tm a b' + tm a c') as eq.
        {
            unfold tm.
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
                pose proof (multilinear_mult_ranni _ _ bck _ A) as stupid.
                unfold multi_type, multilinear_type in stupid.
                rewrite stupid; clear stupid.
                pose proof (multilinear_mult_ranni _ _ k _ A) as stupid.
                unfold multi_type, multilinear_type in stupid.
                rewrite stupid; clear stupid.
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
    -   assert ((λ x, [tm x a|] k) = (λ x, 0)) as eq.
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
            pose proof (tensor_mult_tm_grade _ _ _ _ xk_grade ak_grade)
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
        do 3 rewrite tensor_sum_decompose_rmult by exact ak_grade.
        remember (list_nth (tensor_decompose_grade U V (b + c)) _ _) as bc'.
        remember (list_nth (tensor_decompose_grade U V b) _ _) as b'.
        remember (list_nth (tensor_decompose_grade U V c) _ _) as c'.
        assert (tm bc' a = tm b' a + tm c' a) as eq.
        {
            unfold tm.
            unfold ex_val in ak.
            unfold ex_proof.
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
                pose proof (multilinear_mult_lanni _ _ bck _ A) as stupid.
                unfold multi_type, multilinear_type in stupid.
                rewrite stupid; clear stupid.
                pose proof (multilinear_mult_lanni _ _ k _ A) as stupid.
                unfold multi_type, multilinear_type in stupid.
                rewrite stupid; clear stupid.
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

Lemma tensor_mult_homogeneous : ∀ a b, homogeneous_tensor U V (tm a b).
    intros a b.
    unfold tm.
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
        tm [multilinear_to_tensor U V A|AH] [multilinear_to_tensor U V B|BH] =
        multilinear_to_tensor U V (multilinear_mult _ _ A B).
    intros k1 k2 A B AH BH.
    unfold tm; cbn.
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
    do 3 rewrite tensor_rmult_homogeneous2.
    do 3 rewrite list_prod2_lconc.
    do 3 rewrite list_prod2_lend.
    cbn.
    do 3 rewrite plus_lid.
    do 2 rewrite plus_rid.
    assert (list_sum (list_image
        (tensor_decompose_grade U V (tm b c)) (λ x, tm a x)) =
        list_sum (list_prod2 tm (a :: list_end)
        (tensor_decompose_grade U V (tm b c)))) as eq.
    {
        rewrite list_prod2_lconc.
        rewrite list_prod2_lend.
        cbn; rewrite plus_lid.
        reflexivity.
    }
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    rewrite eq; clear eq.
    pose proof (tensor_mult_homogeneous a b) as ab_homo.
    pose proof (tensor_lmult_homogeneous2 [_|ab_homo] (c :: list_end)) as eq.
    cbn in eq.
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    rewrite eq; clear eq.
    pose proof (tensor_mult_homogeneous b c) as bc_homo.
    pose proof (tensor_rmult_homogeneous2 (a :: list_end) [_|bc_homo]) as eq.
    cbn in eq.
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    rewrite eq; clear eq.
Local Arguments list_prod2: simpl nomatch.
    cbn.
    do 2 rewrite plus_rid.
    clear A B C al.
    destruct a as [a a_homo].
    destruct b as [b b_homo].
    destruct c as [c c_homo].
    pose proof a_homo as [ak [A A_eq]].
    pose proof b_homo as [bk [B B_eq]].
    pose proof c_homo as [ck [C C_eq]].
    subst a b c.
    pose proof (multilinear_to_tensor_tm _ _ B C b_homo c_homo) as eq.
    assert (homogeneous_tensor U V (multilinear_to_tensor U V (multilinear_mult _ _ B C)))
        as bc_homo2.
    {
        exists (bk + ck), (multilinear_mult _ _ B C).
        reflexivity.
    }
    assert ([tm [_|b_homo] [_|c_homo] | bc_homo] = [_|bc_homo2]) as eq2.
    {
        apply set_type_eq; exact eq.
    }
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    rewrite eq2.
    rewrite multilinear_to_tensor_tm.
    clear eq eq2 bc_homo bc_homo2.
    pose proof (multilinear_to_tensor_tm _ _ A B a_homo b_homo) as eq.
    assert (homogeneous_tensor U V (multilinear_to_tensor U V (multilinear_mult _ _ A B)))
        as ab_homo2.
    {
        exists (ak + bk), (multilinear_mult _ _ A B).
        reflexivity.
    }
    assert ([tm [_|a_homo] [_|b_homo] | ab_homo] = [_|ab_homo2]) as eq2.
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
