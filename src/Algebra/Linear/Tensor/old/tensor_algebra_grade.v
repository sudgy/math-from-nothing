Require Import init.

Require Export tensor_algebra_base.
Require Import linear_multilinear.
Require Import nat.
Require Import card.
Require Import set.
Require Import list.
Require Import plus_sum.

(** This file contains various definitions and theorems about the graded
structure of the tensor algebra.
*)

(* begin hide *)
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

Local Open Scope card_scope.
(* end hide *)
Let multi_type k := multilinear_type U (multilinear_type U V 1) k.

Lemma tensor_grade_project_finite : ∀ (A : tensor_algebra U V) k,
        tensor_finite U V (λ n, If n = k then [A|] n else 0).
    intros [A A_fin] k; cbn.
    apply (le_lt_trans2 (nat_is_finite 1)).
    unfold nat_to_card, le; equiv_simpl.
    exists (λ x, [0|nat_0_lt_1]).
    intros [a a_eq] [b b_eq] eq; clear eq.
    apply set_type_eq; cbn.
    do 2 case_if.
    -   subst.
        reflexivity.
    -   contradiction.
    -   contradiction.
    -   contradiction.
Qed.

Definition tensor_grade_project (A : tensor_algebra U V ) k :=
    [_|tensor_grade_project_finite A k].

Definition homogeneous_tensor A := ∃ k (M : multi_type k),
    A = multilinear_to_tensor U V M.
Definition tensor_grade (A : tensor_algebra U V ) k := ∃ (M : multi_type k),
    A = multilinear_to_tensor U V M.

Theorem tensor_zero_homogeneous : homogeneous_tensor 0.
    exists 0, 0.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros x.
    unfold multilinear_to_tensor_base.
    destruct (strong_excluded_middle (x = 0)) as [x_eq|x_neq].
    -   subst.
        cbn.
        reflexivity.
    -   reflexivity.
Qed.

Theorem tensor_project_homogeneous :
        ∀ A k, homogeneous_tensor (tensor_grade_project A k).
    intros A k.
    exists k, ([A|] k).
    apply set_type_eq; cbn.
    unfold multilinear_to_tensor_base; cbn.
    apply functional_ext.
    intros x.
    classic_case (x = k) as [eq|neq].
    -   unfold multilinear_type_k_eq; cbn.
        subst; cbn.
        reflexivity.
    -   reflexivity.
Qed.

Theorem tensor_project_grade : ∀ A k, tensor_grade (tensor_grade_project A k) k.
    intros A k.
    exists ([A|] k).
    apply set_type_eq.
    apply functional_ext.
    intros x.
    cbn.
    unfold multilinear_to_tensor_base.
    case_if.
    -   subst.
        cbn.
        reflexivity.
    -   reflexivity.
Qed.

Lemma tensor_max_nz_ex : ∀ A : tensor_algebra U V,
        ∃ n, (∀ m, 0 ≠ [A|] m → m < n) ∧ (∀ m, n <= m → 0 = [A|] m) ∧
        (∀ m, nat_suc m = n → 0 ≠ [A|] m).
    intros A.
    classic_case (∃ k, 0 ≠ [A|] k) as [A_nz|A_z].
    2: {
        exists 0.
        rewrite not_ex in A_z.
        setoid_rewrite not_not in A_z.
        split.
        2: split.
        -   intros m m_neq.
            specialize (A_z m).
            contradiction.
        -   intros m m_pos.
            apply A_z.
        -   intros m m_eq.
            inversion m_eq.
    }
    pose proof (finite_well_ordered_set_max _ [|A] A_nz)
        as [n [n_nz n_greatest]].
    exists (nat_suc n).
    split.
    2: split.
    -   intros m.
        rewrite nat_lt_suc_le.
        apply n_greatest.
    -   intros m m_leq.
        classic_contradiction contr.
        specialize (n_greatest _ contr).
        pose proof (trans m_leq n_greatest) as leq.
        rewrite <- nlt_le in leq.
        apply leq.
        apply nat_lt_suc.
    -   intros m m_eq.
        inversion m_eq.
        exact n_nz.
Qed.
Definition tensor_max_nz A := ex_val (tensor_max_nz_ex A).
Theorem tensor_max_nz_leq : ∀ A m, 0 ≠ [A|] m → m < tensor_max_nz A.
    intros A m neq.
    unfold tensor_max_nz.
    rewrite_ex_val n n_leq.
    apply n_leq.
    exact neq.
Qed.
Theorem tensor_max_nz_geq : ∀ A m, tensor_max_nz A <= m → 0 = [A|] m.
    intros A m leq.
    unfold tensor_max_nz in leq.
    rewrite_ex_val n n_leq.
    apply n_leq.
    exact leq.
Qed.
Theorem tensor_max_nz_least : ∀ A m, nat_suc m = tensor_max_nz A → 0 ≠ [A|] m.
    intros A m leq.
    unfold tensor_max_nz in leq.
    rewrite_ex_val n n_leq.
    apply n_leq.
    exact leq.
Qed.

Definition tensor_decompose_grade A :=
    (func_to_list (λ k, [_|tensor_project_homogeneous A k]) (tensor_max_nz A)).


Theorem tensor_decompose_grade_eq : ∀ A,
        A = list_sum (list_image (tensor_decompose_grade A) (λ x, [x|])).
    intros a.
    destruct a as [af af_fin].
    apply set_type_eq; cbn.
    apply functional_ext.
    intros x.
    unfold plus; cbn.
    unfold tensor_decompose_grade.
    remember (tensor_max_nz [af|af_fin]) as n.
    pose proof (tensor_max_nz_leq [af|af_fin]) as n_greatest.
    cbn in n_greatest.
    rewrite <- Heqn in n_greatest.
    clear Heqn.
    assert ([list_sum
       (list_image (A := set_type homogeneous_tensor)
          (func_to_list
             (λ k : nat,
                [tensor_grade_project [af | af_fin] k
                | tensor_project_homogeneous [af | af_fin] k]) n)
          (λ x0 : set_type homogeneous_tensor, [x0 | ])) | ] x =
          list_sum
              (func_to_list (λ k, [tensor_grade_project [af | af_fin] k|] x) n))
        as eq.
    {
        clear n_greatest.
        nat_induction n.
        -   unfold zero; cbn.
            reflexivity.
        -   cbn in *.
            rewrite list_sum_plus.
            rewrite list_image_conc.
            rewrite list_sum_plus.
            unfold func_to_list in IHn.
            rewrite <- IHn.
            unfold plus at 1; cbn.
            reflexivity.
    }
    change (set_type (tensor_finite U V)) with (tensor_algebra U V) in *.
    rewrite eq; clear eq.
    cbn.
    revert af af_fin n_greatest.
    nat_induction n.
    -   intros.
        unfold zero at 2; cbn.
        symmetry; classic_contradiction neq.
        apply n_greatest in neq.
        contradiction (nat_lt_zero _ neq).
    -   intros.
        cbn.
        pose (af' := [af|af_fin]-tensor_grade_project [af|af_fin] n).
        assert (∀ y, 0 ≠ [af'|] y → y < n) as af'_n_greatest.
        {
            clear IHn.
            intros y neq.
            setoid_rewrite nat_lt_suc_le in n_greatest.
            split.
            -   apply n_greatest.
                unfold af' in neq.
                unfold tensor_grade_project, plus, neg in neq; cbn in neq.
                case_if.
                +   rewrite plus_rinv in neq.
                    contradiction.
                +   rewrite neg_zero, plus_rid in neq.
                    exact neq.
            -   intros contr; subst y.
                apply neq; clear neq.
                unfold af'.
                unfold tensor_grade_project; cbn.
                unfold zero; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros y.
                unfold plus, neg; cbn.
                case_if.
                +   rewrite plus_rinv.
                    reflexivity.
                +   contradiction.
        }
        specialize (IHn [af'|] [|af'] af'_n_greatest).
        assert (af x = [af'|] x
                + [tensor_grade_project [af|af_fin] n|] x)
            as eq.
        {
            unfold af'.
            unfold plus at 2; cbn.
            unfold neg; cbn.
            rewrite plus_rlinv.
            reflexivity.
        }
        rewrite eq; clear eq.
        rewrite plus_comm.
        rewrite IHn at 1; clear IHn.
        cbn.
        unfold func_to_list.
        rewrite list_sum_plus.
        rewrite plus_comm.
        apply f_equal2.
        +   unfold af', tensor_grade_project; cbn.
            unfold plus at 1 3, neg; cbn.
            apply f_equal.
            apply func_to_list_eq.
            intros m m_lt.
            case_if.
            2: reflexivity.
            case_if.
            *   exfalso; clear - m_lt e e0.
                subst.
                rewrite <- nle_lt in m_lt.
                apply m_lt.
                apply refl.
            *   rewrite neg_zero, plus_rid, plus_lid.
                reflexivity.
        +   unfold af'.
            unfold plus at 2, neg; cbn.
            case_if.
            *   rewrite plus_rinv, plus_rid.
                rewrite plus_rid.
                reflexivity.
            *   rewrite plus_rid.
                reflexivity.
Qed.

Lemma tensor_decompose_nth : ∀ A k,
        [list_nth (tensor_decompose_grade A) k [_|tensor_zero_homogeneous]|]
        = multilinear_to_tensor U V ([A|] k).
    intros A k.
    unfold tensor_decompose_grade.
    classic_case (k < tensor_max_nz A) as [k_lt|k_ge].
    -   rewrite func_to_list_nth_lt by exact k_lt.
        unfold tensor_grade_project.
        apply set_type_eq; cbn.
        apply functional_ext.
        unfold multilinear_to_tensor_base.
        intros x.
        case_if.
        +   subst.
            cbn.
            reflexivity.
        +   reflexivity.
    -   rewrite nlt_le in k_ge.
        rewrite func_to_list_nth_ge by exact k_ge.
        apply tensor_max_nz_geq in k_ge.
        apply set_type_eq; cbn.
        apply functional_ext.
        intros x.
        unfold multilinear_to_tensor_base.
        destruct (strong_excluded_middle (x = k)) as [eq|neq].
        +   subst.
            cbn.
            rewrite <- k_ge.
            reflexivity.
        +   reflexivity.
Qed.

Lemma tensor_decompose_nth_grade : ∀ A k,
        tensor_grade [list_nth (tensor_decompose_grade A) k
            [_|tensor_zero_homogeneous]|] k.
    intros A k.
    exists ([A|] k).
    rewrite tensor_decompose_nth.
    reflexivity.
Qed.

Theorem tensor_decompose_zero : tensor_decompose_grade 0 = list_end.
    unfold tensor_decompose_grade.
    replace (tensor_max_nz 0) with (zero (U := nat)).
    unfold zero at 3; cbn.
    reflexivity.
    unfold tensor_max_nz.
    rewrite_ex_val n [n_lt [n_ge n_least]].
    nat_destruct n; try reflexivity.
    specialize (n_least n (refl _)).
    contradiction.
Qed.

Lemma multilinear_to_tensor_eq_grade : ∀ k1 k2
        (A : multi_type k1) (B : multi_type k2),
        0 ≠ A → multilinear_to_tensor U V A = multilinear_to_tensor U V B → k1 = k2.
    intros k1 k2 A B A_nz eq.
    apply eq_set_type in eq; cbn in eq.
    assert (multilinear_to_tensor_base U V A k1 = multilinear_to_tensor_base U V B k1)
        as eq2.
    {
        rewrite eq.
        reflexivity.
    }
    clear eq; rename eq2 into eq.
    unfold multilinear_to_tensor_base in eq.
    destruct (strong_excluded_middle (k1 = k1)) as [k1_eq|k1_neq].
    2: contradiction.
    destruct (strong_excluded_middle (k1 = k2)) as [k_eq|k_neq].
    1: exact k_eq.
    unfold multilinear_type_k_eq, Logic.eq_rect_r, Logic.eq_rect in eq.
    destruct (Logic.eq_sym _).
    symmetry in eq; contradiction.
Qed.

Lemma tensor_grade_unique : ∀ A k1 k2,
        0 ≠ A → tensor_grade A k1 → tensor_grade A k2 → k1 = k2.
    intros A k1 k2 A_nz k1_grade k2_grade.
    destruct k1_grade as [A1 A1_eq].
    destruct k2_grade as [A2 A2_eq].
    assert (0 ≠ A1) as A1_neq.
    {
        intros contr.
        subst.
        rewrite multilinear_to_tensor_zero in A_nz.
        contradiction.
    }
    apply (multilinear_to_tensor_eq_grade _ _ A1 A2 A1_neq).
    rewrite <- A1_eq, <- A2_eq.
    reflexivity.
Qed.

Lemma multilinear_to_tensor_grade : ∀ k (A : multi_type k),
        tensor_grade (multilinear_to_tensor U V A) k.
    intros k A.
    exists A.
    reflexivity.
Qed.

Lemma tensor_grade_zero_eq : ∀ A k, tensor_grade A k → ∀ n, n ≠ k → 0 = [A|] n.
    intros A k A_grade n n_neq.
    destruct A_grade as [A' A_eq]; subst A.
    cbn.
    unfold multilinear_to_tensor_base.
    destruct (strong_excluded_middle (n = k)) as [eq|neq].
    -   contradiction.
    -   reflexivity.
Qed.

Lemma tensor_decompose_plus_nth : ∀ a b n, let z := [_|tensor_zero_homogeneous]
        in [list_nth (tensor_decompose_grade (a + b)) n z|] =
        [list_nth (tensor_decompose_grade a) n z|] +
        [list_nth (tensor_decompose_grade b) n z|].
    intros a b n z.
    unfold z.
    do 3 rewrite tensor_decompose_nth.
    pose proof (multilinear_to_tensor_plus U V) as stupid.
    rewrite stupid.
    reflexivity.
Qed.
(* begin hide *)
End TensorAlgebra.
(* end hide *)
