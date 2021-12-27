Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_power.
Require Import module_category.
Require Import linear_subspace.
Require Import linear_grade.

Require Import nat.
Require Import card.
Require Import set.
Require Import unordered_list.
Require Import plus_sum.

(** This file contains the definition of the graded structure of the tensor
algebra.
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
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD TP TZ TN TPC
    TPA TPZ TPN TSM TSMC TSMO TSML TSMR TAP TAZ TAN TAPC TAPA TAPZ TAPN TASM
    TASMC TASMO TASML TASMR.

Let k_tensor k := module_V (tensor_power V k).

Definition tensor_subspace_set n (v : tensor_algebra_base V)
    := ∃ v' : k_tensor n, power_to_tensor V v' = v.

Lemma tensor_subspace_zero : ∀ n, tensor_subspace_set n 0.
    intros n.
    exists 0.
    apply power_to_tensor_zero.
Qed.

Lemma tensor_subspace_plus : ∀ n u v,
        tensor_subspace_set n u → tensor_subspace_set n v →
        tensor_subspace_set n (u + v).
    intros n u' v' [u u_eq] [v v_eq]; subst u' v'.
    exists (u + v).
    symmetry; apply power_to_tensor_plus.
Qed.

Lemma tensor_subspace_scalar : ∀ n a v,
        tensor_subspace_set n v → tensor_subspace_set n (a · v).
    intros n a v' [v v_eq]; subst v'.
    exists (a · v).
    apply power_to_tensor_scalar.
Qed.

Definition tensor_subspace n := make_subspace
    (tensor_subspace_set n)
    (tensor_subspace_zero n)
    (tensor_subspace_plus n)
    (tensor_subspace_scalar n).

Program Instance tensor_grade : GradedSpace U (tensor_algebra_base V) := {
    grade_I := nat;
    grade_subspace n := tensor_subspace n;
}.
Next Obligation.
    rename H into neq.
    destruct H0 as [v1 v1_eq].
    destruct H1 as [v2 v2_eq].
    rewrite <- v2_eq in v1_eq.
    unfold power_to_tensor in v1_eq; cbn in v1_eq.
    apply eq_set_type in v1_eq; cbn in v1_eq.
    unfold power_to_tensor_base in v1_eq.
    (* I don't know why Coq is being so finicky about this *)
    assert (∀ n,
           match strong_excluded_middle (i = n) with
           | strong_or_left H => module_homo_f (tensor_power_nat_eq V H) v1
           | strong_or_right _ => 0
           end =
           match strong_excluded_middle (j = n) with
           | strong_or_left H => module_homo_f (tensor_power_nat_eq V H) v2
           | strong_or_right _ => 0
           end) as v1_eq'.
    {
        intros m.
        change
            (match strong_excluded_middle (i = m) with
            | strong_or_left H => module_homo_f (tensor_power_nat_eq V H) v1
            | strong_or_right _ => 0
            end)
            with
            ((λ n, match strong_excluded_middle (i = n) with
            | strong_or_left H => module_homo_f (tensor_power_nat_eq V H) v1
            | strong_or_right _ => (@zero _ (module_zero (tensor_power V n)))
            end) m).
        rewrite v1_eq.
        reflexivity.
    }
    clear v1_eq.
    specialize (v1_eq' j).
    destruct (strong_excluded_middle (i = j)) as [ij_eq|ij_neq];
    destruct (strong_excluded_middle (j = j)) as [jj_eq|jj_neq];
    try contradiction.
    destruct jj_eq; cbn in v1_eq'.
    subst v2.
    rewrite (power_to_tensor_zero V) in v2_eq.
    exact v2_eq.
Qed.
Next Obligation.
    pose proof (fin_nat_ex _ [|v]) as [n n_eq].
    unfold nat_to_card in n_eq; equiv_simpl in n_eq.
    destruct n_eq as [g [g_inj g_sur]].
    pose (g' m := match (strong_excluded_middle (m < n)) with
        | strong_or_left ltq => [g [m|ltq]|]
        | strong_or_right _ => n
        end).
    pose (l := func_to_ulist g' n).
    assert (∀ n, tensor_subspace_set n (power_to_tensor V ([v|] n))) as v_in.
    {
        intros m.
        exists ([v|] m).
        reflexivity.
    }
    pose (l' := ulist_image l (λ n, make_subspace_vector
        (tensor_subspace n) _ (v_in n))).
    exists l'.
    split.
    -   unfold l'.
        rewrite ulist_image_comp; cbn.
        apply set_type_eq; cbn.
        apply functional_ext; intros m.
        unfold l.
        rewrite func_to_ulist_image.
        assert ([ulist_sum (func_to_ulist (λ m0, power_to_tensor V ([v|] (g' m0))) n)|] m =
            ulist_sum (func_to_ulist (λ m0, power_to_tensor_base V ([v|] (g' m0)) m) n)) as eq.
        {
            do 2 rewrite ulist_sum_sum_eq.
            remember n as n'.
            rewrite Heqn'.
            assert (n <= n') as n_leq by (rewrite Heqn'; apply refl).
            clear Heqn'.
            nat_induction n.
            -   unfold zero; cbn.
                reflexivity.
            -   cbn.
                unfold plus at 1; cbn.
                apply rplus.
                rewrite IHn by exact (trans (nat_le_suc n) n_leq).
                reflexivity.
        }
        unfold tensor_algebra_base.
        rewrite eq; clear eq l l'.
        pose (h m0 :=
         @power_to_tensor_base F V (g' m0)
           (@set_value (@tensor_algebra_base_base F V)
              (@tensor_finite F V) v (g' m0)) m).
        fold h.
        classic_case ([v|] m = 0) as [fv_z|fv_nz].
        *   rewrite fv_z.
            assert (h = (λ _, 0)) as h_eq.
            {
                apply functional_ext.
                intros a.
                unfold h.
                unfold power_to_tensor_base.
                destruct (strong_excluded_middle (g' a = m)).
                -   destruct e; cbn.
                    exact fv_z.
                -   reflexivity.
            }
            rewrite h_eq.
            clear v g g_inj g_sur g' v v_in h fv_z h_eq.
            nat_induction n.
            --  rewrite func_to_ulist_zero.
                rewrite ulist_sum_end.
                reflexivity.
            --  rewrite func_to_ulist_suc.
                rewrite ulist_sum_add.
                rewrite plus_lid.
                exact IHn.
        *   rewrite neq_sym in fv_nz.
            pose proof (g_sur [m|fv_nz]) as [vn vn_eq].
            pose (h' m := If m < n then h m else 0).
            assert (∀ m, m < n → h m = h' m) as h'_eq.
            {
                intros m' ltq.
                unfold h', h.
                case_if.
                -   reflexivity.
                -   contradiction.
            }
            rewrite (func_to_ulist_eq _ _ _ h'_eq); clear h'_eq.
            assert (h' = (λ m0, If m0 = [vn|] then ([v|] m) else 0)) as h_eq.
            {
                apply functional_ext.
                intros m'.
                unfold h'; clear h'.
                unfold h; clear h.
                unfold power_to_tensor_base.
                unfold g'.
                destruct (strong_excluded_middle (m' < n)).
                case_if; subst.
                1: destruct (strong_excluded_middle ([g [[vn|]|l]|] = m));
                    subst; cbn.
                3: destruct (strong_excluded_middle ([g [m'|l]|] = m));
                    subst; cbn.
                5: case_if; subst.
                1, 4, 6: reflexivity.
                -   apply eq_set_type in vn_eq; cbn in vn_eq.
                    subst m.
                    exfalso; apply n0.
                    apply eq_set_type; cbn.
                    apply f_equal.
                    apply set_type_eq; reflexivity.
                -   apply eq_set_type in vn_eq; cbn in vn_eq.
                    apply set_type_eq in vn_eq; cbn in vn_eq.
                    apply g_inj in vn_eq.
                    apply eq_set_type in vn_eq; cbn in vn_eq.
                    symmetry in vn_eq; contradiction.
                -   destruct vn; contradiction.
            }
            rewrite h_eq.
            rewrite (ulist_sum_func_single ([v|] m) _ _ [|vn]).
            reflexivity.
    -   unfold l'.
        remember l as l''.
        clear Heql'' l' l l g' n g g_inj g_sur.
        rename l'' into l.
        induction l using ulist_induction.
        +   rewrite ulist_image_end.
            apply ulist_prop_end.
        +   rewrite ulist_image_add.
            apply ulist_prop_add.
            split.
            *   exists a.
                cbn.
                reflexivity.
            *   exact IHl.
Qed.
Next Obligation.
    rename H into l_in.
    rename H0 into l_uni.
    rename H1 into l_zero.
    destruct l as [|v l] using ulist_induction.
    1: apply ulist_prop_end.
    assert (0 = sub_vector_v v) as v_z.
    {
        clear IHl.
        classic_contradiction v_nz.
        apply ulist_prop_add in l_in as [[i i_eq] l_in].
        pose proof (sub_vector_in v) as v_in.
        rewrite <- i_eq in v_in.
        destruct v_in as [v' v_eq].
        rewrite ulist_image_add, ulist_unique_add in l_uni.
        rewrite <- i_eq in l_uni.
        rewrite ulist_image_add in l_zero.
        rewrite <- v_eq in l_zero, v_nz.
        clear v v_eq i_eq.
        rename v' into v.
        destruct l_uni as [v_nin l_uni].
        clear l_uni.
        rewrite ulist_sum_add in l_zero.
        unfold zero, plus in l_zero; cbn in l_zero.
        apply eq_set_type in l_zero; cbn in l_zero.
        assert (∀ k, 0 = power_to_tensor_base V v k +
            [ulist_sum (ulist_image l sub_vector_v)|] k) as eq2.
        {
            intros k.
            change (@zero _ (TZ k)) with
                ((λ k : nat, (@zero _ (module_zero (tensor_power V k)))) k).
            rewrite l_zero.
            reflexivity.
        }
        clear l_zero.
        specialize (eq2 i).
        unfold power_to_tensor_base in eq2.
        destruct (strong_excluded_middle (i = i)) as [eq|];
            [>destruct eq; cbn in eq2|contradiction].
        induction l as [|a l] using ulist_induction.
        1: {
            rewrite ulist_image_end, ulist_sum_end in eq2.
            change ([0|] i) with (@zero _ (module_zero (tensor_power V i)))
                in eq2.
            rewrite plus_rid in eq2.
            subst v.
            rewrite (power_to_tensor_zero V) in v_nz.
            contradiction.
        }
        apply ulist_prop_add in l_in as [[j aj] l_in].
        apply IHl; clear IHl.
        -   exact l_in.
        -   rewrite ulist_image_add, in_ulist_add in v_nin.
            rewrite not_or in v_nin.
            apply v_nin.
        -   rewrite ulist_image_add, ulist_sum_add in eq2.
            unfold plus at 2 in eq2; cbn in eq2.
            rewrite plus_assoc in eq2.
            rewrite (plus_comm v) in eq2.
            rewrite <- plus_assoc in eq2.
            rewrite plus_0_ab_na_b in eq2.
            rewrite <- eq2; clear eq2.
            rewrite <- neg_zero.
            apply f_equal.
            assert (tensor_subspace_set j (sub_vector_v a)) as a_in.
            {
                rewrite aj.
                apply sub_vector_in.
            }
            destruct a_in as [a' a_eq].
            rewrite ulist_image_add in v_nin.
            rewrite <- aj in v_nin.
            rewrite <- a_eq.
            clear a_eq a aj.
            rename a' into a.
            unfold power_to_tensor; cbn.
            unfold power_to_tensor_base.
            destruct (strong_excluded_middle (j = i)) as [ij_eq|ij_neq].
            +   rewrite in_ulist_add in v_nin.
                rewrite not_or in v_nin.
                subst.
                destruct v_nin; contradiction.
            +   reflexivity.
    }
    rewrite ulist_prop_add.
    split.
    1: exact v_z.
    apply IHl.
    -   rewrite ulist_prop_add in l_in.
        apply l_in.
    -   rewrite ulist_image_add, ulist_unique_add in l_uni.
        apply l_uni.
    -   rewrite ulist_image_add, ulist_sum_add in l_zero.
        rewrite <- v_z in l_zero.
        rewrite plus_lid in l_zero.
        exact l_zero.
Qed.


(*
Local Open Scope card_scope.
(* end hide *)

Lemma tensor_grade_project_finite : ∀ (A : tensor_algebra_base V) k,
        tensor_finite V (λ n, If k = n then [A|] n else 0).
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

Definition tensor_grade_project (A : tensor_algebra_base V ) k :=
    [_|tensor_grade_project_finite A k].

Definition homogeneous_tensor A := ∃ k (M : k_tensor k),
    A = power_to_tensor V M.
Definition tensor_grade (A : tensor_algebra_base V ) k := ∃ (M : k_tensor k),
    A = power_to_tensor V M.

Theorem tensor_zero_homogeneous : homogeneous_tensor 0.
    exists 0, 0.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros x.
    unfold power_to_tensor_base.
    destruct (strong_excluded_middle (0 = x)) as [x_eq|x_neq].
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
    unfold power_to_tensor_base; cbn.
    apply functional_ext.
    intros x.
    classic_case (k = x) as [eq|neq].
    -   destruct eq; cbn.
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
    unfold power_to_tensor_base.
    case_if.
    -   subst.
        cbn.
        reflexivity.
    -   reflexivity.
Qed.

Lemma tensor_max_nz_ex : ∀ A : tensor_algebra_base V,
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
    change (set_type (tensor_finite V)) with (tensor_algebra_base V) in *.
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
                unfold neg, plus; cbn.
                case_if; try contradiction.
                rewrite plus_rinv.
                reflexivity.
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
        = power_to_tensor V ([A|] k).
    intros A k.
    unfold tensor_decompose_grade.
    classic_case (k < tensor_max_nz A) as [k_lt|k_ge].
    -   rewrite func_to_list_nth_lt by exact k_lt.
        unfold tensor_grade_project.
        apply set_type_eq; cbn.
        apply functional_ext.
        unfold power_to_tensor_base.
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
        unfold power_to_tensor_base.
        destruct (strong_excluded_middle (k = x)) as [eq|neq].
        +   destruct eq.
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
    specialize (n_least n (Logic.eq_refl _)).
    contradiction.
Qed.

Lemma power_to_tensor_eq_grade : ∀ k1 k2
        (A : k_tensor k1) (B : k_tensor k2),
        0 ≠ A → power_to_tensor V A = power_to_tensor V B → k1 = k2.
    intros k1 k2 A B A_nz eq.
    apply eq_set_type in eq; cbn in eq.
    assert (power_to_tensor_base V A k1 = power_to_tensor_base V B k1)
        as eq2.
    {
        rewrite eq.
        reflexivity.
    }
    clear eq; rename eq2 into eq.
    unfold power_to_tensor_base in eq.
    destruct (strong_excluded_middle (k1 = k1)) as [k1_eq|k1_neq].
    2: contradiction.
    destruct (strong_excluded_middle (k2 = k1)) as [k_eq|k_neq].
    1: symmetry; exact k_eq.
    destruct k1_eq; cbn in eq.
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
        rewrite (power_to_tensor_zero V) in A_nz.
        contradiction.
    }
    apply (power_to_tensor_eq_grade _ _ A1 A2 A1_neq).
    rewrite <- A1_eq, <- A2_eq.
    reflexivity.
Qed.

Lemma power_to_tensor_grade : ∀ k (A : k_tensor k),
        tensor_grade (power_to_tensor V A) k.
    intros k A.
    exists A.
    reflexivity.
Qed.

Lemma tensor_grade_zero_eq : ∀ A k, tensor_grade A k → ∀ n, n ≠ k → 0 = [A|] n.
    intros A k A_grade n n_neq.
    destruct A_grade as [A' A_eq]; subst A.
    cbn.
    unfold power_to_tensor_base.
    destruct (strong_excluded_middle (k = n)) as [eq|neq].
    -   exfalso; symmetry in eq; contradiction.
    -   reflexivity.
Qed.

Lemma tensor_decompose_plus_nth : ∀ a b n, let z := [_|tensor_zero_homogeneous]
        in [list_nth (tensor_decompose_grade (a + b)) n z|] =
        [list_nth (tensor_decompose_grade a) n z|] +
        [list_nth (tensor_decompose_grade b) n z|].
    intros a b n z.
    unfold z.
    do 3 rewrite tensor_decompose_nth.
    pose proof (power_to_tensor_plus V) as stupid.
    rewrite stupid.
    reflexivity.
Qed.
*)
(* begin hide *)
End TensorAlgebra.
(* end hide *)
