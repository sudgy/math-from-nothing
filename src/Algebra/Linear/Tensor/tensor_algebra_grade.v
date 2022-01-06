Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_power_base.
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

(* begin hide *)
End TensorAlgebra.
(* end hide *)
