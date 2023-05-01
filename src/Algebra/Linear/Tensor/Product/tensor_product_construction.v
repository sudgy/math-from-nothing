Require Import init.

Require Export linear_base.
Require Import linear_free.
Require Import linear_subspace.
Require Import linear_span.
Require Import linear_grade_sum.
Require Import module_category.

Require Import set.
Require Import card.

Require Import unordered_list.

(* begin hide *)
Section TensorProduct.

(* end hide *)
Context {F : CRingObj} (M N : ModuleObj F).

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
Let V1 := module_V M.
Let VP1 := module_plus M.
Let VZ1 := module_zero M.
Let VN1 := module_neg M.
Let VPA1 := module_plus_assoc M.
Let VPC1 := module_plus_comm M.
Let VPZ1 := module_plus_lid M.
Let VPN1 := module_plus_linv M.
Let SM1 := module_scalar M.
Let SMO1 := module_scalar_id M.
Let SML1 := module_scalar_ldist M.
Let SMR1 := module_scalar_rdist M.
Let SMC1 := module_scalar_comp M.
Let V2 := module_V N.
Let VP2 := module_plus N.
Let VZ2 := module_zero N.
Let VN2 := module_neg N.
Let VPA2 := module_plus_assoc N.
Let VPC2 := module_plus_comm N.
Let VPZ2 := module_plus_lid N.
Let VPN2 := module_plus_linv N.
Let SM2 := module_scalar N.
Let SMO2 := module_scalar_id N.
Let SML2 := module_scalar_ldist N.
Let SMR2 := module_scalar_rdist N.
Let SMC2 := module_scalar_comp N.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP1 VZ1 VN1
    VPA1 VPC1 VPZ1 VPN1 SM1 SMO1 SML1 SMR1 SMC1 VP2 VZ2 VN2 VPA2 VPC2 VPZ2 VPN2
    SM2 SMO2 SML2 SMR2 SMC2.

(* end hide *)
Let FR_module := free_linear F (V1 * V2).
Let FR := module_V FR_module.
Let to_FR a b := to_free F (V1 * V2) (a, b).

(* begin hide *)
Let FR_plus := module_plus FR_module.
Let FR_zero := module_zero FR_module.
Let FR_neg := module_neg FR_module.
Let FR_plus_comm := module_plus_comm FR_module.
Let FR_plus_assoc := module_plus_assoc FR_module.
Let FR_plus_lid := module_plus_lid FR_module.
Let FR_plus_linv := module_plus_linv FR_module.
Let FR_scalar := module_scalar FR_module.
Let FR_scalar_id := module_scalar_id FR_module.
Let FR_scalar_ldist := module_scalar_ldist FR_module.
Let FR_scalar_rdist := module_scalar_rdist FR_module.
Let FR_scalar_comp := module_scalar_comp FR_module.
Existing Instances FR_plus FR_zero FR_neg FR_plus_comm FR_plus_assoc FR_plus_lid
    FR_plus_linv FR_scalar FR_scalar_id FR_scalar_ldist FR_scalar_rdist
    FR_scalar_comp.

(* end hide *)
Let sub1 v := ∃ a b c, v = to_FR (a + b) c - to_FR a c - to_FR b c.
Let sub2 v := ∃ a b c, v = to_FR a (b + c) - to_FR a b - to_FR a c.
Let sub3 v := ∃ a m n, v = a · to_FR m n - to_FR (a · m) n.
Let sub4 v := ∃ a m n, v = a · to_FR m n - to_FR m (a · n).
Definition tensor_product_ideal := sub1 ∪ sub2 ∪ sub3 ∪ sub4.

Definition tensor_space := linear_span_quotient U tensor_product_ideal.
Definition tensor_mult_base a b := to_quotient U tensor_product_ideal (to_free F (V1 * V2) (a, b)).
Local Infix "⊗" := tensor_mult_base.

Definition tensor_plus := quotient_space_plus (linear_span_subspace U tensor_product_ideal).
Definition tensor_zero := quotient_space_zero (linear_span_subspace U tensor_product_ideal).
Definition tensor_neg := quotient_space_neg (linear_span_subspace U tensor_product_ideal).
Definition tensor_plus_assoc := quotient_space_plus_assoc (linear_span_subspace U tensor_product_ideal).
Definition tensor_plus_comm := quotient_space_plus_comm (linear_span_subspace U tensor_product_ideal).
Definition tensor_plus_lid := quotient_space_plus_lid (linear_span_subspace U tensor_product_ideal).
Definition tensor_plus_linv := quotient_space_plus_linv (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_mult := quotient_space_scalar_mult (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_id := quotient_space_scalar_id (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_ldist := quotient_space_scalar_ldist (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_rdist := quotient_space_scalar_rdist (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_comp := quotient_space_scalar_comp (linear_span_subspace U tensor_product_ideal).
Existing Instances tensor_plus tensor_zero tensor_neg tensor_plus_assoc
    tensor_plus_comm tensor_plus_lid tensor_plus_linv tensor_scalar_mult
    tensor_scalar_id tensor_scalar_ldist tensor_scalar_rdist tensor_scalar_comp.

Theorem tensor_ldist_base : ∀ a b c, a ⊗ (b + c) = a ⊗ b + a ⊗ c.
Proof.
    intros a b c.
    unfold tensor_mult_base; cbn.
    unfold plus at 2; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    left; left; right.
    exists a, b, c.
    unfold to_FR.
    rewrite neg_plus.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem tensor_rdist_base : ∀ a b c, (a + b) ⊗ c = a ⊗ c + b ⊗ c.
Proof.
    intros a b c.
    unfold tensor_mult_base, plus at 2; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    repeat left.
    exists a, b, c.
    unfold to_FR.
    rewrite neg_plus.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem tensor_lscalar_base : ∀ a u v, (a · u) ⊗ v = a · (u ⊗ v).
Proof.
    intros a u v.
    symmetry.
    unfold tensor_mult_base, scalar_mult; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    left; right.
    exists a, u, v; cbn.
    unfold to_FR.
    reflexivity.
Qed.

Theorem tensor_rscalar_base : ∀ a u v, u ⊗ (a · v) = a · (u ⊗ v).
Proof.
    intros a u v.
    symmetry.
    unfold tensor_mult_base, scalar_mult; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    right.
    exists a, u, v; cbn.
    unfold to_FR.
    reflexivity.
Qed.

Theorem tensor_mult_lneg_base : ∀ u v, (-u) ⊗ v = -(u ⊗ v).
Proof.
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite tensor_lscalar_base.
    apply scalar_neg_one.
Qed.
Theorem tensor_mult_rneg_base : ∀ u v, u ⊗ (-v) = -(u ⊗ v).
Proof.
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite tensor_rscalar_base.
    apply scalar_neg_one.
Qed.

Definition simple_tensor_base T := ∃ a b, T = a ⊗ b.

(* begin hide *)
Local Open Scope card_scope.

(* end hide *)
Theorem tensor_sum_base : ∀ T, ∃ l : ulist (set_type simple_tensor_base),
    T = ulist_sum (ulist_image (λ x, [x|]) l).
Proof.
    intros T.
    equiv_get_value T.
    destruct T as [T T_fin'].
    unfold sum_module_finite in T_fin'.
    pose proof T_fin' as T_fin.
    (* TODO: Get rid of the use of cardinals here *)
    rewrite simple_finite_finite in T_fin.
    apply fin_nat_ex in T_fin as [n n_eq].
    revert T T_fin' n_eq.
    unfold sum_module_finite.
    nat_induction n.
    {
        intros T T_fin' eq.
        exists ulist_end.
        rewrite ulist_image_end, ulist_sum_end.
        unfold zero; cbn.
        apply f_equal.
        apply set_type_eq; cbn.
        apply functional_ext.
        intros x.
        classic_contradiction contr.
        apply zero_is_empty in eq.
        assert (∅ x) as x_in.
        {
            rewrite <- eq.
            rewrite neq_sym.
            exact contr.
        }
        contradiction x_in.
    }
    intros T T_fin' T_size.
    change (nat_suc n) with (1 + n) in T_size.
    rewrite <- nat_to_card_plus in T_size.
    unfold plus, nat_to_card in T_size; equiv_simpl in T_size.
    destruct T_size as [f [f_inj f_sur]].
    pose (x := f (inl [0|nat_one_pos])).
    pose (T' v := If v = [x|] then 0 else T v).
    assert (nat_to_card n = |set_type (λ x, 0 ≠ T' x)|) as T'n.
    {
        unfold nat_to_card; equiv_simpl.
        assert (∀ m : set_type (λ x, x < n), 0 ≠ T' [f (inr m)|]) as T'_neq.
        {
            intros m.
            unfold T'.
            case_if.
            -   unfold x in e.
                apply set_type_eq in e.
                apply f_inj in e.
                inversion e.
            -   destruct (f (inr m)) as [fm fm_neq].
                exact fm_neq.
        }
        exists (λ m, [[f (inr m)|] | T'_neq m]).
        split; split.
        -   intros a b eq.
            apply set_type_eq in eq; cbn in eq.
            apply set_type_eq in eq; cbn in eq.
            apply f_inj in eq.
            inversion eq.
            reflexivity.
        -   intros [b b_neq].
            assert (0 ≠ T b) as b_neq2.
            {
                unfold T' in b_neq.
                case_if.
                1: contradiction.
                exact b_neq.
            }
            pose proof (sur f [b|b_neq2]) as [a a_eq].
            apply set_type_eq in a_eq; cbn in a_eq.
            destruct a as [a|a].
            +   unfold T' in b_neq.
                exfalso.
                case_if.
                1: contradiction.
                rewrite <- a_eq in n0.
                apply n0.
                apply set_type_eq.
                unfold x.
                apply f_equal.
                apply f_equal.
                destruct a as [a a_lt].
                apply set_type_eq; cbn.
                clear - a_lt.
                apply nat_lt_one_eq in a_lt.
                symmetry; exact a_lt.
            +   exists a.
                subst b.
                apply set_type_eq; cbn.
                reflexivity.
    }
    assert (finite (|set_type (λ x, 0 ≠ T' x)|)) as T'_fin.
    {
        rewrite <- T'n.
        apply nat_is_finite.
    }
    rewrite <- simple_finite_finite in T'_fin.
    specialize (IHn T' T'_fin T'n) as [l l_eq].
    pose (x' := T [x|] · (fst [x|] ⊗ snd [x|])).
    assert (simple_tensor_base x') as x'_simple.
    {
        exists (T [x|] · fst [x|]), (snd [x|]).
        unfold x'.
        rewrite tensor_lscalar_base.
        reflexivity.
    }
    exists ([x'|x'_simple] ː l).
    rewrite ulist_image_add, ulist_sum_add.
    unfold x'; cbn.
    clear x' x'_simple.
    rewrite <- l_eq.
    assert (T = [T [x|] · to_FR (fst [x|]) (snd [x|]) + [T'|T'_fin]|]) as eq.
    {
        apply functional_ext.
        intros v.
        unfold T'.
        unfold plus; cbn.
        unfold scalar_mult; cbn.
        unfold scalar_mult; cbn.
        replace (fst [x|], snd [x|]) with [x|].
        2: destruct [x|]; reflexivity.
        unfold single_to_sum_module_base.
        assert ((v = [x|]) = ([x|] = v)) as eq.
        {
            apply propositional_ext; split; intro; symmetry; assumption.
        }
        rewrite eq.
        case_if.
        -   subst v; cbn.
            rewrite plus_rid.
            rewrite mult_rid.
            reflexivity.
        -   rewrite mult_ranni.
            rewrite plus_lid.
            reflexivity.
    }
    unfold scalar_mult, plus, tensor_mult_base, to_quotient; cbn.
    equiv_simpl.
    applys_eq linear_span_zero.
    symmetry.
    apply plus_0_anb_a_b.
    apply set_type_eq; cbn.
    exact eq.
Qed.
(* begin hide *)

End TensorProduct.
(* end hide *)
