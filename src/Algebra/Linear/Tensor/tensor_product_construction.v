Require Import init.

Require Export linear_base.
Require Import linear_free.
Require Import linear_subspace.
Require Import linear_span.
Require Import module_category.

Require Import set.
Require Import card.

Require Import list.
Require Import plus_sum.

Section TensorProduct.

Context {F : CRing} (M N : Module F).

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

Let FR := free_linear U (V1 * V2).
Let to_FR a b := to_free F (V1 * V2) (a, b).

Let FR_plus := free_plus_class F (V1 * V2).
Let FR_zero := free_zero F (V1 * V2).
Let FR_neg := free_neg F (V1 * V2).
Let FR_plus_comm := free_plus_comm_class F (V1 * V2).
Let FR_plus_assoc := free_plus_assoc_class F (V1 * V2).
Let FR_plus_lid := free_plus_lid_class F (V1 * V2).
Let FR_plus_linv := free_plus_linv_class F (V1 * V2).
Let FR_scalar := free_scalar F (V1 * V2).
Let FR_scalar_id := free_scalar_id_class F (V1 * V2).
Let FR_scalar_ldist := free_scalar_ldist_class F (V1 * V2).
Let FR_scalar_rdist := free_scalar_rdist_class F (V1 * V2).
Let FR_scalar_comp := free_scalar_comp_class F (V1 * V2).
Existing Instances FR_plus FR_zero FR_neg FR_plus_comm FR_plus_assoc FR_plus_lid
    FR_plus_linv FR_scalar FR_scalar_id FR_scalar_ldist FR_scalar_rdist
    FR_scalar_comp.

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
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite tensor_lscalar_base.
    apply scalar_neg_one.
Qed.
Theorem tensor_mult_rneg_base : ∀ u v, u ⊗ (-v) = -(u ⊗ v).
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite tensor_rscalar_base.
    apply scalar_neg_one.
Qed.

Definition simple_tensor_base T := ∃ a b, T = a ⊗ b.

Local Open Scope card_scope.

Theorem tensor_sum_base : ∀ T, ∃ l : list (set_type simple_tensor_base),
        T = list_sum (list_image l (λ x, [x|])).
    intros T.
    equiv_get_value T.
    pose proof (free_fin T) as T_fin.
    apply fin_nat_ex in T_fin as [n n_eq].
    revert T n_eq.
    nat_induction n.
    {
        intros T eq.
        exists list_end.
        cbn.
        unfold zero; cbn.
        apply f_equal.
        apply free_eq.
        intros x.
        classic_contradiction contr.
        apply zero_is_empty in eq.
        assert (∅ x) as x_in.
        {
            rewrite <- eq.
            exact contr.
        }
        contradiction x_in.
    }
    intros T T_size.
    change (nat_suc n) with (1 + n) in T_size.
    rewrite <- nat_to_card_plus in T_size.
    unfold plus, nat_to_card in T_size; equiv_simpl in T_size.
    destruct T_size as [f [f_inj f_sur]].
    pose (x := f (inl [0|nat_0_lt_1])).
    pose (T' v := If v = [x|] then 0 else free_f T v).
    assert (nat_to_card n = |set_type (λ x, T' x ≠ 0)|) as T'n.
    {
        unfold nat_to_card; equiv_simpl.
        assert (∀ m : set_type (λ x, x < n), T' [f (inr m)|] ≠ 0) as T'_neq.
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
        split.
        -   intros a b eq.
            apply eq_set_type in eq; cbn in eq.
            apply set_type_eq in eq; cbn in eq.
            apply f_inj in eq.
            inversion eq.
            reflexivity.
        -   intros [b b_neq].
            assert (free_f T b ≠ 0) as b_neq2.
            {
                unfold T' in b_neq.
                case_if.
                1: contradiction.
                exact b_neq.
            }
            specialize (f_sur [b|b_neq2]) as [a a_eq].
            apply eq_set_type in a_eq; cbn in a_eq.
            destruct a as [a|a].
            +   unfold T' in b_neq.
                exfalso.
                case_if.
                1: contradiction.
                rewrite <- a_eq in n0.
                apply n0.
                apply eq_set_type.
                unfold x.
                apply f_equal.
                apply f_equal.
                destruct a as [a a_lt].
                apply set_type_eq; cbn.
                clear - a_lt.
                apply nat_lt_1 in a_lt.
                symmetry; exact a_lt.
            +   exists a.
                subst b.
                apply set_type_eq; cbn.
                reflexivity.
    }
    assert (finite (|set_type (λ x, T' x ≠ 0)|)) as T'_fin.
    {
        rewrite <- T'n.
        apply nat_is_finite.
    }
    specialize (IHn (make_free T' T'_fin) T'n) as [l l_eq].
    pose (x' := free_f T [x|] · (fst [x|] ⊗ snd [x|])).
    assert (simple_tensor_base x') as x'_simple.
    {
        exists (free_f T [x|] · fst [x|]), (snd [x|]).
        unfold x'.
        rewrite tensor_lscalar_base.
        reflexivity.
    }
    exists ([x'|x'_simple] :: l).
    cbn.
    unfold x'.
    clear x' x'_simple.
    rewrite <- l_eq.
    assert (T = free_f T [x|] · to_FR (fst [x|]) (snd [x|]) + (make_free T' T'_fin)) as eq.
    {
        apply free_eq.
        intros v.
        unfold T'.
        unfold plus; cbn.
        unfold scalar_mult; cbn.
        replace (fst [x|], snd [x|]) with [x|].
        2: destruct [x|]; reflexivity.
        case_if.
        -   subst v.
            rewrite plus_rid.
            rewrite mult_rid.
            reflexivity.
        -   rewrite mult_ranni.
            rewrite plus_lid.
            reflexivity.
    }
    unfold scalar_mult, plus, tensor_mult_base, to_quotient; cbn.
    rewrite eq at 1.
    equiv_simpl.
    rewrite neg_plus.
    rewrite (plus_comm (_ · to_FR _ _)).
    rewrite plus_assoc.
    rewrite <- (plus_assoc _ (_ · to_FR _ _)).
    rewrite plus_rinv.
    rewrite plus_rid.
    rewrite plus_rinv.
    apply linear_span_zero.
Qed.

End TensorProduct.
