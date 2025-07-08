Require Import init.

Require Export tensor_algebra_defs.
Require Import tensor_algebra_direct_base.
Require Import algebra_category.
Require Import category_initterm.
Require Import equivalence.
Require Import linear_grade_sum.
Require Import linear_free.
Require Import ring_ideal.

Require Import list.
Require Import unordered_list.

(* begin hide *)
Section TensorAlgebraCategory.

(* end hide *)
Context {U : CRing} (V : Module U).

Let f := make_module_homomorphism U V (algebra_module (tensor_algebra_object V))
    (vector_to_tensor V)
    (vector_to_tensor_plus V)
    (vector_to_tensor_scalar V).

Definition tensor_to_algebra_base := make_to_algebra _ _ f.

Let FR_module := free_linear U (list V).
Let FR := module_V FR_module.
Let to_FR a := to_free U (list V) a.

Let FR_grade := free_grade U (list V).
Existing Instances FR_grade FR_mult FR_ldist FR_rdist FR_lscalar FR_rscalar
    FR_mult_assoc FR_one FR_mult_lid FR_mult_rid.

Theorem tensor_algebra_ex : ∃ T, @initial (TO_ALGEBRA V) T.
Proof.
    pose (TASM := tensor_algebra_scalar_mult V).
    pose (TASO := tensor_algebra_scalar_id V).
    pose (TASC := tensor_algebra_scalar_comp V).
    pose (TASL := tensor_algebra_scalar_ldist V).
    pose (TASR := tensor_algebra_scalar_rdist V).
    exists tensor_to_algebra_base.
    unfold tensor_to_algebra_base, initial; cbn.
    intros [A g].
    change (ModuleObjHomomorphism V (algebra_module A)) with (morphism V (algebra_module A)) in g.
    unfold to_algebra_set; cbn.
    assert (∀ α v, to_qring (tensor_ideal V) (α · v) =
        α · (to_qring (tensor_ideal V) v)) as to_qring_scalar.
    {
        intros α v.
        unfold scalar_mult at 2; cbn.
        unfold to_qring, to_qring_type; equiv_simpl.
        reflexivity.
    }
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        pose (h1 := free_extend U (list V) (λ l, list_prod (list_image g l))).
        assert (∀ v, h1 (to_FR [v]) = g v) as h1_vec.
        {
            intros v.
            unfold h1.
            rewrite (free_extend_free _ _).
            rewrite list_image_single.
            rewrite list_prod_single.
            reflexivity.
        }
        assert (HomomorphismPlus h1) as h1_plus.
        {
            split.
            apply module_homo_plus.
        }
        assert (∀ α v, h1 (α · v) = α · h1 v) as h1_scalar.
        {
            apply module_homo_scalar.
        }
        assert (HomomorphismMult h1) as h1_mult.
        {
            split.
            intros a b.
            induction a as [|a u] using grade_induction.
            {
                rewrite mult_lanni.
                rewrite homo_zero.
                rewrite mult_lanni.
                reflexivity.
            }
            rewrite rdist.
            do 2 rewrite (homo_plus (f := h1)).
            rewrite rdist.
            rewrite IHu.
            apply rplus.
            clear u IHu.
            induction b as [|b v] using grade_induction.
            {
                rewrite mult_ranni.
                rewrite homo_zero.
                rewrite mult_ranni.
                reflexivity.
            }
            rewrite ldist.
            do 2 rewrite (homo_plus (f := h1)).
            rewrite ldist.
            rewrite IHv.
            apply rplus.
            clear v IHv.
            destruct a as [a a_homo], b as [b b_homo]; cbn.
            destruct a_homo as [u au], b_homo as [v bv].
            apply to_free_ex in au as [α a_eq]; subst a.
            apply to_free_ex in bv as [β b_eq]; subst b.
            rewrite scalar_lmult, scalar_rmult.
            do 4 rewrite h1_scalar.
            rewrite scalar_lmult, scalar_rmult.
            do 2 apply f_equal.
            unfold mult at 1; cbn.
            rewrite (free_bilinear_free _ _).
            unfold h1.
            do 3 rewrite (free_extend_free _ _).
            rewrite list_image_conc.
            apply list_prod_conc.
        }
        assert (∀ x y, eq_equal (ideal_equiv (tensor_ideal V)) x y →
            h1 x = h1 y) as wd.
        {
            intros x y eq.
            cbn in eq.
            rewrite <- plus_0_anb_a_b.
            rewrite <- homo_neg.
            rewrite <- homo_plus.
            remember (x - y) as v.
            rewrite <- Heqv in eq.
            rewrite <- Heqv.
            clear x y Heqv.
            destruct eq as [l v_eq]; subst v.
            induction l as [|a l] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                setoid_rewrite homo_zero.
                reflexivity.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite homo_plus.
            rewrite <- IHl; clear l IHl.
            rewrite plus_rid.
            destruct a as [[a b] v]; cbn.
            do 2 setoid_rewrite homo_mult.
            assert (h1 [v|] = 0) as eq.
            {
                clear a b.
                destruct v as [v [v_in|v_in]]; cbn.
                -   destruct v_in as [a [b v_eq]]; subst v.
                    do 2 setoid_rewrite homo_plus.
                    setoid_rewrite homo_neg.
                    do 3 rewrite h1_vec.
                    rewrite <- plus_assoc.
                    rewrite module_homo_plus.
                    rewrite <- neg_plus.
                    apply plus_rinv.
                -   destruct v_in as [α [u v_eq]]; subst v.
                    rewrite homo_plus.
                    rewrite homo_neg.
                    rewrite h1_scalar.
                    do 2 rewrite h1_vec.
                    rewrite module_homo_scalar.
                    apply plus_rinv.
            }
            rewrite eq.
            rewrite mult_ranni, mult_lanni.
            reflexivity.
        }
        pose (h := unary_op wd : (tensor_algebra_base V) → algebra_module A).
        assert (∀ u v, h (u + v) = h u + h v) as h_plus.
        {
            intros u v.
            equiv_get_value u v.
            unfold plus at 1, tensor_algebra_base, quotient_ring; cbn.
            unfold h; equiv_simpl.
            apply homo_plus.
        }
        assert (∀ a v, h (a · v) = a · h v) as h_scalar.
        {
            intros a v.
            equiv_get_value v.
            unfold scalar_mult at 1; cbn.
            unfold h; equiv_simpl.
            apply h1_scalar.
        }
        assert (∀ u v, h (u * v) = h u * h v) as h_mult.
        {
            intros u v.
            equiv_get_value u v.
            unfold mult at 1, tensor_algebra_base, quotient_ring; cbn.
            unfold h; equiv_simpl.
            apply homo_mult.
        }
        assert (h 1 = 1) as h_one.
        {
            unfold h.
            unfold one at 1; equiv_simpl.
            unfold h1.
            unfold one at 1; cbn.
            rewrite (free_extend_free _ _).
            rewrite list_image_end.
            reflexivity.
        }
        exists (make_algebra_homomorphism U (tensor_algebra_object V) _
            h h_plus h_scalar h_mult h_one).
        intros x; cbn.
        unfold h, vector_to_tensor.
        unfold to_qring.
        equiv_simpl.
        rewrite h1_vec.
        reflexivity.
    -   intros [f1 f1_eq] [f2 f2_eq].
        apply set_type_eq; cbn.
        apply algebra_homomorphism_eq.
        intros v.
        equiv_get_value v.
        change (to_equiv (ideal_equiv (tensor_ideal V)) v) with
            (to_qring (tensor_ideal V) v).
        induction v as [|a v] using grade_induction.
        {
            rewrite homo_zero.
            do 2 rewrite algebra_homo_zero.
            reflexivity.
        }
        rewrite homo_plus.
        do 2 rewrite algebra_homo_plus.
        rewrite IHv.
        apply rplus.
        clear v IHv.
        destruct a as [v [l vl]]; cbn.
        apply to_free_ex in vl as [α v_eq]; subst v.
        rewrite to_qring_scalar.
        do 2 rewrite algebra_homo_scalar.
        apply f_equal.
        clear α.
        induction l.
        {
            do 2 rewrite algebra_homo_one.
            reflexivity.
        }
        cbn.
        rewrite <- list_conc_single.
        rewrite <- (free_bilinear_free U (list (module_V V))
            (λ a b, to_free U (list (module_V V)) (a + b)) [a] l).
        change (free_bilinear _ _ _ _ _) with (to_free U _ [a] * to_free U _ l).
        rewrite homo_mult.
        do 2 rewrite algebra_homo_mult.
        rewrite IHl.
        apply rmult.
        clear l IHl.
        rewrite f1_eq, f2_eq.
        reflexivity.
Qed.

End TensorAlgebraCategory.
