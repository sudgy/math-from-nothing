Require Import init.

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
Context {F : CRingObj} (V : ModuleObj F).
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
Let VP := module_plus V.
Let VZ := module_zero V.
Let VN := module_neg V.
Let VPA := module_plus_assoc V.
Let VPC := module_plus_comm V.
Let VPZ := module_plus_lid V.
Let VPN := module_plus_linv V.
Let VSM := module_scalar V.
Let VSMO := module_scalar_id V.
Let VSML := module_scalar_ldist V.
Let VSMR := module_scalar_rdist V.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP VZ VN VPA
    VPC VPZ VPN VSM VSMO VSML VSMR.

Record to_algebra := make_to_algebra {
    to_algebra_algebra : AlgebraObj F;
    to_algebra_homo : ModuleObjHomomorphism V (algebra_module to_algebra_algebra);
}.

Definition to_algebra_set (f g : to_algebra)
    (h : cat_morphism (ALGEBRA F)
                      (to_algebra_algebra f)
                      (to_algebra_algebra g))
    := ∀ x, algebra_homo_f h (module_homo_f (to_algebra_homo f) x) =
            module_homo_f (to_algebra_homo g) x.

Definition to_algebra_compose {F G H : to_algebra}
    (f : set_type (to_algebra_set G H)) (g : set_type (to_algebra_set F G))
    := [f|] ∘ [g|].

Lemma to_algebra_set_compose_in {F' G H : to_algebra} :
    ∀ (f : set_type (to_algebra_set G H)) g,
    to_algebra_set F' H (to_algebra_compose f g).
Proof.
    intros [f f_eq] [g g_eq].
    unfold to_algebra_set in *.
    unfold to_algebra_compose; cbn.
    intros x.
    rewrite g_eq.
    apply f_eq.
Qed.

Lemma to_algebra_set_id_in : ∀ f : to_algebra, to_algebra_set f f 𝟙.
Proof.
    intros f.
    unfold to_algebra_set.
    intros x.
    cbn.
    reflexivity.
Qed.

Program Instance TO_ALGEBRA : Category := {
    cat_U := to_algebra;
    cat_morphism f g := set_type (to_algebra_set f g);
    cat_compose {F G H} f g := [_|to_algebra_set_compose_in f g];
    cat_id f := [_|to_algebra_set_id_in f];
}.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_assoc (ALGEBRA F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_lid (ALGEBRA F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_rid (ALGEBRA F)).
Qed.

Let f := make_module_homomorphism F V (algebra_module (tensor_algebra_object V))
    (vector_to_tensor V)
    (vector_to_tensor_plus V)
    (vector_to_tensor_scalar V).

Definition tensor_to_algebra_base := make_to_algebra _ f.

Let FR_module := free_linear F (list (module_V V)).
Let FR := module_V FR_module.
Let to_FR a := to_free F (list (module_V V)) a.

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
Let FR_grade := free_grade F (list (module_V V)).
Existing Instances FR_plus FR_zero FR_neg FR_plus_comm FR_plus_assoc FR_plus_lid
    FR_plus_linv FR_scalar FR_scalar_id FR_scalar_ldist FR_scalar_rdist
    FR_scalar_comp FR_grade FR_mult FR_ldist FR_rdist FR_lscalar FR_rscalar
    FR_mult_assoc FR_one FR_mult_lid FR_mult_rid.

Lemma tensor_algebra_ex_base : @initial TO_ALGEBRA tensor_to_algebra_base.
Proof.
    pose (TAP := tensor_algebra_plus V).
    pose (TAZ := tensor_algebra_zero V).
    pose (TAN := tensor_algebra_neg V).
    pose (TAPC := tensor_algebra_plus_comm V).
    pose (TAPA := tensor_algebra_plus_assoc V).
    pose (TAPZ := tensor_algebra_plus_lid V).
    pose (TAPN := tensor_algebra_plus_linv V).
    pose (TASM := tensor_algebra_scalar_mult V).
    pose (TASO := tensor_algebra_scalar_id V).
    pose (TASC := tensor_algebra_scalar_comp V).
    pose (TASL := tensor_algebra_scalar_ldist V).
    pose (TASR := tensor_algebra_scalar_rdist V).
    pose (TAM := tensor_mult_class V).
    pose (TAO := tensor_one V).
    pose (TAL := tensor_mult_ldist V).
    pose (TAR := tensor_mult_rdist V).
    unfold tensor_to_algebra_base, initial; cbn.
    intros [A g].
    pose (AP := algebra_plus A).
    pose (AZ := algebra_zero A).
    pose (AN := algebra_neg A).
    pose (APC := algebra_plus_comm A).
    pose (APA := algebra_plus_assoc A).
    pose (APZ := algebra_plus_lid A).
    pose (APN := algebra_plus_linv A).
    pose (ASM := algebra_scalar A).
    pose (ASO := algebra_scalar_id A).
    pose (ASC := algebra_scalar_comp A).
    pose (ASL := algebra_scalar_ldist A).
    pose (ASR := algebra_scalar_rdist A).
    pose (AM := algebra_mult A).
    pose (AO := algebra_one A).
    pose (AL := algebra_ldist A).
    pose (AR := algebra_rdist A).
    pose (AMA := algebra_mult_assoc A).
    pose (AML := algebra_mult_lid A).
    pose (AMR := algebra_mult_rid A).
    pose (ASML := algebra_scalar_lmult A).
    pose (ASMR := algebra_scalar_rmult A).
    unfold to_algebra_set; cbn.
    assert (∀ α v, to_qring (tensor_ideal V) (α · v) =
        α · (to_qring (tensor_ideal V) v)) as to_qring_scalar.
    {
        intros α v.
        unfold scalar_mult at 2; cbn.
        unfold to_qring; equiv_simpl.
        apply (ideal_eq_reflexive (tensor_ideal V)).
    }
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        pose (h1 := free_extend F (list (module_V V))
            (λ l, list_prod (list_image l (module_homo_f g)))).
        assert (∀ v, h1 (to_free F (list (module_V V)) [v]) = module_homo_f g v)
            as h1_vec.
        {
            intros v.
            unfold h1.
            rewrite (free_extend_free _ _).
            rewrite list_image_single.
            cbn.
            apply mult_rid.
        }
        assert (HomomorphismPlus h1) as h1_plus.
        {
            split.
            apply (free_extend_plus _ _).
        }
        assert (∀ α v, h1 (α · v) = α · h1 v) as h1_scalar.
        {
            apply (free_extend_scalar _ _).
        }
        assert (HomomorphismMult h1) as h1_mult.
        {
            split.
            intros a b.
            rewrite (grade_decomposition_eq a).
            rewrite (grade_decomposition_eq b).
            pose (u := grade_decomposition a).
            pose (v := grade_decomposition b).
            fold u v.
            clearbody u v.
            clear a b.
            induction u as [|a u] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                rewrite mult_lanni.
                rewrite homo_zero.
                rewrite mult_lanni.
                reflexivity.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite rdist.
            do 2 rewrite (homo_plus (f := h1)).
            rewrite rdist.
            rewrite IHu.
            apply rplus.
            clear u IHu.
            induction v as [|b v] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                rewrite mult_ranni.
                rewrite homo_zero.
                rewrite mult_ranni.
                reflexivity.
            }
            rewrite ulist_image_add, ulist_sum_add.
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
            apply list_prod_mult.
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
        pose (h := unary_op wd).
        assert (∀ u v, h (u + v) = h u + h v) as h_plus.
        {
            intros u v.
            equiv_get_value u v.
            unfold plus at 1; cbn.
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
            unfold mult at 1; cbn.
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
        exists (make_algebra_homomorphism F (tensor_algebra_object V) _
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
        rewrite (grade_decomposition_eq v).
        remember (grade_decomposition v) as l.
        clear v Heql.
        induction l as [|a l] using ulist_induction.
        {
            rewrite ulist_image_end, ulist_sum_end.
            rewrite to_qring_zero.
            do 2 rewrite algebra_homo_zero.
            reflexivity.
        }
        rewrite ulist_image_add, ulist_sum_add.
        rewrite to_qring_plus.
        do 2 rewrite algebra_homo_plus.
        rewrite IHl.
        apply rplus.
        clear l IHl.
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
        rewrite <- (free_bilinear_free F (list (module_V V))
            (λ a b, to_free F (list (module_V V)) (a ++ b)) [a] l).
        change (free_bilinear _ _ _ _ _) with (to_free F _ [a] * to_free F _ l).
        rewrite to_qring_mult.
        do 2 rewrite algebra_homo_mult.
        rewrite IHl.
        apply rmult.
        clear l IHl.
        rewrite f1_eq, f2_eq.
        reflexivity.
Qed.

Theorem tensor_algebra_ex : ∃ T, @initial TO_ALGEBRA T.
Proof.
    exists tensor_to_algebra_base.
    exact tensor_algebra_ex_base.
Qed.

Definition to_tensor_algebra := ex_val tensor_algebra_ex.
Definition tensor_algebra := to_algebra_algebra to_tensor_algebra.
Definition vector_to_tensor_homo := to_algebra_homo to_tensor_algebra.
Definition vector_to_tensor := module_homo_f vector_to_tensor_homo.

Theorem tensor_algebra_universal : @initial TO_ALGEBRA to_tensor_algebra.
Proof.
    apply (ex_proof tensor_algebra_ex).
Qed.

End TensorAlgebraCategory.

Arguments vector_to_tensor {F V}.
