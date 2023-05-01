Require Import init.

Require Import linear_extend.
Require Export tensor_algebra_defs.
Require Import tensor_algebra_traditional_base.
Require Import tensor_algebra_traditional_scalar.
Require Import tensor_algebra_traditional_vector.
Require Import tensor_algebra_traditional_mult.
Require Import tensor_product_universal.
Require Import tensor_power_universal.
Require Import linear_grade_sum.
Require Import module_category.
Require Import algebra_category.
Require Import category_initterm.

Require Import set.
Require Import list.
Require Import unordered_list.

(* begin hide *)
Section TensorAlgebraObjCategory.

(* end hide *)
Context {F : CRingObj} (V : ModuleObj F).

Let f := make_module_homomorphism F V (algebra_module (tensor_algebra_object V))
    (vector_to_tensor V)
    (vector_to_tensor_plus V)
    (vector_to_tensor_scalar V).

Definition tensor_to_algebra_base := make_to_algebra _ _ f.

Lemma tensor_algebra_ex_base : @initial (TO_ALGEBRA V) tensor_to_algebra_base.
Proof.
    pose (UP := cring_plus F).
    pose (UZ := cring_zero F).
    pose (UN := cring_neg F).
    pose (UPC := cring_plus_comm F).
    pose (UPZ := cring_plus_lid F).
    pose (UPN := cring_plus_linv F).
    pose (UM := cring_mult F).
    pose (UO := cring_one F).
    pose (VP := module_plus V).
    pose (VSM := module_scalar V).
    pose (TAG := tensor_grade V).
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
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        pose (h1 n (l : list (module_V V)) (eq : list_size l = n)
            := rfold mult 1 (list_image g l)).
        assert (∀ n, ∀ l1 a b l2 eq1 eq2 eq3,
            h1 n (l1 + (a + b) ꞉ l2) eq1 =
            h1 n (l1 + a ꞉ l2) eq2 + h1 n (l1 + b ꞉ l2) eq3) as h1_plus.
        {
            intros n l1 a b l2 eq1 eq2 eq3.
            unfold h1.
            clear eq1 eq2 eq3.
            induction l1.
            -   unfold list_conc; cbn.
                do 3 rewrite list_image_add.
                rewrite (module_homo_plus _ _ g).
                apply rdist.
            -   do 3 rewrite list_conc_add.
                do 3 rewrite list_image_add.
                do 3 rewrite rfold_add.
                rewrite IHl1; clear IHl1.
                apply ldist.
        }
        assert (∀ n, ∀ l1 a v l2 eq1 eq2,
            h1 n (l1 + (a · v) ꞉ l2) eq1 =
            a · h1 n (l1 + v ꞉ l2) eq2) as h1_scalar.
        {
            intros n l1 a v l2 eq1 eq2.
            unfold h1.
            clear eq1 eq2.
            induction l1.
            -   unfold list_conc; cbn.
                do 2 rewrite list_image_add.
                rewrite (module_homo_scalar _ _ g).
                apply scalar_lmult.
            -   do 2 rewrite list_conc_add.
                do 2 rewrite list_image_add.
                do 2 rewrite rfold_add.
                rewrite IHl1; clear IHl1.
                apply scalar_rmult.
        }
        pose (h2 n := make_multilinear _ n _ (h1 n) (h1_plus n) (h1_scalar n)).
        pose (h3 n := ex_singleton (tensor_power_universal V n (h2 n))).
        cbn in h3.
        pose (h4 i v := [h3 i|] v).
        assert (∀ n, ∀ l eq, [h3 n|]
            ([power_to_tensor V (vectors_to_power V l)|] n) = h1 n l eq)
            as h4_eq2.
        {
            intros n l eq.
            subst n.
            cbn.
            rewrite single_to_sum_module_base_eq.
            exact ([|h3 (list_size l)] l Logic.eq_refl).
        }
        pose (h := linear_extend h4).
        assert (h 1 = 1) as h_one.
        {
            assert (of_grade 0 1) as o_homo.
            {
                apply of_grade_ex.
                exists 1.
                reflexivity.
            }
            unfold h.
            rewrite (linear_extend_homo _ _ _ o_homo).
            cbn.
            pose (o := power_to_tensor V (vectors_to_power V list_end)).
            change (sum_module_type _ _) with (tensor_algebra_base V).
            change (one (U := tensor_algebra_base V)) with o.
            unfold o.
            rewrite (h4_eq2 0 list_end Logic.eq_refl).
            reflexivity.
        }
        assert (∀ u v, h (u * v) = h u * h v) as h_mult.
        {
            intros u v.
            induction u as [|u u'] using grade_induction.
            {
                rewrite mult_lanni.
                rewrite module_homo_zero.
                rewrite mult_lanni.
                reflexivity.
            }
            rewrite rdist.
            do 2 rewrite module_homo_plus.
            rewrite IHu'; clear IHu'.
            rewrite rdist.
            apply rplus; clear u'.
            induction v as [|v v'] using grade_induction.
            {
                rewrite mult_ranni.
                rewrite module_homo_zero.
                rewrite mult_ranni.
                reflexivity.
            }
            rewrite ldist.
            do 2 rewrite module_homo_plus.
            rewrite IHv'; clear IHv'.
            rewrite ldist.
            apply rplus; clear v'.
            destruct u as [u [i iu]]; cbn.
            destruct v as [v [j jv]]; cbn.
            unfold h.
            rewrite (linear_extend_homo _ _ _ iu).
            rewrite (linear_extend_homo _ _ _ jv).
            rewrite (tensor_mult_homo _ _ _ _ _ iu jv).
            rewrite (linear_extend_homo _ _ _ (tensor_mult_base_grade _ _ _ _ _)).
            apply of_grade_ex in iu as [u' u_eq]; cbn.
            apply of_grade_ex in jv as [v' v_eq]; cbn.
            subst u v.
            do 4 rewrite grade_to_from; cbn.
            unfold grade_to; cbn.
            do 3 rewrite single_to_sum_module_base_eq.
            rename u' into u, v' into v.
            pose proof (tensor_power_sum V u) as [ul u_eq]; subst u.
            induction ul as [|u ul] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                rewrite tensor_product_lanni.
                do 3 rewrite module_homo_zero.
                rewrite mult_lanni.
                reflexivity.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite tensor_rdist.
            do 3 rewrite module_homo_plus.
            rewrite IHul; clear IHul.
            rewrite rdist.
            apply rplus; clear ul.
            pose proof (tensor_power_sum V v) as [vl v_eq]; subst v.
            induction vl as [|v vl] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                rewrite tensor_product_ranni.
                do 3 rewrite module_homo_zero.
                rewrite mult_ranni.
                reflexivity.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite tensor_ldist.
            do 3 rewrite module_homo_plus.
            rewrite IHvl; clear IHvl.
            rewrite ldist.
            apply rplus; clear vl.
            destruct u as [u [α [ul u_eq]]]; cbn.
            destruct v as [v [β [vl v_eq]]]; cbn.
            subst u v.
            rewrite tensor_lscalar, tensor_rscalar.
            do 6 rewrite module_homo_scalar.
            rewrite scalar_lmult, scalar_rmult.
            do 2 apply f_equal.
            clear α β.
            destruct ul as [ul ul_eq]; cbn.
            destruct vl as [vl vl_eq]; cbn.
            pose proof ([|h3 (list_size ul)] ul Logic.eq_refl) as ul_eq2.
            cbn in ul_eq2.
            pose proof ([|h3 (list_size vl)] vl Logic.eq_refl) as vl_eq2.
            cbn in vl_eq2.
            subst i j; cbn.
            rewrite ul_eq2, vl_eq2.
            rewrite vectors_to_power_mult.
            rewrite ([|h3 (list_size ul + list_size vl)] (ul + vl)
                (list_size_conc ul vl)).
            cbn.
            unfold h1.
            rewrite list_image_conc.
            clear ul_eq2 vl_eq2.
            induction ul.
            -   cbn.
                rewrite mult_lid.
                reflexivity.
            -   rewrite list_image_add.
                rewrite list_conc_add.
                rewrite rfold_add.
                rewrite IHul.
                apply mult_assoc.
        }
        exists (make_algebra_homomorphism _ (tensor_algebra_object V) _
            h (module_homo_plus _ _ h) (module_homo_scalar _ _ h) h_mult h_one).
        cbn.
        intros v.
        assert (of_grade 1 (vector_to_tensor V v)) as v_grade.
        {
            apply of_grade_ex.
            exists (vectors_to_power V (v ꞉ list_end)).
            reflexivity.
        }
        unfold h.
        rewrite (linear_extend_homo _ _ _ v_grade).
        change (vector_to_tensor V v)
            with (power_to_tensor V (vectors_to_power V (v ꞉ list_end))).
        assert (list_size (v ꞉ list_end) = 1) as eq by reflexivity.
        rewrite (h4_eq2 1 (v ꞉ list_end) eq).
        unfold h1; cbn.
        apply mult_rid.
    -   intros [f1 f1_eq] [f2 f2_eq].
        apply set_type_eq; cbn.
        apply algebra_homomorphism_eq.
        intros v.
        induction v as [|v v'] using grade_induction.
        {
            do 2 rewrite algebra_homo_zero.
            reflexivity.
        }
        do 2 rewrite algebra_homo_plus.
        rewrite IHv; clear IHv.
        apply rplus; clear v'.
        destruct v as [v' [n nv]]; cbn.
        apply of_grade_ex in nv as [v v_eq]; subst v'.
        pose proof (tensor_power_sum V v) as [l v_eq]; subst v.
        induction l as [|v l] using ulist_induction.
        {
            rewrite ulist_image_end, ulist_sum_end.
            rewrite single_to_sum_module_zero.
            cbn.
            do 2 rewrite algebra_homo_zero.
            reflexivity.
        }
        rewrite ulist_image_add, ulist_sum_add.
        rewrite single_to_sum_module_plus.
        do 2 rewrite algebra_homo_plus.
        rewrite IHl; clear IHl.
        apply rplus; clear l.
        destruct v as [v [α [[l l_eq] v_eq]]]; cbn; subst v.
        rewrite single_to_sum_module_scalar.
        do 2 rewrite algebra_homo_scalar.
        apply f_equal.
        cbn.
        destruct l_eq; cbn.
        induction l as [|v l].
        {
            cbn.
            assert (scalar_to_tensor V 1 = 1) as eq by reflexivity.
            unfold scalar_to_tensor in eq.
            unfold UO in eq.
            cbn in *.
            unfold zero in eq; cbn in eq.
            unfold zero; cbn.
            unfold power_to_tensor in eq.
            rewrite eq.
            do 2 rewrite algebra_homo_one.
            reflexivity.
        }
        cbn.
        assert (@power_to_tensor F V (nat_suc (list_size l)) (tensor_mult
            V (tensor_power V (list_size l)) v (vectors_to_power V l)) =
            vector_to_tensor V v * power_to_tensor V (vectors_to_power V l))
            as eq.
        {
            assert (of_grade 1 (vector_to_tensor V v)) as v_homo.
            {
                apply of_grade_ex.
                exists (vectors_to_power V (v ꞉ list_end)).
                cbn.
                unfold vector_to_tensor.
                reflexivity.
            }
            assert (of_grade (list_size l) (power_to_tensor V (vectors_to_power V l)))
                as l_homo.
            {
                apply of_grade_ex.
                exists (vectors_to_power V l).
                reflexivity.
            }
            rewrite (tensor_mult_homo _ _ _ _ _ v_homo l_homo).
            cbn.
            change (tensor_mult V (cring_module F) v 1) with
                (vectors_to_power V (v ꞉ list_end)).
            change 1 with (list_size (v ꞉ list_end)).
            unfold tensor_mult_base.
            unfold grade_to; cbn.
            do 2 rewrite single_to_sum_module_base_eq.
            rewrite (vectors_to_power_mult V).
            rewrite <- power_to_tensor_k_eq.
            reflexivity.
        }
        unfold power_to_tensor in eq.
        rewrite eq; clear eq.
        do 2 rewrite algebra_homo_mult.
        apply f_equal2; [>clear IHl|exact IHl].
        rewrite f1_eq, f2_eq.
        reflexivity.
Qed.

Theorem tensor_algebra_ex : ∃ T, @initial (TO_ALGEBRA V) T.
Proof.
    exists tensor_to_algebra_base.
    exact tensor_algebra_ex_base.
Qed.

End TensorAlgebraObjCategory.
