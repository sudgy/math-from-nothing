Require Import init.

Require Import linear_extend.
Require Import tensor_algebra_base.
Require Import tensor_algebra_scalar.
Require Import tensor_algebra_vector.
Require Import tensor_algebra_mult.
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

Lemma tensor_algebra_ex_base : @initial TO_ALGEBRA tensor_to_algebra_base.
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
    pose (TAGM := tensor_grade_mult V).
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
            := rfold mult 1 (list_image l (module_homo_f g))).
        assert (∀ n, ∀ l1 a b l2 eq1 eq2 eq3,
            h1 n (l1 ++ (a + b) :: l2) eq1 =
            h1 n (l1 ++ a :: l2) eq2 + h1 n (l1 ++ b :: l2) eq3) as h1_plus.
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
            h1 n (l1 ++ (a · v) :: l2) eq1 =
            a · h1 n (l1 ++ v :: l2) eq2) as h1_scalar.
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
        pose (h4 i v (H : of_grade i v) := module_homo_f [h3 i|] (ex_val H)).
        assert (∀ n, ∀ l eq li,
            h4 n (power_to_tensor V (vectors_to_power V l)) li = h1 n l eq)
            as h4_eq2.
        {
            intros n l eq li.
            unfold h4.
            unfold h3.
            pose proof [|ex_singleton (tensor_power_universal V n (h2 n))]
                as h2_eq.
            unfold multilinear_from_set in h2_eq; cbn in h2_eq.
            specialize (h2_eq _ eq).
            rewrite_ex_val a a_eq.
            subst n.
            destruct (Logic.eq_refl); cbn in h2_eq.
            apply power_to_tensor_eq in a_eq.
            subst a.
            exact h2_eq.
        }
        assert (linear_extend_plus_base h4) as h_plus_base.
        {
            intros u v i H1 H2.
            unfold h4.
            pose proof (of_grade_plus u v i H1 H2) as H3.
            rewrite (proof_irrelevance _ H3).
            unfold ex_val.
            destruct (ex_to_type _) as [uv' uv_eq]; cbn in *.
            destruct (ex_to_type _) as [u' u_eq]; cbn in *.
            destruct (ex_to_type _) as [v' v_eq]; cbn in *.
            clear H1 H2 H3.
            rewrite <- u_eq, <- v_eq in uv_eq.
            rewrite <- (power_to_tensor_plus V) in uv_eq.
            apply power_to_tensor_eq in uv_eq.
            rewrite uv_eq.
            apply module_homo_plus.
        }
        assert (linear_extend_scalar_base h4) as h_scalar_base.
        {
            intros a v i H.
            unfold h4.
            unfold ex_val.
            destruct (ex_to_type _) as [av' av_eq]; cbn in *.
            destruct (ex_to_type _) as [v' v_eq]; cbn in *.
            rewrite <- v_eq in av_eq.
            rewrite <- (power_to_tensor_scalar V) in av_eq.
            apply power_to_tensor_eq in av_eq.
            rewrite av_eq.
            apply module_homo_scalar.
        }
        pose (h := linear_extend h4).
        assert (∀ u v, h (u + v) = h u + h v) as h_plus.
        {
            apply linear_extend_plus; assumption.
        }
        assert (∀ a v, h (a · v) = a · h v) as h_scalar.
        {
            apply linear_extend_scalar; assumption.
        }
        assert (h 0 = 0) as h_zero.
        {
            rewrite <- (scalar_lanni 0).
            rewrite h_scalar.
            apply scalar_lanni.
        }
        assert (h 1 = 1) as h_one.
        {
            assert (of_grade 0 1) as o_homo.
            {
                exists 1.
                reflexivity.
            }
            unfold h.
            rewrite (linear_extend_homo h4 h_scalar_base _ _ o_homo).
            pose (o := power_to_tensor V (vectors_to_power V list_end)).
            change (one (U := tensor_algebra_base V)) with o.
            unfold o.
            cbn.
            rewrite (h4_eq2 0 list_end Logic.eq_refl).
            cbn.
            reflexivity.
        }
        assert (∀ u v, h (u * v) = h u * h v) as h_mult.
        {
            intros u v.
            rewrite (grade_decomposition_eq u).
            rewrite (grade_decomposition_eq v).
            remember (grade_decomposition u) as ul.
            remember (grade_decomposition v) as vl.
            clear u v Hequl Heqvl.
            induction ul as [|u ul] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                rewrite mult_lanni.
                rewrite h_zero.
                rewrite mult_lanni.
                reflexivity.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite rdist.
            do 2 rewrite h_plus.
            rewrite IHul; clear IHul.
            rewrite rdist.
            apply rplus; clear ul.
            induction vl as [|v vl] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                rewrite mult_ranni.
                rewrite h_zero.
                rewrite mult_ranni.
                reflexivity.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite ldist.
            do 2 rewrite h_plus.
            rewrite IHvl; clear IHvl.
            rewrite ldist.
            apply rplus; clear vl.
            destruct u as [u' [i [u u_eq]]]; cbn.
            destruct v as [v' [j [v v_eq]]]; cbn.
            subst u' v'.
            pose proof (tensor_power_sum V u) as [ul u_eq]; subst u.
            induction ul as [|u ul] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                rewrite single_to_grade_sum_zero.
                unfold TAZ, tensor_algebra_base in *.
                rewrite h_zero.
                do 2 rewrite mult_lanni.
                apply h_zero.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite single_to_grade_sum_plus.
            rewrite rdist.
            do 2 rewrite h_plus.
            rewrite rdist.
            rewrite IHul; clear IHul.
            apply rplus; clear ul.
            pose proof (tensor_power_sum V v) as [vl v_eq]; subst v.
            induction vl as [|v vl] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                rewrite single_to_grade_sum_zero.
                unfold TAZ, tensor_algebra_base in *.
                rewrite h_zero.
                do 2 rewrite mult_ranni.
                apply h_zero.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite single_to_grade_sum_plus.
            rewrite ldist.
            do 2 rewrite h_plus.
            rewrite ldist.
            rewrite IHvl; clear IHvl.
            apply rplus; clear vl.
            assert (∀ n (x : module_V (tensor_power V n)),
                of_grade n (power_to_tensor V x)) as ln.
            {
                intros n x.
                exists x.
                reflexivity.
            }
            unfold h.
            assert (∀ n x, linear_extend h4 (power_to_tensor V x) =
                h4 n (power_to_tensor V x) (ln n x)) as h4_eq.
            {
                intros n x.
                rewrite (linear_extend_homo _ h_scalar_base n _ (ln n x)).
                reflexivity.
            }
            do 2 rewrite h4_eq.
            rewrite (tensor_mult_homo _ i j _ _ (ln i [u|]) (ln j [v|])).
            rewrite power_to_tensor_tm.
            rewrite h4_eq; clear h4_eq.
            destruct u as [u [α [[ul ul_eq] u_eq]]].
            destruct v as [v [β [[vl vl_eq] v_eq]]].
            cbn in *.
            destruct ul_eq; cbn in *.
            destruct vl_eq; cbn in *.
            subst u v.
            pose (VuSM := module_scalar (tensor_power V (list_size ul))).
            pose (VvSM := module_scalar (tensor_power V (list_size vl))).
            pose (VuvSM := module_scalar (tensor_power V (list_size (ul++vl)))).
            assert (of_grade (list_size ul + list_size vl)
                (power_to_tensor V (α * β · vectors_to_power V (ul ++ vl))))
                as uv_grade.
            {
                rewrite power_to_tensor_scalar.
                apply of_grade_scalar.
                rewrite <- list_size_plus.
                apply ln.
            }
            rewrite (linear_extend_base_eq _ _ _ _ _ uv_grade).
            2: {
                rewrite (tensor_lscalar (tensor_power V (list_size ul))).
                rewrite (tensor_rscalar (tensor_power V (list_size ul))).
                do 2 rewrite module_homo_scalar.
                rewrite (vectors_to_power_mult V).
                do 3 rewrite (power_to_tensor_scalar V).
                rewrite scalar_comp.
                apply f_equal.
                symmetry; apply power_to_tensor_k_eq.
            }
            assert (∀ (γ : cring_U F) n l H1 H2, n = list_size l →
                h4 n (power_to_tensor V (scalar_mult (ScalarMult := module_scalar
                (tensor_power V (list_size l))) γ (vectors_to_power V l))) H1 =
                γ · h4 n (power_to_tensor V (vectors_to_power V l)) H2) as h4_eq.
            {
                intros γ n l γVl Vl l_eq.
                unfold h4.
                pose proof (ex_proof γVl) as eq1; cbn in eq1.
                pose proof (ex_proof Vl) as eq2; cbn in eq2.
                subst n.
                apply power_to_tensor_eq in eq1.
                apply power_to_tensor_eq in eq2.
                change (ex_type_val (ex_to_type γVl)) with (ex_val γVl) in eq1.
                change (ex_type_val (ex_to_type Vl)) with (ex_val Vl) in eq2.
                rewrite eq1, eq2.
                apply module_homo_scalar.
            }
            assert (∀ l, of_grade (list_size l)
                (power_to_tensor V (vectors_to_power V l))) as l_grade.
            {
                intros l.
                apply ln.
            }
            pose proof (l_grade (ul ++ vl)) as uvl_grade.
            rewrite (list_size_plus ul vl) in uvl_grade at 1.
            rewrite (h4_eq _ _ _ _ uvl_grade (Logic.eq_sym (list_size_plus ul vl))).
            rewrite (h4_eq _ _ _ _ (l_grade ul) Logic.eq_refl).
            rewrite (h4_eq _ _ _ _ (l_grade vl) Logic.eq_refl).
            rewrite scalar_lmult, scalar_rmult.
            rewrite scalar_comp.
            apply f_equal.
            rewrite (h4_eq2 (list_size ul + list_size vl) (ul ++ vl) (list_size_plus ul vl)).
            rewrite (h4_eq2 (list_size ul) ul Logic.eq_refl).
            rewrite (h4_eq2 (list_size vl) vl Logic.eq_refl).
            unfold h1; cbn.
            rewrite list_image_conc.
            clear l_grade uv_grade uvl_grade ln VuSM VvSM VuvSM.
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
            h h_plus h_scalar h_mult h_one).
        cbn.
        intros v.
        assert (of_grade 1 (vector_to_tensor V v)) as v_grade.
        {
            exists (vectors_to_power V (v :: list_end)).
            reflexivity.
        }
        unfold h.
        rewrite (linear_extend_homo _ h_scalar_base _ _ v_grade).
        change (vector_to_tensor V v)
            with (power_to_tensor V (vectors_to_power V (v :: list_end))).
        assert (list_size (v :: list_end) = 1) as eq by reflexivity.
        rewrite (h4_eq2 1 (v :: list_end) eq).
        unfold h1; cbn.
        apply mult_rid.
    -   intros [f1 f1_eq] [f2 f2_eq].
        apply set_type_eq; cbn.
        apply algebra_homomorphism_eq.
        intros v.
        rewrite (grade_decomposition_eq v).
        remember (grade_decomposition v) as l.
        clear v Heql.
        induction l as [|v l] using ulist_induction.
        {
            rewrite ulist_image_end, ulist_sum_end.
            unfold TAZ.
            pose proof (algebra_homo_zero f1) as eq1.
            pose proof (algebra_homo_zero f2) as eq2.
            cbn in *.
            rewrite eq1, eq2.
            reflexivity.
        }
        rewrite ulist_image_add, ulist_sum_add.
        do 2 rewrite algebra_homo_plus.
        rewrite IHl; clear IHl.
        apply rplus; clear l.
        destruct v as [v' [n [v v_eq]]]; subst v'; cbn.
        pose proof (tensor_power_sum V v) as [l v_eq]; subst v.
        induction l as [|v l] using ulist_induction.
        {
            rewrite ulist_image_end, ulist_sum_end.
            rewrite single_to_grade_sum_zero.
            unfold TAZ.
            pose proof (algebra_homo_zero f1) as eq1.
            pose proof (algebra_homo_zero f2) as eq2.
            cbn in *.
            unfold tensor_algebra_base in *.
            rewrite eq1, eq2.
            reflexivity.
        }
        rewrite ulist_image_add, ulist_sum_add.
        rewrite single_to_grade_sum_plus.
        do 2 rewrite algebra_homo_plus.
        rewrite IHl; clear IHl.
        apply rplus; clear l.
        destruct v as [v [α [[l l_eq] v_eq]]]; cbn; subst v.
        rewrite single_to_grade_sum_scalar.
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
                exists (vectors_to_power V (v :: list_end)).
                cbn.
                unfold vector_to_tensor.
                reflexivity.
            }
            assert (of_grade (list_size l) (power_to_tensor V (vectors_to_power V l)))
                as l_homo.
            {
                exists (vectors_to_power V l).
                reflexivity.
            }
            rewrite (tensor_mult_homo _ _ _ _ _ v_homo l_homo).
            rewrite (power_to_tensor_tm V).
            change (tensor_mult V (cring_module F) v 1) with
                (vectors_to_power V (v :: list_end)).
            change 1 with (list_size (v :: list_end)).
            rewrite (vectors_to_power_mult V).
            rewrite <- power_to_tensor_k_eq.
            cbn.
            reflexivity.
        }
        unfold power_to_tensor in eq.
        rewrite eq; clear eq.
        do 2 rewrite algebra_homo_mult.
        apply f_equal2; [>clear IHl|exact IHl].
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

(* begin hide *)
End TensorAlgebraObjCategory.

(* end hide *)
Arguments vector_to_tensor {F V}.
