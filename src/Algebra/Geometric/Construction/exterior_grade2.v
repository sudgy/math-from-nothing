
Require Import init.

Require Import geometric_universal.
Require Import exterior_grade1.
Require Import algebra_category.
Require Import category_initterm.
Require Import linear_grade.
Require Import linear_grade_sum.
Require Import linear_grade_isomorphism.
Require Import linear_extend.
Require Import linear_subspace.
Require Import linear_span.

Require Export nat.
Require Import unordered_list.

Section ExteriorGrade.

Context {U : CRingObj} (V : ModuleObj U).
Local Notation φ := (vector_to_ext V).
Local Notation σ := (scalar_to_ext V).

Let ι := make_module_homomorphism U V (algebra_module (ext_algebra_n V))
    (vector_to_ext_n V)
    (vector_to_ext_n_plus V)
    (vector_to_ext_n_scalar V).

Definition ext_n_to_ext := make_to_ext _ _ ι (vector_to_ext_n_alternating V).

Theorem ext_algebra_n_universal : @initial (TO_EXT V) ext_n_to_ext.
Proof.
    unfold ext_n_to_ext, initial; cbn.
    intros [A g g_alt].
    unfold to_ext_set; cbn.
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        pose proof (exterior_universal V (make_to_ext _ _ g g_alt)) as h_ex.
        apply ex_singleton in h_ex as [h1 h1_eq].
        cbn in h1.
        unfold to_ext_set in h1_eq; cbn in h1_eq.
        pose (ENG := ext_n_grade V).
        pose (h2 (i : nat) (a : ext_algebra_n V)
            (H : of_grade i a) := h1 [ex_val H|]).
        assert (linear_extend_plus_base (VG := ENG) h2) as h2_plus.
        {
            intros u' v' i iu iv.
            unfold h2.
            rewrite_ex_val uv uv_eq.
            rewrite_ex_val u u_eq.
            rewrite_ex_val v v_eq.
            rewrite <- algebra_homo_plus.
            apply f_equal.
            subst u' v'.
            rewrite <- to_ext_n_plus in uv_eq.
            apply single_to_grade_sum_eq in uv_eq.
            rewrite uv_eq.
            reflexivity.
        }
        assert (linear_extend_scalar_base (VG := ENG) h2) as h2_scalar.
        {
            intros a v' i iv.
            unfold h2.
            rewrite_ex_val av av_eq.
            rewrite_ex_val v v_eq.
            rewrite <- algebra_homo_scalar.
            apply f_equal.
            subst v'.
            rewrite <- to_ext_n_scalar in av_eq.
            apply single_to_grade_sum_eq in av_eq.
            rewrite av_eq.
            reflexivity.
        }
        pose (h3 := linear_extend (VG := ENG) h2 : ext_algebra_n V → A).
        assert (∀ u v, h3 (u + v) = h3 u + h3 v) as h3_plus.
        {
            apply (linear_extend_plus _ h2_plus h2_scalar).
        }
        assert (∀ a v, h3 (a · v) = a · h3 v) as h3_scalar.
        {
            apply (linear_extend_scalar _ h2_plus h2_scalar).
        }
        assert (h3 0 = 0) as h3_zero.
        {
            rewrite <- (scalar_lanni 0).
            rewrite h3_scalar.
            apply scalar_lanni.
        }
        assert (∀ u v, h3 (u * v) = h3 u * h3 v) as h3_mult.
        {
            intros u v.
            induction u as [|u u' i iu iu' IHu]
                using (grade_induction (VG := ENG)).
            {
                rewrite h3_zero.
                do 2 rewrite mult_lanni.
                exact h3_zero.
            }
            rewrite rdist.
            do 2 rewrite h3_plus.
            rewrite rdist.
            rewrite IHu.
            apply rplus.
            clear u' iu' IHu.
            induction v as [|v v' j jv jv' IHv]
                using (grade_induction (VG := ENG)).
            {
                rewrite h3_zero.
                do 2 rewrite mult_ranni.
                exact h3_zero.
            }
            rewrite ldist.
            do 2 rewrite h3_plus.
            rewrite ldist.
            rewrite IHv.
            apply rplus.
            clear v' jv' IHv.
            destruct iu as [u' u_eq]; subst u.
            destruct jv as [v' v_eq]; subst v.
            change (single_to_grade_sum nat (ext_n_module V) u')
                with (to_ext_n V u').
            change (single_to_grade_sum nat (ext_n_module V) v')
                with (to_ext_n V v').
            destruct u' as [u u_in], v' as [v v_in].
            rewrite to_ext_n_mult.
            unfold h3.
            assert (∀ {i x} (H : subspace_set (ext_n_subspace V i) x),
                of_grade i (to_ext_n V [x|H])) as n_grade.
            {
                intros a x H.
                exists [x | H].
                reflexivity.
            }
            do 3 rewrite (linear_extend_homo _ h2_scalar _ _ (n_grade _ _ _)).
            unfold h2.
            rewrite_ex_val uv uv_eq.
            rewrite_ex_val u' u'_eq.
            rewrite_ex_val v' v'_eq.
            apply single_to_grade_sum_eq in uv_eq, u'_eq, v'_eq.
            subst uv u' v'; cbn.
            apply algebra_homo_mult.
        }
        assert (h3 1 = 1) as h3_one.
        {
            unfold h3.
            assert (of_grade 0 (one (U := ext_algebra_n V))) as o1.
            {
                exists [_|ext_n_one_in V].
                reflexivity.
            }
            rewrite (linear_extend_homo _ h2_scalar _ _ o1).
            unfold h2.
            rewrite_ex_val o o_eq.
            apply single_to_grade_sum_eq in o_eq.
            subst o; cbn.
            apply algebra_homo_one.
        }
        exists (make_algebra_homomorphism _ _ _
            h3 h3_plus h3_scalar h3_mult h3_one).
        intros x.
        cbn.
        unfold h3.
        assert (of_grade 1 (vector_to_ext_n V x)) as x1.
        {
            exists [_|vector_to_ext_n_in V x].
            reflexivity.
        }
        rewrite (linear_extend_homo _ h2_scalar _ _ x1).
        unfold h2.
        rewrite_ex_val x' x'_eq.
        apply single_to_grade_sum_eq in x'_eq.
        subst x'; cbn.
        apply h1_eq.
    -   intros [f1 f1_eq] [f2 f2_eq].
        apply set_type_eq; cbn.
        apply algebra_homomorphism_eq.
        intros v.
        pose proof (ext_n_sum V v) as [l v_eq]; subst v.
        induction l as [|[a l] l'] using ulist_induction.
        {
            rewrite ulist_image_end, ulist_sum_end.
            do 2 rewrite algebra_homo_zero.
            reflexivity.
        }
        rewrite ulist_image_add, ulist_sum_add; cbn.
        do 2 rewrite algebra_homo_plus.
        rewrite IHl'.
        apply rplus.
        clear l' IHl'.
        do 2 rewrite algebra_homo_scalar.
        apply f_equal.
        clear a.
        induction l as [|a l].
        {
            rewrite list_image_end; cbn.
            do 2 rewrite algebra_homo_one.
            reflexivity.
        }
        rewrite list_image_add; cbn.
        do 2 rewrite algebra_homo_mult.
        rewrite IHl.
        apply rmult.
        clear l IHl.
        rewrite f1_eq, f2_eq.
        reflexivity.
Qed.

Lemma ext_algebra_iso_ex :
    ∃ f : cat_morphism (ext_algebra_n V) (exterior_algebra V),
        isomorphism f ∧
        ∀ x, f (vector_to_ext_n V x) = φ x.
Proof.
    pose proof (initial_unique _ _
        ext_algebra_n_universal (exterior_universal V))
        as [[f f_eq] [[g g_eq] [fg gf]]].
    cbn in *.
    unfold to_ext_set in *; cbn in *.
    change (ex_type_val (ex_to_type (_))) with (to_ext_algebra V) in *.
    inversion fg as [eq1]; clear fg.
    inversion gf as [eq2]; clear gf.
    exists f.
    split.
    -   exists g.
        split.
        +   apply algebra_homomorphism_eq.
            apply (func_eq _ _ eq1).
        +   apply algebra_homomorphism_eq.
            apply (func_eq _ _ eq2).
    -   exact f_eq.
Qed.

Let f := ex_val ext_algebra_iso_ex.
Let f_iso := land (ex_proof ext_algebra_iso_ex).
Let g := ex_val f_iso.
Lemma ext_algebra_iso_eq : ∀ x, f (vector_to_ext_n V x) = φ x.
Proof.
    apply (ex_proof ext_algebra_iso_ex).
Qed.
Lemma ext_algebra_iso_fg : ∀ x, f (g x) = x.
Proof.
    intros x.
    pose proof (ex_proof f_iso) as [eq1 eq2]; clear eq2.
    inversion eq1 as [eq1'].
    apply (func_eq _ _ eq1').
Qed.
Lemma ext_algebra_iso_gf : ∀ x, g (f x) = x.
Proof.
    intros x.
    pose proof (ex_proof f_iso) as [eq1 eq2]; clear eq1.
    inversion eq2 as [eq2'].
    apply (func_eq _ _ eq2').
Qed.

Let TAG := ext_n_grade V.
Let TAGM := ext_n_grade_mult V.
Existing Instances TAG TAGM.

Definition exterior_grade := grade_isomorphism
    (algebra_to_module_homomorphism f)
    (algebra_to_module_iso f f_iso).
Definition exterior_grade_mult := graded_algebra_isomorphism f f_iso.

Existing Instances exterior_grade exterior_grade_mult.

Theorem scalar_to_exterior_grade : ∀ a, of_grade (H9 := exterior_grade) 0 (σ a).
Proof.
    intros a.
    unfold of_grade; cbn.
    exists (a · (@one _ (algebra_one (ext_algebra_n V)))).
    cbn.
    split.
    -   pose (o := [1|ext_n_one_in V] : module_V (ext_n_module V 0)).
        exists (a · o).
        unfold o.
        rewrite single_to_grade_sum_scalar.
        reflexivity.
    -   rewrite algebra_homo_scalar.
        rewrite algebra_homo_one.
        reflexivity.
Qed.

Theorem exterior_grade_zero_scalar : ∀ v, of_grade 0 v ↔ (∃ a, v = σ a).
Proof.
    intros v.
    split.
    -   intros [v' [v_zero v_eq]]; subst v.
        pose proof (ext_n_sum_grade V _ v_zero) as [l v'_eq]; subst v'.
        clear v_zero.
        induction l as [|[a v] l] using ulist_induction.
        {
            rewrite ulist_image_end, ulist_sum_end.
            exists 0.
            rewrite module_homo_zero.
            rewrite scalar_to_ext_zero.
            reflexivity.
        }
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite algebra_homo_plus.
        destruct IHl as [b IHl].
        exists (a + b).
        cbn in IHl.
        rewrite IHl.
        rewrite scalar_to_ext_plus.
        apply rplus.
        clear l b IHl.
        destruct v as [v v_in].
        destruct v_in as [l [v_in v_size]]; subst v.
        cbn.
        rewrite algebra_homo_scalar.
        unfold scalar_to_ext, scalar_to_geo.
        apply f_equal.
        destruct l; [>|inversion v_size].
        unfold list_image; cbn.
        rewrite (proof_irrelevance _ (ext_n_one_in V)).
        apply algebra_homo_one.
    -   intros [a v_eq]; subst v.
        apply scalar_to_exterior_grade.
Qed.

Theorem vector_to_exterior_grade : ∀ v, of_grade 1 (φ v).
Proof.
    intros v.
    unfold of_grade; cbn.
    exists (vector_to_ext_n V v).
    cbn.
    split.
    -   exists [φ v| vector_to_ext_n_in V v].
        reflexivity.
    -   apply ext_algebra_iso_eq.
Qed.

Theorem exterior_grade_one_vector : ∀ v, of_grade 1 v ↔ (∃ a, v = φ a).
Proof.
    intros v.
    split.
    -   intros [v' [v_one v_eq]]; subst v.
        pose proof (ext_n_sum_grade V _ v_one) as [l v'_eq]; subst v'.
        clear v_one.
        induction l as [|[a v] l] using ulist_induction.
        {
            rewrite ulist_image_end, ulist_sum_end.
            exists 0.
            rewrite module_homo_zero.
            symmetry.
            apply module_homo_zero.
        }
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite algebra_homo_plus.
        destruct IHl as [u IHl].
        destruct v as [v v_in].
        destruct v_in as [l' [v_in v_size]]; subst v.
        destruct l' as [|v l']; [>inversion v_size|].
        destruct l'; [>|inversion v_size].
        cbn.
        exists (a · v + u).
        cbn in IHl.
        rewrite IHl.
        rewrite module_homo_plus.
        apply rplus.
        clear l u IHl.
        rewrite algebra_homo_scalar.
        rewrite module_homo_scalar.
        apply f_equal.
        unfold list_image; cbn.
        pose proof (vector_to_ext_n_in V v) as v_in.
        rewrite <- mult_rid in v_in.
        rewrite (proof_irrelevance _ v_in).
        assert ([φ v * 1 | v_in] =
            [φ v | vector_to_ext_n_in V v]) as eq.
        {
            apply set_type_eq; cbn.
            apply mult_rid.
        }
        rewrite eq.
        apply ext_algebra_iso_eq.
    -   intros [a v_eq]; subst v.
        apply vector_to_exterior_grade.
Qed.

Theorem ext_list_grade : ∀ l,
    of_grade (H9 := exterior_grade) (list_size l)
    (list_prod (list_image (vector_to_ext V) l)).
Proof.
    intros l.
    induction l as [|v l].
    {
        rewrite list_size_end.
        rewrite list_image_end, list_prod_end.
        rewrite <- scalar_id.
        apply scalar_to_exterior_grade.
    }
    rewrite list_size_add.
    rewrite list_image_add, list_prod_add.
    change (nat_suc (list_size l)) with (1 + list_size l).
    apply (of_grade_mult (VG := exterior_grade)).
    -   apply vector_to_exterior_grade.
    -   exact IHl.
Qed.

Theorem ext_grade_sum : ∀ x (i : nat), of_grade (H9 := exterior_grade) i x →
    ∃ l : ulist (U * set_type (λ l : list V, list_size l = i)),
    ulist_sum (ulist_image
        (λ x, fst x · list_prod (list_image φ [snd x|])) l) = x.
Proof.
    intros x' i [x [x_in x_eq]]; subst x'.
    pose proof (ext_n_sum_grade V x x_in) as [l l_eq].
    subst x; clear x_in.
    assert (∀ x : set_type (ext_n_base V i), list_size (ex_val [|x]) = i)
        as size_eq.
    {
        clear l.
        intros x.
        rewrite_ex_val l [x_eq l_size].
        exact l_size.
    }
    exists (ulist_image (λ x, (fst x, [_|size_eq (snd x)])) l).
    rewrite ulist_image_comp; cbn.
    induction l as [|[a v] l] using ulist_induction.
    {
        do 2 rewrite ulist_image_end, ulist_sum_end.
        symmetry.
        apply (algebra_homo_zero f).
    }
    do 2 rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite algebra_homo_plus.
    rewrite IHl.
    apply rplus.
    clear l IHl.
    rewrite (algebra_homo_scalar _ _ f).
    apply f_equal.
    destruct v as [v v_in].
    rewrite_ex_val l [v_eq l_size].
    cbn in v_eq.
    subst v; cbn.
    subst i.
    rewrite (proof_irrelevance _ (ext_n_list_in V l)).
    clear a v_in size_eq.
    induction l as [|v l].
    {
        unfold list_image; cbn.
        rewrite (proof_irrelevance _ (ext_n_one_in V)).
        symmetry; apply algebra_homo_one.
    }
    rewrite list_image_add at 1.
    rewrite list_prod_add at 1.
    rewrite IHl at 1; clear IHl.
    pose proof (vector_to_ext_n_in V v) as v_in.
    pose proof (ext_n_list_in V l) as l_in.
    rewrite (proof_irrelevance _(ext_n_algebra_mult_in V _ _ _ _ v_in l_in)).
    rewrite <- (to_ext_n_mult V _ _ _ _ v_in l_in).
    rewrite algebra_homo_mult.
    rewrite (proof_irrelevance _ (vector_to_ext_n_in V v)).
    rewrite (ext_algebra_iso_eq v).
    do 4 apply f_equal.
    apply proof_irrelevance.
Qed.

End ExteriorGrade.
