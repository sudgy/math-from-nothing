Require Import init.

Require Export linear_grade.
Require Import linear_transformation_space.
Require Import linear_bilinear.

Require Import set.
Require Import unordered_list.

Section LinearExtend.

Context {U} {V1 V2 : Module U} {I : Type} `{GradedSpace U V1 I}.
Variable f_base : ∀ i : I, morphism (grade_modules i) V2.

Definition linear_extend_base (v : V1)
    := ulist_sum (ulist_image
        (λ i, f_base i ([grade_to v|] i)) (grades_list v)).

Let f := linear_extend_base.

Lemma linear_extend_sub : ∀ (v : V1) S (S_fin : simple_finite (set_type S)),
    grades_set v ⊆ S → f v = ulist_sum (ulist_image
        (λ i, f_base i ([grade_to v|] i)) (grade_set_to_list S_fin)).
Proof.
    intros v S S_fin sub.
    unfold f, linear_extend_base.
    assert (∃ l, grade_set_to_list S_fin = grades_list v + l ∧
        ulist_prop (λ x, ¬grades_set v x) l) as [l [l_eq l_nin]].
    {
        unfold grades_list, grade_set_to_list.
        rewrite_ex_val Sl [Sl_uni Sl_in].
        rewrite_ex_val vl [vl_uni vl_in].
        assert (∃ l, ulist_image set_value Sl = ulist_image set_value vl + l)
            as [l eq].
        {
            apply ulist_sub_ex.
            -   apply ulist_image_unique_inj; [>|exact vl_uni].
                split.
                intros a b.
                rewrite set_type_eq.
                trivial.
            -   intros x x_in.
                apply image_in_ulist in x_in as [[x' x'_in1] [x_eq x'_in2]].
                cbn in x_eq.
                subst x'.
                specialize (sub _ x'_in1).
                change x with [[x|sub]|].
                apply in_ulist_image.
                apply Sl_in.
        }
        exists l.
        split; [>exact eq|].
        apply ulist_prop_split.
        intros a l' l_eq a_in.
        subst l.
        specialize (vl_in [a|a_in]).
        apply in_ulist_split in vl_in as [l'' l_eq].
        subst vl.
        rewrite ulist_image_add in eq; cbn in eq.
        rewrite <- ulist_conc_single in eq.
        rewrite <- plus_assoc in eq.
        rewrite (plus_comm _ (a ː l')) in eq.
        rewrite ulist_conc_single in eq.
        rewrite ulist_conc_add in eq.
        assert (ulist_unique (ulist_image set_value Sl)) as Sl_uni'.
        {
            apply ulist_image_unique_inj; [>|exact Sl_uni].
            split.
            intros x y.
            rewrite set_type_eq.
            trivial.
        }
        rewrite eq in Sl_uni'.
        rewrite ulist_unique_add in Sl_uni'.
        rewrite in_ulist_add_eq in Sl_uni'.
        rewrite not_or in Sl_uni'.
        destruct Sl_uni' as [[neq]].
        contradiction.
    }
    rewrite l_eq.
    rewrite ulist_image_conc, ulist_sum_conc.
    rewrite <- plus_0_a_b_ba.
    clear - l_nin.
    ulist_prop_induction l l_nin as i i_nin IHl.
    -   rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    -   rewrite ulist_image_add, ulist_sum_add.
        rewrite <- IHl.
        rewrite plus_rid.
        unfold grades_set in i_nin.
        rewrite not_not in i_nin.
        unfold grade_project in i_nin.
        rewrite <- (module_homo_zero grade_from) in i_nin.
        apply inj in i_nin.
        apply set_type_eq in i_nin; cbn in i_nin.
        unfold sum_project_base in i_nin.
        pose proof (func_eq _ _ i_nin i) as eq.
        unfold zero at 1 in eq; cbn in eq.
        rewrite if_true in eq by reflexivity.
        rewrite <- eq.
        rewrite module_homo_zero.
        reflexivity.
Qed.

Theorem linear_extend_plus : ∀ u v, f (u + v) = f u + f v.
Proof.
    intros u v.
    pose (S := grades_set u ∪ grades_set v ∪ grades_set (u + v)).
    assert (grades_set u ⊆ S) as u_sub.
    {
        apply (trans (union_lsub _ (grades_set v))).
        apply union_lsub.
    }
    assert (grades_set v ⊆ S) as v_sub.
    {
        apply (trans (union_rsub (grades_set u) _)).
        apply union_lsub.
    }
    assert (grades_set (u + v) ⊆ S) as uv_sub.
    {
        apply union_rsub.
    }
    assert (simple_finite (set_type S)) as S_fin.
    {
        apply simple_finite_union.
        -   apply simple_finite_union.
            +   apply grades_set_finite.
            +   apply grades_set_finite.
        -   apply grades_set_finite.
    }
    rewrite (linear_extend_sub _ S S_fin u_sub).
    rewrite (linear_extend_sub _ S S_fin v_sub).
    rewrite (linear_extend_sub _ S S_fin uv_sub).
    remember (grade_set_to_list S_fin) as l.
    clear Heql.
    induction l as [|i l] using ulist_induction.
    {
        do 3 rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_lid.
        reflexivity.
    }
    do 3 rewrite ulist_image_add, ulist_sum_add.
    rewrite IHl.
    rewrite module_homo_plus.
    unfold plus at 2; cbn.
    rewrite module_homo_plus.
    apply plus_4.
Qed.

Theorem linear_extend_scalar : ∀ a v, f (a · v) = a · f v.
Proof.
    intros a v.
    pose (S := grades_set v ∪ grades_set (a · v)).
    assert (grades_set v ⊆ S) as v_sub.
    {
        apply union_lsub.
    }
    assert (grades_set (a · v) ⊆ S) as av_sub.
    {
        apply union_rsub.
    }
    assert (simple_finite (set_type S)) as S_fin.
    {
        apply simple_finite_union.
        -   apply grades_set_finite.
        -   apply grades_set_finite.
    }
    rewrite (linear_extend_sub _ S S_fin v_sub).
    rewrite (linear_extend_sub _ S S_fin av_sub).
    remember (grade_set_to_list S_fin) as l.
    clear Heql.
    induction l as [|i l] using ulist_induction.
    {
        do 2 rewrite ulist_image_end, ulist_sum_end.
        rewrite scalar_ranni.
        reflexivity.
    }
    do 2 rewrite ulist_image_add, ulist_sum_add.
    rewrite IHl.
    rewrite module_homo_scalar.
    unfold scalar_mult at 1; cbn.
    rewrite module_homo_scalar.
    rewrite scalar_ldist.
    reflexivity.
Qed.

Definition linear_extend := make_module_homomorphism U V1 V2
    linear_extend_base linear_extend_plus linear_extend_scalar.
Global Arguments linear_extend : simpl never.

Theorem linear_extend_homo : ∀ i v, of_grade i v →
    linear_extend v = f_base i ([grade_to v|] i).
Proof.
    intros i v iv.
    classic_case (0 = v) as [v_z|v_nz].
    -   subst v.
        do 3 rewrite module_homo_zero.
        reflexivity.
    -   unfold linear_extend; cbn.
        unfold linear_extend_base.
        rewrite (grades_list_homo v i v_nz iv).
        rewrite ulist_image_single, ulist_sum_add, ulist_sum_end.
        apply plus_rid.
Qed.

End LinearExtend.

Section BilinearExtend.

Context {U} {V1 V2 : Module U} {I : Type} `{GradedSpace U V1 I}.

Variable op : ∀ (i j : I), set_type (bilinear (U := U)
    (V1 := grade_modules i) (V2 := grade_modules j) (V3 := V2)).

Section BilinearBase.

Context i (a : grade_modules i).

Let f1_base := λ j v, [op i j|] a v.

Lemma bilinear_extend_base_plus :
    ∀ j u v, f1_base j (u + v) = f1_base j u + f1_base j v.
Proof.
    intros j u v.
    unfold f1_base.
    apply [|op i j].
Qed.

Lemma bilinear_extend_base_scalar :
    ∀ j a v, f1_base j (a · v) = a · f1_base j v.
Proof.
    intros j u v.
    unfold f1_base.
    apply [|op i j].
Qed.

Let f1 j := make_module_homomorphism _ _ _
    (f1_base j) (bilinear_extend_base_plus j) (bilinear_extend_base_scalar j).

Definition bilinear_extend_base := linear_extend f1.

End BilinearBase.

Let f_base := bilinear_extend_base :
    ∀ i, grade_modules i → (linear_trans_module V1 V2).

Lemma bilinear_extend_plus_base :
    ∀ i u v, f_base i (u + v) = f_base i u + f_base i v.
Proof.
    intros i u v.
    apply module_homomorphism_eq.
    intros x.
    induction x as [|a x IHx] using grade_induction.
    {
        do 2 rewrite module_homo_zero.
        reflexivity.
    }
    do 2 rewrite module_homo_plus.
    rewrite IHx; clear IHx.
    apply rplus; clear x.
    unfold plus at 2; cbn.
    unfold linear_trans_plus_base.
    unfold f_base, bilinear_extend_base.
    destruct a as [a [j aj]]; cbn.
    do 3 rewrite (linear_extend_homo _ _ _ aj).
    cbn.
    apply [|op i j].
Qed.

Lemma bilinear_extend_scalar_base : ∀ i a v, f_base i (a · v) = a · f_base i v.
Proof.
    intros i a v.
    apply module_homomorphism_eq.
    intros x.
    induction x as [|u x IHx] using grade_induction.
    {
        do 2 rewrite module_homo_zero.
        reflexivity.
    }
    do 2 rewrite module_homo_plus.
    rewrite IHx; clear IHx.
    apply rplus; clear x.
    unfold scalar_mult at 2; cbn.
    unfold linear_trans_scalar_base.
    unfold f_base, bilinear_extend_base.
    destruct u as [u [j uj]]; cbn.
    do 2 rewrite (linear_extend_homo _ _ _ uj).
    cbn.
    apply [|op i j].
Qed.

Definition f_base2 (i : I) := make_module_homomorphism _ _ _ (f_base i)
    (bilinear_extend_plus_base i) (bilinear_extend_scalar_base i).

Definition bilinear_extend (u v : V1) := linear_extend f_base2 u v.
Global Arguments bilinear_extend : simpl never.
Let f := bilinear_extend.

Theorem bilinear_extend_ldist : ∀ u v w, f u (v + w) = f u v + f u w.
Proof.
    intros u v w.
    unfold f, bilinear_extend.
    induction u as [|a u IHu] using grade_induction.
    {
        rewrite module_homo_zero.
        unfold zero; cbn.
        unfold linear_trans_zero_base.
        rewrite plus_lid.
        reflexivity.
    }
    apply module_homo_plus.
Qed.

Theorem bilinear_extend_rdist : ∀ u v w, f (u + v) w = f u w + f v w.
Proof.
    intros u v w.
    unfold f, bilinear_extend.
    rewrite module_homo_plus.
    reflexivity.
Qed.

Theorem bilinear_extend_lscalar : ∀ a u v, f (a · u) v = a · f u v.
Proof.
    intros a u v.
    unfold f, bilinear_extend.
    rewrite module_homo_scalar.
    reflexivity.
Qed.

Theorem bilinear_extend_rscalar : ∀ a u v, f u (a · v) = a · f u v.
Proof.
    intros a u v.

    unfold f, bilinear_extend.
    induction u as [|x u IHu] using grade_induction.
    {
        rewrite module_homo_zero.
        unfold zero; cbn.
        unfold linear_trans_zero_base.
        rewrite scalar_ranni.
        reflexivity.
    }
    apply module_homo_scalar.
Qed.
Theorem bilinear_extend_lanni : ∀ v, f 0 v = 0.
Proof.
    intros v.
    rewrite <- (scalar_lanni 0).
    rewrite bilinear_extend_lscalar.
    apply scalar_lanni.
Qed.

Theorem bilinear_extend_ranni : ∀ v, f v 0 = 0.
Proof.
    intros v.
    rewrite <- (scalar_lanni 0).
    rewrite bilinear_extend_rscalar.
    apply scalar_lanni.
Qed.

Theorem bilinear_extend_homo : ∀ i j u v, of_grade i u → of_grade j v →
    bilinear_extend u v = [op i j|] ([grade_to u|] i) ([grade_to v|] j).
Proof.
    intros i j u v iu jv.
    unfold bilinear_extend.
    rewrite (linear_extend_homo _ _ _ iu).
    unfold f_base2; cbn.
    unfold f_base, bilinear_extend_base.
    rewrite (linear_extend_homo _ _ _ jv); cbn.
    reflexivity.
Qed.

End BilinearExtend.
