Require Import init.

Require Import module_category.
Require Import algebra_category.
Require Import linear_grade.
Require Import linear_subspace.
Require Import tensor_algebra.

Require Import nat.
Require Import set.
Require Import unordered_list.
Require Import ring_ideal.

Require Export exterior_construct.

(* begin hide *)
Section ExteriorGrade.

Local Arguments grade_subspace : simpl never.

(* end hide *)
Context {F : CRingObj} (V : ModuleObj F).

(* begin hide *)
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UO := cring_one F.

Existing Instances UP UZ UN UPC UPZ UPN UO.

Let EP := ext_plus V.
Let EZ := ext_zero V.
Let EN := ext_neg V.
Let EPC := ext_plus_comm V.
Let EPA := ext_plus_assoc V.
Let EPZ := ext_plus_lid V.
Let EPN := ext_plus_linv V.
Let EM := ext_mult V.
Let EO := ext_one V.
Let ESM := ext_scalar V.

Existing Instances EP EZ EN EPC EPA EPZ EPN EM EO ESM.

Let TP := algebra_plus (tensor_algebra V).
Let TZ := algebra_zero (tensor_algebra V).
Let TN := algebra_neg (tensor_algebra V).
Let TPA := algebra_plus_assoc (tensor_algebra V).
Let TPC := algebra_plus_comm (tensor_algebra V).
Let TPZ := algebra_plus_lid (tensor_algebra V).
Let TPN := algebra_plus_linv (tensor_algebra V).
Let TSM := algebra_scalar (tensor_algebra V).
Let TSMO := algebra_scalar_id (tensor_algebra V).
Let TSML := algebra_scalar_ldist (tensor_algebra V).
Let TSMR := algebra_scalar_rdist (tensor_algebra V).
Let TM := algebra_mult (tensor_algebra V).
Let TMO := algebra_one (tensor_algebra V).
Let TL := algebra_ldist (tensor_algebra V).
Let TR := algebra_rdist (tensor_algebra V).
Let TML := algebra_mult_lid (tensor_algebra V).
Let TMR := algebra_mult_rid (tensor_algebra V).

Existing Instances TP TZ TN TPA TPC TPZ TPN TSM TSMO TSML TSMR TM TMO TL TR TML TMR.

Let TG := tensor_grade V.
Let TAG := tensor_grade_mult V.

Existing Instances TG TAG.

(* end hide *)
Definition ext_grade_set n (v : ext V)
    := ∃ v', tensor_to_ext V v' = v ∧ of_grade (H9 := TG) n v'.

Lemma ext_grade_zero : ∀ n, ext_grade_set n 0.
Proof.
    intros n.
    exists 0.
    split.
    -   apply tensor_to_ext_zero.
    -   apply of_grade_zero.
Qed.

Lemma ext_grade_plus : ∀ n u v,
    ext_grade_set n u → ext_grade_set n v → ext_grade_set n (u + v).
Proof.
    intros n u v [u' [u_eq nu]] [v' [v_eq nv]].
    subst u v.
    exists (u' + v').
    split.
    -   apply tensor_to_ext_plus.
    -   apply of_grade_plus; assumption.
Qed.

Lemma ext_grade_scalar : ∀ n a v, ext_grade_set n v → ext_grade_set n (a · v).
Proof.
    intros n a v [v' [v_eq nv]]; subst v.
    exists (a · v').
    split.
    -   apply tensor_to_ext_scalar.
    -   apply of_grade_scalar.
        exact nv.
Qed.

Definition ext_grade n := make_subspace
    (ext_grade_set n)
    (ext_grade_zero n)
    (ext_grade_plus n)
    (ext_grade_scalar n).

Program Instance exterior_grade : GradedSpace (cring_U F) (ext V) := {
    grade_I := nat;
    grade_subspace n := ext_grade n;
}.
Next Obligation.
    rename H into neq.
    rename H0 into iv.
    rename H1 into jv.
    destruct iv as [v' [v'_eq iv]].
    destruct jv as [v'' [v''_eq jv]].
    rewrite <- v''_eq.
    rewrite <- v''_eq in v'_eq.
    clear v v''_eq.
    rewrite <- plus_0_anb_a_b in v'_eq.
    rewrite <- (tensor_to_ext_neg V) in v'_eq.
    rewrite <- (tensor_to_ext_plus V) in v'_eq.
    unfold tensor_to_ext, zero in v'_eq; equiv_simpl in v'_eq.
    apply equiv_eq in v'_eq; cbn in v'_eq.
    rewrite plus_lid in v'_eq.
    rewrite neg_plus, neg_neg in v'_eq.
    destruct v'_eq as [l l_eq].
    apply (f_equal (λ x, grade_project (VG := TG) x j)) in l_eq.
    rewrite grade_project_plus in l_eq.
    rewrite (grade_project_of_grade _ _ jv) in l_eq.
    rewrite grade_project_neg in l_eq.
    rewrite (grade_project_of_grade_neq _ _ _ iv neq) in l_eq.
    rewrite neg_zero, plus_lid in l_eq.
    rewrite l_eq; clear l_eq iv jv v' v'' neq i.
    induction l using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite grade_project_zero.
        symmetry; apply tensor_to_ext_zero.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite grade_project_plus.
    rewrite (tensor_to_ext_plus V).
    rewrite <- IHl; clear IHl l.
    rewrite plus_rid.
    destruct a as [[a1 a2] [a3 [v a3_eq]]]; subst a3; cbn.
    induction a1 as [|a11 a12 i a12i i_z] using grade_induction.
    {
        do 2 rewrite mult_lanni.
        rewrite grade_project_zero.
        symmetry; apply tensor_to_ext_zero.
    }
    do 2 rewrite rdist.
    rewrite grade_project_plus.
    rewrite (tensor_to_ext_plus V).
    rewrite <- IHa1; clear i_z IHa1.
    rewrite plus_rid.
    induction a2 as [|a21 a22 k a22k k_z] using grade_induction.
    {
        rewrite mult_ranni.
        rewrite grade_project_zero.
        symmetry; apply tensor_to_ext_zero.
    }
    rewrite ldist.
    rewrite grade_project_plus.
    rewrite (tensor_to_ext_plus V).
    rewrite <- IHa2; clear k_z IHa2.
    rewrite plus_rid.
    assert (of_grade (i + 2 + k)
        (a11 * (vector_to_tensor v * vector_to_tensor v) * a21)) as a_grade.
    {
        apply of_grade_mult; [>|exact a22k].
        apply of_grade_mult; [>exact a12i|].
        apply of_grade_mult; apply vector_to_tensor_grade.
    }
    classic_case (i + 2 + k = j) as [j_eq|j_neq].
    -   rewrite j_eq in a_grade.
        rewrite (grade_project_of_grade _ _ a_grade).
        unfold tensor_to_ext, zero; equiv_simpl.
        symmetry; apply equiv_eq; cbn.
        rewrite neg_zero, plus_rid.
        assert (ext_ideal_base V (vector_to_tensor v * vector_to_tensor v))
            as v2_in by (exists v; reflexivity).
        exists (((a11, a21), [_|v2_in]) ::: ulist_end).
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid.
        reflexivity.
    -   rewrite (grade_project_of_grade_neq _ _ _ a_grade j_neq).
        symmetry; apply tensor_to_ext_zero.
Qed.
Next Obligation.
    equiv_get_value v.
    change (to_equiv (ring_ideal.ideal_equiv (ext_ideal V)) v)
        with (tensor_to_ext V v).
    pose proof (grade_decompose_ex v) as [l [l_eq l_in]].
    pose (ST := SubspaceVector (cring_U F) (algebra_V (tensor_algebra V))).
    (* TODO: Make this and the definiiton of ext_grade_set fuse somehow *)
    pose (ext_subset (S : ST) := λ x : ext V,
        ∃ x', tensor_to_ext V x' = x ∧ subspace_set (sub_vector_sub S) x').
    assert (ext_sub_zero : ∀ S, ext_subset S 0).
    {
        intros S.
        exists 0.
        split.
        -   apply tensor_to_ext_zero.
        -   apply subspace_zero.
    }
    assert (ext_sub_plus : ∀ S, ∀ u v,
        ext_subset S u → ext_subset S v → ext_subset S (u + v)).
    {
        clear v l_eq.
        intros S u v [u' [u_eq u'_in]] [v' [v_eq v'_in]]; subst u v.
        exists (u' + v').
        split.
        -   apply tensor_to_ext_plus.
        -   apply subspace_plus; assumption.
    }
    assert (ext_sub_scalar : ∀ S, ∀ a v, ext_subset S v → ext_subset S (a · v)).
    {
        intros S a u [u' [u_eq u'_in]]; subst u.
        exists (a · u').
        split.
        -   apply tensor_to_ext_scalar.
        -   apply subspace_scalar.
            exact u'_in.
    }
    pose (ext_sub S := make_subspace
        (ext_subset S)
        (ext_sub_zero S)
        (ext_sub_plus S)
        (ext_sub_scalar S)).
    assert (S_in : ∀ S, ext_subset S (tensor_to_ext V (sub_vector_v S))).
    {
        intros [S u Su]; cbn.
        exists u; cbn.
        split.
        -   reflexivity.
        -   exact Su.
    }
    pose (f S := make_subspace_vector (ext_sub S) _ (S_in S)).
    exists (ulist_image l f).
    split.
    -   rewrite ulist_image_comp.
        unfold f; cbn.
        clear l_in ST ext_subset ext_sub_zero ext_sub_plus ext_sub_scalar
            ext_sub S_in f.
        subst v.
        induction l using ulist_induction.
        +   do 2 rewrite ulist_image_end, ulist_sum_end.
            apply tensor_to_ext_zero.
        +   do 2 rewrite ulist_image_add, ulist_sum_add.
            rewrite <- IHl; clear IHl.
            apply tensor_to_ext_plus.
    -   clear l_eq.
        induction l using ulist_induction.
        +   rewrite ulist_image_end.
            apply ulist_prop_end.
        +   rewrite ulist_image_add, ulist_prop_add.
            apply ulist_prop_add in l_in as [a_in l_in].
            split; [>clear l_in IHl|exact (IHl l_in)].
            unfold f; cbn.
            destruct a_in as [i a_in].
            exists i.
            apply predicate_ext.
            intros x; split; intros [x' [x_eq x'_in]]; subst x.
            *   exists x'.
                split.
                --  reflexivity.
                --  rewrite <- a_in.
                    exact x'_in.
            *   exists x'.
                split.
                --  reflexivity.
                --  rewrite <- a_in in x'_in.
                    exact x'_in.
Qed.
Next Obligation.
    rename H into l_in, H0 into l_uni, H1 into l_z.
    assert (∀ i (l : ulist (algebra_V (tensor_algebra V) * algebra_V
        (tensor_algebra V) * set_type (ext_ideal_base V))),
        tensor_to_ext V (grade_project (ulist_sum (ulist_image l
            (λ p, fst (fst p) * [snd p|] * snd (fst p)))) i) = 0) as lem.
    {
        clear l l_in l_uni l_z.
        intros i l.
        induction l using ulist_induction.
        -   rewrite ulist_image_end, ulist_sum_end.
            rewrite grade_project_zero.
            apply tensor_to_ext_zero.
        -   rewrite ulist_image_add, ulist_sum_add.
            rewrite grade_project_plus.
            rewrite (tensor_to_ext_plus V).
            rewrite IHl; clear IHl l.
            rewrite plus_rid.
            destruct a as [[a1 a2] [a3 a3_in]]; cbn.
            induction a1 as [|a1 a1' j a1j a1'j] using grade_induction.
            {
                do 2 rewrite mult_lanni.
                rewrite grade_project_zero.
                apply tensor_to_ext_zero.
            }
            do 2 rewrite rdist.
            rewrite grade_project_plus, (tensor_to_ext_plus V).
            rewrite IHa1; clear IHa1 a1' a1'j.
            rewrite plus_rid.
            induction a2 as [|a2 a2' k a2k a2'k] using grade_induction.
            {
                rewrite mult_ranni.
                rewrite grade_project_zero.
                apply tensor_to_ext_zero.
            }
            rewrite ldist.
            rewrite grade_project_plus, (tensor_to_ext_plus V).
            rewrite IHa2; clear IHa2 a2' a2'k.
            rewrite plus_rid.
            assert (of_grade (j + 2 + k) (a1 * a3 * a2)) as a_grade.
            {
                apply grade_mult; [>|exact a2k].
                apply grade_mult; [>exact a1j|].
                destruct a3_in as [v a3_eq].
                subst a3.
                apply grade_mult; apply vector_to_tensor_grade.
            }
            classic_case (j + 2 + k = i) as [eq|neq].
            +   rewrite eq in a_grade.
                rewrite (grade_project_of_grade _ _ a_grade).
                unfold tensor_to_ext, zero; equiv_simpl.
                apply equiv_eq; cbn.
                rewrite neg_zero, plus_rid.
                exists (((a1, a2), [a3|a3_in]) ::: ulist_end).
                rewrite ulist_image_add, ulist_sum_add; cbn.
                rewrite ulist_image_end, ulist_sum_end.
                rewrite plus_rid.
                reflexivity.
            +   rewrite (grade_project_of_grade_neq _ _ _ a_grade neq).
                apply tensor_to_ext_zero.
    }
    apply ulist_prop_split.
    intros [A v Av] l' l_eq; cbn in *.
    subst l; rename l' into l.
    rewrite ulist_image_add, ulist_sum_add in l_z; cbn in l_z.
    rewrite ulist_image_add, ulist_unique_add in l_uni; cbn in l_uni.
    destruct l_uni as [A_nin l_uni]; clear l_uni.
    apply ulist_prop_add in l_in as [[i Ai] l_in]; cbn in *.
    pose proof Av as Av'.
    rewrite <- Ai in Av'.
    destruct Av' as [v' [v'_eq v'i]].
    subst v.
    assert (∃ lv, tensor_to_ext V (lv - grade_project lv i) =
        ulist_sum (ulist_image l sub_vector_v)) as [lv lv_eq].
    {
        clear v' l_z v'i Av.
        pose (l' := ulist_image l (λ x, from_equiv (sub_vector_v x))).
        assert (ulist_sum (ulist_image l sub_vector_v) =
            tensor_to_ext V (ulist_sum l')) as l_eq.
        {
            unfold l'.
            clear l' l_in A A_nin i Ai.
            induction l using ulist_induction.
            -   do 2 rewrite ulist_image_end, ulist_sum_end.
                symmetry; apply tensor_to_ext_zero.
            -   do 2 rewrite ulist_image_add, ulist_sum_add.
                rewrite (tensor_to_ext_plus V).
                rewrite <- IHl; clear IHl.
                apply rplus; clear l.
                destruct a as [a_sub a]; cbn.
                unfold tensor_to_ext.
                rewrite from_equiv_eq.
                reflexivity.
        }
        exists (ulist_sum l').
        rewrite (tensor_to_ext_plus V).
        rewrite l_eq.
        apply plus_0_a_ba_b.
        rewrite (tensor_to_ext_neg V).
        rewrite <- neg_zero.
        apply f_equal.
        unfold l'.
        clear l_eq l'.
        induction l using ulist_induction.
        -   rewrite ulist_image_end, ulist_sum_end.
            rewrite grade_project_zero.
            symmetry; apply tensor_to_ext_zero.
        -   rewrite ulist_image_add, in_ulist_add in A_nin.
            rewrite not_or in A_nin.
            destruct A_nin as [Aa A_nin].
            rewrite ulist_prop_add in l_in.
            destruct l_in as [a_in l_in].
            specialize (IHl A_nin l_in).
            clear A_nin l_in.
            rewrite ulist_image_add, ulist_sum_add.
            rewrite grade_project_plus.
            rewrite (tensor_to_ext_plus V).
            rewrite <- IHl; clear IHl.
            rewrite plus_rid.
            assert (∃ v, v = from_equiv (sub_vector_v a) ∧
                tensor_to_ext V v = sub_vector_v a) as [v [v_eq1 v_eq2]].
            {
                exists (from_equiv (sub_vector_v a)).
                split; [>reflexivity|].
                unfold tensor_to_ext.
                apply from_equiv_eq.
            }
            rewrite <- v_eq1; clear v_eq1.
            destruct a_in as [j aj].
            destruct a as [B b Bb]; cbn in *.
            rename Aa into AB, aj into Bj.
            subst b.
            pose proof Bb as Bb'.
            rewrite <- Bj in Bb'.
            destruct Bb' as [v' [v'_eq v'j]].
            classic_case (i = j) as [eq|neq].
            {
                subst.
                rewrite <- Ai, <- Bj in AB.
                contradiction.
            }
            symmetry in v'_eq.
            unfold tensor_to_ext in v'_eq; equiv_simpl in v'_eq.
            apply equiv_eq in v'_eq; cbn in v'_eq.
            clear l.
            destruct v'_eq as [l l_eq].
            rewrite <- plus_rrmove in l_eq.
            rewrite l_eq; clear l_eq.
            rewrite grade_project_plus.
            rewrite neq_sym in neq.
            rewrite (grade_project_of_grade_neq _ _ _ v'j neq).
            rewrite plus_rid.
            clear neq v'j v' Bj Ai j AB Bb v A B.
            symmetry; apply lem.
    }
    rewrite <- lv_eq in l_z.
    unfold plus at 1, zero, tensor_to_ext in l_z; equiv_simpl in l_z.
    symmetry in l_z.
    apply equiv_eq in l_z; cbn in l_z.
    rewrite neg_zero, plus_rid in l_z.
    destruct l_z as [vl vl_eq].
    apply (f_equal (λ x, grade_project (VG := TG) x i)) in vl_eq.
    rewrite grade_project_plus in vl_eq.
    rewrite (grade_project_of_grade _ _ v'i) in vl_eq.
    rewrite grade_project_plus in vl_eq.
    rewrite grade_project_neg in vl_eq.
    rewrite grade_project_project in vl_eq.
    rewrite plus_rinv, plus_rid in vl_eq.
    clear lv lv_eq.
    rewrite vl_eq.
    clear vl_eq A_nin Ai l_in v'i.
    symmetry; apply lem.
Qed.

Program Instance exterior_grade_mult : GradedAlgebraObj (cring_U F) (ext V).
Next Obligation.
    destruct H as [u' [u_eq u'i]].
    destruct H0 as [v' [v_eq v'j]].
    subst u v.
    exists (u' * v').
    split.
    -   apply tensor_to_ext_mult.
    -   apply (grade_mult (GradedAlgebraObj := TAG)); assumption.
Qed.

Theorem scalar_to_ext_grade : ∀ a, of_grade 0 (scalar_to_ext V a).
Proof.
    intros a.
    exists (scalar_to_tensor V a).
    split.
    -   reflexivity.
    -   apply scalar_to_tensor_grade.
Qed.

Theorem ext_grade_zero_scalar : ∀ v : ext V,
    of_grade 0 v ↔ (∃ a, v = scalar_to_ext V a).
Proof.
    intros v.
    split.
    -   intros [v' [v_eq v0]].
        subst v.
        apply tensor_grade_zero_scalar in v0 as [a v'_eq].
        subst v'.
        exists a.
        reflexivity.
    -   intros [a v_eq]; subst v.
        apply scalar_to_ext_grade.
Qed.

Theorem vector_to_ext_grade : ∀ a, of_grade 1 (vector_to_ext V a).
Proof.
    intros a.
    exists (vector_to_tensor a).
    split.
    -   reflexivity.
    -   apply vector_to_tensor_grade.
Qed.

Theorem ext_grade_one_vector : ∀ v : ext V,
    of_grade 1 v ↔ (∃ a, v = vector_to_ext V a).
Proof.
    intros v.
    split.
    -   intros [v' [v_eq v0]].
        subst v.
        apply tensor_grade_one_vector in v0 as [a v'_eq].
        subst v'.
        exists a.
        reflexivity.
    -   intros [a v_eq]; subst v.
        apply vector_to_ext_grade.
Qed.

Theorem ext_list_grade : ∀ l,
    of_grade (H9 := exterior_grade) (list_size l)
    (list_prod (list_image (vector_to_ext V) l)).
Proof.
    intros l.
    induction l.
    -   rewrite list_image_end.
        cbn.
        rewrite <- scalar_to_ext_one.
        apply scalar_to_ext_grade.
    -   rewrite list_image_add.
        cbn.
        change (nat_suc (list_size l)) with (1 + list_size l).
        apply (grade_mult (GradedAlgebraObj := exterior_grade_mult)).
        +   apply vector_to_ext_grade.
        +   exact IHl.
Qed.

Theorem ext_grade_sum : ∀ (v : ext V) n, of_grade n v →
    ∃ l : ulist (cring_U F * set_type (λ l', list_size l' = n)),
        v = ulist_sum (ulist_image l
        (λ p, fst p · list_prod (list_image (vector_to_ext V) [snd p|]))).
Proof.
    intros v' n nv.
    destruct nv as [v [v_eq nv]]; subst v'.
    pose proof (tensor_grade_sum _ _ _ nv) as [l l_eq].
    subst v; clear nv.
    exists l.
    induction l as [|[α x] l] using ulist_induction.
    {
        do 2 rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    }
    do 2 rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite tensor_to_ext_plus.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite tensor_to_ext_scalar.
    apply f_equal.
    destruct x as [l l_size]; cbn; clear l_size.
    induction l.
    {
        cbn.
        reflexivity.
    }
    cbn.
    rewrite tensor_to_ext_mult.
    rewrite IHl.
    reflexivity.
Qed.
(* begin hide *)

End ExteriorGrade.
(* end hide *)
