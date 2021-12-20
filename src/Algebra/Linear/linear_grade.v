Require Import init.

Require Export linear_base.
Require Import linear_subspace.

Require Import set.
Require Import unordered_list.

#[universes(template)]
Record SubspaceVector U V `{Plus V, Zero V, ScalarMult U V}
    := make_subspace_vector
{
    sub_vector_sub : Subspace U V;
    sub_vector_v : V;
    sub_vector_in : subspace_set sub_vector_sub sub_vector_v;
}.
Arguments make_subspace_vector {U V H H0 H1}.
Arguments sub_vector_sub {U V H H0 H1}.
Arguments sub_vector_v {U V H H0 H1}.
Arguments sub_vector_in {U V H H0 H1}.

#[universes(template)]
Class GradedSpace U V `{P : Plus V, @PlusComm V P, @PlusAssoc V P, Zero V, ScalarMult U V} := {
    grade_I : Type;
    grade_subspace : grade_I → Subspace U V;
    grade_distinct : ∀ i j, i ≠ j → ∀ v,
        subspace_set (grade_subspace i) v → subspace_set (grade_subspace j) v →
        0 = v;
    grade_decompose_ex : ∀ v : V, ∃ l : ulist (SubspaceVector U V),
        v = ulist_sum (ulist_image l sub_vector_v) ∧
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                             subspace_set (sub_vector_sub S)) l;
    grade_independent : ∀ l : ulist (SubspaceVector U V),
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                             subspace_set (sub_vector_sub S)) l →
        ulist_unique (ulist_image l (λ S, subspace_set (sub_vector_sub S))) →
        0 = ulist_sum (ulist_image l sub_vector_v) →
        ulist_prop (λ S, 0 = sub_vector_v S) l;
}.

Section LinearGrade.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @MultAssoc U UM,
    @MultLid U UM UO,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    VPC : @PlusComm V VP,
    VPA : @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM,
    @ScalarComp U V UM SM
}.

Context `{@GradedSpace U V VP VPC VPA VZ SM}.

Definition of_grade i v := subspace_set (grade_subspace i) v.

Definition homogeneous v := ∃ i, of_grade i v.

Theorem of_grade_unique : ∀ v i j, 0 ≠ v → of_grade i v → of_grade j v → i = j.
    intros v i j v_nz vi vj.
    classic_contradiction contr.
    pose proof (grade_distinct i j contr v vi vj).
    contradiction.
Qed.

Theorem grade_decompose_ex2 : ∀ v : V, ∃ l : ulist (set_type homogeneous),
        v = ulist_sum (ulist_image l (λ x, [x|])) ∧
        ulist_unique (ulist_image l (λ x, ex_val [|x])) ∧
        ulist_prop (λ x, 0 ≠ [x|]) l.
    intros v.
    pose proof (grade_decompose_ex v) as [l [v_eq l_subs]].
    revert v v_eq l_subs.
    induction l using ulist_induction; intros.
    -   exists ulist_end.
        rewrite ulist_image_end in v_eq.
        rewrite ulist_sum_end in v_eq.
        rewrite ulist_image_end.
        rewrite ulist_sum_end.
        rewrite ulist_image_end.
        repeat split.
        +   exact v_eq.
        +   apply ulist_unique_end.
        +   apply ulist_prop_end.
    -   rewrite ulist_image_add in v_eq.
        rewrite ulist_sum_add in v_eq.
        rewrite ulist_prop_add in l_subs.
        destruct l_subs as [[i S_eq] l_subs].
        apply plus_rlmove in v_eq.
        specialize (IHl _ v_eq l_subs) as [l' [av_eq [l'_uni l'_nz]]].
        classic_case (0 = sub_vector_v a) as [a_z|a_nz].
        {
            rewrite <- a_z in av_eq.
            rewrite neg_zero, plus_lid in av_eq.
            exists l'.
            repeat split; assumption.
        }
        classic_case (in_ulist (ulist_image l'
            (λ x, subspace_set (grade_subspace (ex_val [|x]))))
            (subspace_set (sub_vector_sub a))) as [a_in|a_nin].
        2: {
            assert (homogeneous (sub_vector_v a)) as a_homo.
            {
                exists i.
                unfold of_grade.
                rewrite S_eq.
                apply sub_vector_in.
            }
            exists ([_|a_homo] ::: l').
            rewrite ulist_prop_add.
            repeat rewrite ulist_image_add.
            rewrite ulist_unique_add.
            repeat split.
            -   rewrite ulist_sum_add.
                rewrite plus_rlmove.
                exact av_eq.
            -   rewrite_ex_val j a_j.
                cbn in a_j.
                intros j_in.
                apply a_nin.
                apply image_in_ulist in j_in as [a' [a'_eq a'_in]].
                pose proof (in_ulist_image _ _ (λ x, subspace_set
                    (grade_subspace (ex_val [|x]))) a'_in) as a'_in'.
                cbn in a'_in'.
                assert (subspace_set (grade_subspace (ex_val [|a'])) =
                    subspace_set (sub_vector_sub a)) as eq.
                {
                    rewrite <- S_eq.
                    do 2 apply f_equal.
                    rewrite_ex_val k a'_k.
                    subst k.
                    apply (of_grade_unique (sub_vector_v a)).
                    -   exact a_nz.
                    -   exact a_j.
                    -   unfold of_grade.
                        rewrite S_eq.
                        apply sub_vector_in.
                }
                rewrite eq in a'_in'.
                exact a'_in'.
            -   exact l'_uni.
            -   exact a_nz.
            -   exact l'_nz.
        }
        apply image_in_ulist in a_in as [b [ab_eq b_in]].
        apply in_ulist_split in b_in as [l'' l_eq].
        subst l'.
        assert (subspace_set (grade_subspace i)
            (sub_vector_v a + [b|])) as ab_in.
        {
            rewrite S_eq.
            apply subspace_plus.
            -   exact (sub_vector_in a).
            -   rewrite <- ab_eq.
                rewrite_ex_val j b_in.
                exact b_in.
        }
        assert (homogeneous (sub_vector_v a + [b|])) as ab_homo.
        {
            exists i.
            exact ab_in.
        }
        pose (ab := [_|ab_homo]).
        rewrite ulist_image_add, ulist_sum_add in av_eq.
        rewrite <- plus_rlmove in av_eq.
        rewrite plus_assoc in av_eq.
        rewrite ulist_image_add, ulist_unique_add in l'_uni.
        rewrite ulist_prop_add in l'_nz.
        classic_case (0 = [ab|]) as [ab_z|ab_nz].
        +   exists l''.
            repeat split.
            *   cbn in ab_z.
                rewrite <- ab_z in av_eq.
                rewrite plus_lid in av_eq.
                exact av_eq.
            *   apply l'_uni.
            *   apply l'_nz.
        +   exists (ab ::: l'').
            repeat rewrite ulist_image_add.
            rewrite ulist_prop_add.
            rewrite ulist_unique_add.
            repeat split.
            *   rewrite ulist_sum_add.
                exact av_eq.
            *   destruct l'_uni as [b_nin l'_uni].
                assert (ex_val [|b] = ex_val [|ab]) as eq.
                {
                    rewrite_ex_val j1 j1_eq.
                    rewrite_ex_val j2 j2_eq.
                    assert (i = j1) as eq.
                    {
                        apply (of_grade_unique (sub_vector_v a)).
                        -   exact a_nz.
                        -   unfold of_grade.
                            rewrite S_eq.
                            apply sub_vector_in.
                        -   unfold of_grade.
                            rewrite ab_eq.
                            apply sub_vector_in.
                    }
                    subst j1.
                    apply (of_grade_unique [ab|]).
                    -   exact ab_nz.
                    -   exact ab_in.
                    -   exact j2_eq.
                }
                rewrite eq in b_nin.
                exact b_nin.
            *   apply l'_uni.
            *   exact ab_nz.
            *   apply l'_nz.
Qed.

Definition grade_decomposition v := ex_val (grade_decompose_ex2 v).

Theorem grade_decomposition_eq : ∀ v,
        v = ulist_sum (ulist_image (grade_decomposition v) (λ x, [x|])).
    intros v.
    apply (ex_proof (grade_decompose_ex2 v)).
Qed.

Theorem grade_decomposition_uni : ∀ v,
        ulist_unique (ulist_image (grade_decomposition v) (λ x, ex_val [|x])).
    intros v.
    apply (ex_proof (grade_decompose_ex2 v)).
Qed.

Theorem grade_decomposition_nz : ∀ v,
        ulist_prop (λ x, 0 ≠ [x|]) (grade_decomposition v).
    intros v.
    apply (ex_proof (grade_decompose_ex2 v)).
Qed.

Lemma grade_decompose_unique_strengthen : ∀ l : ulist (set_type homogeneous),
        ulist_unique (ulist_image l (λ x, ex_val [|x])) →
        ulist_prop (λ x, 0 ≠ [x|]) l →
        ulist_unique (ulist_image l
            (λ x, subspace_set (grade_subspace (ex_val [|x])))).
    intros l l_uni l_nz.
    induction l using ulist_induction.
    -   rewrite ulist_image_end.
        apply ulist_unique_end.
    -   rewrite ulist_image_add, ulist_unique_add.
        rewrite ulist_image_add, ulist_unique_add in l_uni.
        rewrite ulist_prop_add in l_nz.
        split.
        +   clear IHl.
            intros a_in.
            apply (land l_uni).
            apply image_in_ulist in a_in as [a' [eq a'_in]].
            assert (ex_val [|a'] = ex_val [|a]) as eq'.
            {
                apply (of_grade_unique _ _ _ (land l_nz)); unfold of_grade in *.
                -   rewrite eq.
                    apply (ex_proof [|a]).
                -   apply (ex_proof [|a]).
            }
            rewrite <- eq'.
            apply (in_ulist_image l a').
            exact a'_in.
        +   apply IHl.
            *   apply l_uni.
            *   apply l_nz.
Qed.

Lemma grade_decomposition_perm_wlog :
        ∀ v (al bl : ulist (set_type homogeneous)),
        v = ulist_sum (ulist_image al (λ x, [x|])) →
        v = ulist_sum (ulist_image bl (λ x, [x|])) →
        ulist_unique (ulist_image al (λ x, ex_val [|x])) →
        ulist_unique (ulist_image bl (λ x, ex_val [|x])) →
        ulist_prop (λ x, 0 ≠ [x|]) al →
        ulist_prop (λ x, 0 ≠ [x|]) bl →
        ∀ x, in_ulist al x → in_ulist bl x.
    intros v al bl v_eq1 v_eq2 al_uni bl_uni al_nz bl_nz x al_x.
    classic_contradiction bl_x.
    assert (∃ (x' : set_type homogeneous) al bl,
        0 ≠ [x'|] ∧
        0 = [x'|] + ulist_sum (ulist_image al (λ x, [x|]))
                  - ulist_sum (ulist_image bl (λ x, [x|])) ∧
        ulist_unique (ulist_image (x' ::: al)
            (λ x, subspace_set (grade_subspace (ex_val [|x])))) ∧
        ulist_unique (ulist_image (x' ::: bl)
            (λ x, subspace_set (grade_subspace (ex_val [|x])))) ∧
        ulist_prop (λ x, 0 ≠ [x|]) al ∧
        ulist_prop (λ x, 0 ≠ [x|]) bl
    ) as lemma.
    {
        apply in_ulist_split in al_x as [al' al_eq].
        subst al.
        rewrite ulist_image_add, ulist_unique_add in al_uni.
        destruct al_uni as [al_x al_uni].
        apply ulist_prop_add in al_nz as [x_nz al_nz].
        classic_case (∃ x', in_ulist bl x' ∧ ex_val [|x] = ex_val [|x'])
            as [x'_ex|x'_nex].
        -   destruct x'_ex as [x' [x'_in xx'_eq]].
            apply in_ulist_split in x'_in as [bl' bl_eq].
            subst bl.
            pose (x'' := [x|] - [x'|]).
            destruct x as [x x_homo], x' as [x' x'_homo]; cbn in *.
            unpack_ex_val i i_eq x_eq.
            rewrite i_eq in xx'_eq.
            unpack_ex_val_with x'_homo j j_eq x'_eq.
            rewrite j_eq in xx'_eq.
            subst j.
            assert (subspace_set (grade_subspace i) x'') as x''_in.
            {
                apply subspace_plus.
                -   exact x_eq.
                -   apply subspace_neg.
                    exact x'_eq.
            }
            assert (homogeneous x'') as x''_homo.
            {
                exists i.
                exact x''_in.
            }
            assert (ex_val x''_homo = i) as x''_eq.
            {
                rewrite_ex_val j x''_eq.
                apply (of_grade_unique x'').
                -   unfold x''; intros contr.
                    rewrite plus_0_anb_a_b in contr.
                    subst x'.
                    rewrite in_ulist_add in bl_x.
                    rewrite not_or in bl_x.
                    destruct bl_x as [neq bl_x].
                    apply neq.
                    apply set_type_eq; reflexivity.
                -   exact x''_eq.
                -   exact x''_in.
            }
            rewrite in_ulist_add in bl_x.
            rewrite not_or in bl_x.
            exists [_|x''_homo], al', bl'.
            unfold x''; cbn.
            repeat split.
            +   intros contr.
                apply (land bl_x).
                rewrite plus_0_anb_a_b in contr.
                subst x'.
                apply set_type_eq; reflexivity.
            +   rewrite <- (plus_assoc x).
                rewrite (plus_comm (-x')).
                rewrite plus_assoc.
                rewrite ulist_image_add, ulist_sum_add in v_eq1, v_eq2.
                cbn in *.
                rewrite <- v_eq1.
                rewrite <- plus_assoc.
                rewrite <- neg_plus.
                rewrite <- v_eq2.
                rewrite plus_rinv.
                reflexivity.
            +   apply grade_decompose_unique_strengthen.
                *   rewrite ulist_image_add, ulist_unique_add.
                    cbn.
                    rewrite i_eq in al_x.
                    rewrite <- x''_eq in al_x.
                    split; assumption.
                *   rewrite ulist_prop_add; cbn.
                    split; [>|exact al_nz].
                    intros contr.
                    rewrite plus_0_anb_a_b in contr.
                    subst x'.
                    apply (land bl_x).
                    apply set_type_eq; reflexivity.
            +   apply grade_decompose_unique_strengthen.
                *   rewrite ulist_image_add, ulist_unique_add; cbn.
                    rewrite ulist_image_add, ulist_unique_add in bl_uni.
                    split; [>|apply bl_uni].
                    cbn in bl_uni.
                    rewrite j_eq in bl_uni.
                    rewrite <- x''_eq in bl_uni.
                    apply bl_uni.
                *   rewrite ulist_prop_add.
                    rewrite ulist_prop_add in bl_nz; cbn.
                    split; [>|apply bl_nz].
                    intros contr.
                    rewrite plus_0_anb_a_b in contr.
                    subst x'.
                    apply (land bl_x).
                    apply set_type_eq; reflexivity.
            +   exact al_nz.
            +   rewrite ulist_prop_add in bl_nz.
                apply bl_nz.
        -   exists x, al', bl.
            repeat split.
            +   exact x_nz.
            +   rewrite ulist_image_add, ulist_sum_add in v_eq1.
                rewrite <- v_eq1, <- v_eq2.
                rewrite plus_rinv.
                reflexivity.
            +   apply grade_decompose_unique_strengthen.
                *   rewrite ulist_image_add, ulist_unique_add.
                    split; assumption.
                *   rewrite ulist_prop_add.
                    split; assumption.
            +   rewrite ulist_image_add, ulist_unique_add.
                split.
                2: apply grade_decompose_unique_strengthen; assumption.
                rewrite not_ex in x'_nex.
                intros contr.
                apply image_in_ulist in contr as [x' [x'_eq x'_in]].
                symmetry in x'_eq.
                specialize (x'_nex x').
                rewrite not_and in x'_nex.
                destruct x'_nex as [x'_nex|x'_nex]; try contradiction.
                apply x'_nex.
                apply (of_grade_unique _ _ _ x_nz).
                *   apply (ex_proof [|x]).
                *   unfold of_grade in *.
                    rewrite <- x'_eq.
                    apply (ex_proof [|x]).
            +   exact al_nz.
            +   exact bl_nz.
    }
    clear v al bl v_eq1 v_eq2 al_uni bl_uni al_nz bl_nz x al_x bl_x.
    destruct lemma as [x [al [bl [x_nz [eq [al_uni [bl_uni [al_nz bl_nz]]]]]]]].
    assert (∃ l,
        ulist_sum (ulist_image al (λ x, [x|])) -
            ulist_sum (ulist_image bl (λ x, [x|])) =
            ulist_sum (ulist_image l (λ x, [x|])) ∧
        ulist_unique (ulist_image (x ::: l)
            (λ x, subspace_set (grade_subspace (ex_val [|x])))))
        as [l [l_eq l_uni]].
    {
        revert al eq al_uni bl_uni al_nz bl_nz.
        induction bl using ulist_induction; intros.
        {
            exists al.
            repeat split; try assumption.
            rewrite ulist_image_end, ulist_sum_end.
            rewrite neg_zero, plus_rid.
            reflexivity.
        }
        classic_case (∃ a', ex_val [|a'] = ex_val [|a] ∧ in_ulist al a')
            as [a'_in|a'_nin].
        -   destruct a'_in as [a' [aa' a'_in]].
            apply in_ulist_split in a'_in as [al' eq']; subst al.
            rename al' into al.
            pose (a'' := [a'|] - [a|]).
            classic_case (0 = a'') as [a'_z|a'_nz].
            +   unfold a'' in *; clear a''.
                specialize (IHbl al).
                prove_parts IHbl.
                *   rewrite eq.
                    do 2 rewrite <- plus_assoc.
                    apply lplus.
                    do 2 rewrite ulist_image_add, ulist_sum_add.
                    rewrite neg_plus.
                    rewrite plus_assoc.
                    apply rplus.
                    rewrite (plus_comm [a'|]).
                    rewrite <- plus_assoc.
                    rewrite <- a'_z.
                    apply plus_rid.
                *   rewrite ulist_swap in al_uni.
                    rewrite ulist_image_add, ulist_unique_add in al_uni.
                    apply al_uni.
                *   rewrite ulist_swap in bl_uni.
                    rewrite ulist_image_add, ulist_unique_add in bl_uni.
                    apply bl_uni.
                *   rewrite ulist_prop_add in al_nz.
                    apply al_nz.
                *   rewrite ulist_prop_add in bl_nz.
                    apply bl_nz.
                *   destruct IHbl as [l [l_eq l_uni]].
                    exists l.
                    repeat split; try assumption.
                    do 2 rewrite ulist_image_add, ulist_sum_add.
                    rewrite neg_plus.
                    rewrite <- plus_assoc.
                    rewrite (plus_assoc _ (-[a|])).
                    rewrite (plus_comm _ (-[a|])).
                    do 2 rewrite plus_assoc.
                    rewrite <- a'_z.
                    rewrite plus_lid.
                    exact l_eq.
            +   assert (subspace_set (grade_subspace (ex_val [|a])) a'') as a''_in.
                {
                    apply subspace_plus.
                    -   rewrite <- aa'.
                        apply (ex_proof [|a']).
                    -   apply subspace_neg.
                        apply (ex_proof [|a]).
                }
                assert (homogeneous a'') as a''_homo.
                {
                    exists (ex_val [|a]).
                    exact a''_in.
                }
                unfold a'' in *; clear a''.
                specialize (IHbl ([_|a''_homo] ::: al)).
                prove_parts IHbl.
                *   rewrite ulist_image_add, ulist_sum_add; cbn.
                    rewrite eq.
                    do 2 rewrite <- plus_assoc.
                    apply lplus.
                    do 2 rewrite ulist_image_add, ulist_sum_add.
                    rewrite neg_plus.
                    do 3 rewrite <- plus_assoc.
                    apply lplus.
                    do 2 rewrite plus_assoc.
                    apply rplus.
                    apply plus_comm.
                *   do 2 rewrite ulist_image_add, ulist_unique_add; cbn.
                    rewrite in_ulist_add.
                    rewrite not_or.
                    do 2 rewrite ulist_image_add, ulist_unique_add in al_uni.
                    rewrite in_ulist_add in al_uni.
                    rewrite not_or in al_uni.
                    assert (ex_val a''_homo = ex_val [|a']) as eq'.
                    {
                        rewrite aa'.
                        apply (of_grade_unique _ _ _ a'_nz).
                        -   apply (ex_proof a''_homo).
                        -   exact a''_in.
                    }
                    rewrite eq'.
                    exact al_uni.
                *   rewrite ulist_swap in bl_uni.
                    rewrite ulist_image_add, ulist_unique_add in bl_uni.
                    apply bl_uni.
                *   rewrite ulist_prop_add; cbn.
                    split.
                    --  exact a'_nz.
                    --  rewrite ulist_prop_add in al_nz.
                        apply al_nz.
                *   rewrite ulist_prop_add in bl_nz.
                    apply bl_nz.
                *   destruct IHbl as [l [l_eq l_uni]].
                    exists l.
                    repeat split; try assumption.
                    rewrite ulist_image_add, ulist_sum_add in l_eq; cbn in l_eq.
                    do 2 rewrite ulist_image_add, ulist_sum_add.
                    rewrite neg_plus.
                    rewrite <- plus_assoc.
                    rewrite (plus_assoc _ (-[a|])).
                    rewrite (plus_comm _ (-[a|])).
                    do 2 rewrite plus_assoc.
                    exact l_eq.
        -   assert (subspace_set (grade_subspace (ex_val [|a])) (-[a|])) as a'_in.
            {
                apply subspace_neg.
                apply (ex_proof [|a]).
            }
            assert (homogeneous (-[a|])) as a'_homo.
            {
                exists (ex_val [|a]).
                exact a'_in.
            }
            assert (ex_val a'_homo = ex_val [|a]) as a_eq.
            {
                apply (of_grade_unique [a|]).
                -   rewrite ulist_prop_add in bl_nz.
                    apply bl_nz.
                -   rewrite <- neg_neg.
                    apply subspace_neg.
                    apply (ex_proof a'_homo).
                -   apply (ex_proof [|a]).
            }
            specialize (IHbl ([_|a'_homo] ::: al)).
            prove_parts IHbl.
            +   rewrite ulist_image_add, ulist_sum_add; cbn.
                rewrite ulist_image_add, ulist_sum_add in eq.
                rewrite eq.
                rewrite neg_plus.
                do 2 rewrite plus_assoc.
                apply rplus.
                do 2 rewrite <- plus_assoc.
                apply lplus.
                apply plus_comm.
            +   do 2 rewrite ulist_image_add, ulist_unique_add; cbn.
                rewrite in_ulist_add.
                rewrite not_or.
                rewrite ulist_image_add, ulist_unique_add in al_uni.
                destruct al_uni as [x_nin al_uni].
                repeat split; try assumption.
                *   do 2 rewrite ulist_image_add, ulist_unique_add in bl_uni.
                    rewrite in_ulist_add in bl_uni.
                    rewrite not_or in bl_uni.
                    rewrite a_eq.
                    apply bl_uni.
                *   intros contr.
                    apply image_in_ulist in contr.
                    rewrite a_eq in contr.
                    destruct contr as [b [b_eq b_in]].
                    rewrite not_ex in a'_nin.
                    specialize (a'_nin b).
                    rewrite not_and in a'_nin.
                    destruct a'_nin as [a'_nin|a'_nin]; [>|contradiction].
                    apply a'_nin.
                    rewrite ulist_prop_add in bl_nz.
                    apply (of_grade_unique _ _ _ (land bl_nz)).
                    --  unfold of_grade in *.
                        rewrite b_eq.
                        apply (ex_proof [|a]).
                    --  apply (ex_proof [|a]).
            +   rewrite ulist_swap in bl_uni.
                rewrite ulist_image_add, ulist_unique_add in bl_uni.
                apply bl_uni.
            +   rewrite ulist_prop_add; cbn.
                apply ulist_prop_add in bl_nz as [a_nz bl_nz].
                split; try assumption.
                intros contr.
                apply (f_equal neg) in contr.
                rewrite neg_neg, neg_zero in contr.
                contradiction.
            +   rewrite ulist_prop_add in bl_nz.
                apply bl_nz.
            +   destruct IHbl as [l [l_eq l_uni]].
                rewrite ulist_image_add in l_eq; cbn in l_eq.
                exists l.
                repeat split; try assumption.
                rewrite ulist_sum_add in l_eq.
                rewrite ulist_image_add, ulist_sum_add.
                rewrite neg_plus.
                rewrite plus_assoc.
                rewrite (plus_comm _ (-[a|])).
                exact l_eq.
    }
    rewrite <- plus_assoc in eq.
    rewrite l_eq in eq.
    clear al_uni bl_uni al_nz bl_nz l_eq.
    rewrite <- ulist_sum_add in eq.
    rewrite <- ulist_image_add in eq.
    pose (l' := ulist_image (x ::: l) (λ x, make_subspace_vector
        (grade_subspace (ex_val [|x]))
        [x|]
        (ex_proof [|x])
    )).
    pose proof (grade_independent l') as ind.
    unfold l' in ind; cbn in ind; clear l'.
    prove_parts ind.
    -   clear eq l_uni.
        rewrite ulist_image_add, ulist_prop_add; cbn.
        split.
        1: exists (ex_val [|x]); reflexivity.
        induction l using ulist_induction.
        +   rewrite ulist_image_end.
            apply ulist_prop_end.
        +   rewrite ulist_image_add, ulist_prop_add.
            split.
            *   exists (ex_val [|a]).
                cbn.
                reflexivity.
            *   exact IHl.
    -   rewrite ulist_image_comp; cbn.
        exact l_uni.
    -   rewrite ulist_image_comp; cbn.
        exact eq.
    -   rewrite ulist_image_add, ulist_prop_add in ind; cbn in ind.
        destruct ind; contradiction.
Qed.

Theorem grade_decomposition_unique : ∀ v l,
        v = ulist_sum (ulist_image l (λ x, [x|])) →
        ulist_unique (ulist_image l (λ x, ex_val [|x])) →
        ulist_prop (λ x, 0 ≠ [x|]) l →
        grade_decomposition v = l.
    intros v l l_eq l_uni l_nz.
    apply ulist_in_unique_eq.
    -   pose proof (grade_decomposition_uni v) as v_uni.
        apply ulist_image_unique in v_uni.
        exact v_uni.
    -   apply ulist_image_unique in l_uni.
        exact l_uni.
    -   intros x.
        pose proof (grade_decomposition_eq v).
        pose proof (grade_decomposition_uni v).
        pose proof (grade_decomposition_nz v).
        split; apply (grade_decomposition_perm_wlog v); assumption.
Qed.

Theorem grade_decomposition_zero : grade_decomposition 0 = ulist_end.
    apply grade_decomposition_unique.
    -   rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    -   rewrite ulist_image_end.
        apply ulist_unique_end.
    -   apply ulist_prop_end.
Qed.

Theorem of_grade_zero : ∀ i, of_grade i 0.
    intros i.
    apply subspace_zero.
Qed.

Theorem of_grade_scalar : ∀ a v i, of_grade i v → of_grade i (a · v).
    intros a v i v_in.
    apply subspace_scalar.
    exact v_in.
Qed.

Theorem of_grade_neg : ∀ v i, of_grade i v → of_grade i (-v).
    intros v i v_in.
    apply subspace_neg.
    exact v_in.
Qed.

Theorem of_grade_plus : ∀ u v i,
        of_grade i u → of_grade i v → of_grade i (u + v).
    intros u v i u_in v_in.
    apply subspace_plus; assumption.
Qed.

Theorem grade_decomposition_of_grade : ∀ v i, 0 ≠ v → ∀ H : of_grade i v,
        grade_decomposition v =
        [v|ex_intro _ i H] ::: ulist_end.
    intros v i v_nz v_in.
    apply grade_decomposition_unique.
    -   rewrite ulist_image_add, ulist_image_end; cbn.
        rewrite ulist_sum_add, ulist_sum_end.
        rewrite plus_rid.
        reflexivity.
    -   rewrite ulist_image_add, ulist_unique_add; cbn.
        rewrite ulist_image_end.
        split; [>apply in_ulist_end|apply ulist_unique_end].
    -   rewrite ulist_prop_add; cbn.
        split; [>exact v_nz|apply ulist_prop_end].
Qed.

Theorem grade_decomposition_homo : ∀ v : set_type homogeneous, 0 ≠ [v|] →
        grade_decomposition [v|] = v ::: ulist_end.
    intros [v [i v_in]] v_neq; cbn in *.
    apply grade_decomposition_of_grade.
    exact v_neq.
Qed.

Theorem homo_scalar : ∀ a v, homogeneous v → homogeneous (a · v).
    intros a v [i v_in].
    exists i.
    exact (of_grade_scalar _ _ _ v_in).
Qed.

Theorem homo_neg : ∀ v, homogeneous v → homogeneous (-v).
    intros v [i v_in].
    exists i.
    exact (of_grade_neg _ _ v_in).
Qed.

Definition grade_project v i :=
    match (strong_excluded_middle (
        ∃ a : set_type homogeneous, ex_val [|a] = i ∧
             in_ulist (grade_decomposition v) a
        )) with
    | strong_or_left H => [ex_val H|]
    | strong_or_right H => 0
    end.

Ltac case_grade_project v i vi vi_eq vi_in v_nin := let X := fresh in
    change (grade_project v i) with
        (match (strong_excluded_middle (
            ∃ a : set_type homogeneous, ex_val [|a] = i ∧
                 in_ulist (grade_decomposition v) a
            )) with
        | strong_or_left H => [ex_val H|]
        | strong_or_right H => 0
        end) in *;
    destruct (strong_excluded_middle (∃ a,
        ex_val [|a] = i ∧ in_ulist (grade_decomposition v) a)) as [X|v_nin];
    [>
        change (ex_val X) with (ex_type_val (ex_to_type X)) in *;
        destruct (ex_to_type X) as [vi [vi_eq vi_in]];
        clear X;
        change
            (ex_type_val
             (ex_type_constr
                (λ a : set_type homogeneous,
                   ex_val [ | a] = i ∧ in_ulist (grade_decomposition v) a) vi
                (make_and vi_eq vi_in)))
            with vi in *
    |].

Theorem grade_project_grade : ∀ v i, of_grade i (grade_project v i).
    intros v i.
    case_grade_project v i vi vi_eq vi_in v_nin.
    -   unfold of_grade.
        rewrite <- vi_eq.
        apply (ex_proof [|vi]).
    -   apply of_grade_zero.
Qed.

Theorem grade_project_homo : ∀ v i, homogeneous (grade_project v i).
    intros v i.
    exists i.
    apply grade_project_grade.
Qed.

Theorem grade_project_in : ∀ v i, 0 ≠ grade_project v i →
        in_ulist (grade_decomposition v)
            [grade_project v i|grade_project_homo v i].
    intros v i vi_nz.
    assert (in_ulist (ulist_image
        (grade_decomposition v) (λ x, [x|])) (grade_project v i)) as vi_in.
    {
        case_grade_project v i vi vi_eq vi_in v_nin.
        -   apply in_ulist_image.
            exact vi_in.
        -   contradiction.
    }
    apply image_in_ulist in vi_in as [x [x_eq x_in]].
    assert ([grade_project v i | grade_project_homo v i] = x) as x_eq'.
    {
        apply set_type_eq; cbn.
        symmetry; exact x_eq.
    }
    rewrite x_eq'; clear x_eq'.
    case_grade_project v i vi vi_eq vi_in v_nin.
    -   exact x_in.
    -   contradiction.
Qed.

Theorem grade_project_zero : ∀ i, grade_project 0 i = 0.
    intros i.
    case_grade_project 0 i zi zi_eq zi_in v_nin.
    -   rewrite grade_decomposition_zero in zi_in.
        apply in_ulist_end in zi_in.
        contradiction zi_in.
    -   reflexivity.
Qed.

Theorem grade_project_of_grade : ∀ v i, of_grade i v → grade_project v i = v.
    intros v i v_in.
    classic_case (0 = v) as [v_z|v_nz].
    {
        rewrite <- v_z.
        apply grade_project_zero.
    }
    assert (homogeneous v) as v_homo by (exists i; exact v_in).
    pose proof (grade_decomposition_homo [v|v_homo] v_nz) as v_eq.
    cbn in v_eq.
    case_grade_project v i vi vi_eq vi_in v_nin.
    -   rewrite v_eq in vi_in.
        apply in_ulist_single in vi_in.
        subst vi; cbn.
        reflexivity.
    -   rewrite not_ex in v_nin.
        rewrite v_eq in v_nin.
        specialize (v_nin [v|v_homo]); cbn in v_nin.
        rewrite not_and in v_nin.
        destruct v_nin as [v_nin|v_nin].
        +   exfalso; apply v_nin.
            apply (of_grade_unique _ _ _ v_nz).
            *   apply (ex_proof v_homo).
            *   exact v_in.
        +   rewrite in_ulist_add in v_nin.
            rewrite not_or in v_nin.
            destruct v_nin; contradiction.
Qed.

Theorem grade_project_project : ∀ v i,
        grade_project (grade_project v i) i = grade_project v i.
    intros v i.
    apply grade_project_of_grade.
    apply grade_project_grade.
Qed.

Theorem grade_project_eq_of_grade : ∀ v i, v = grade_project v i → of_grade i v.
    intros v i v_eq.
    rewrite v_eq.
    apply grade_project_grade.
Qed.

End LinearGrade.
