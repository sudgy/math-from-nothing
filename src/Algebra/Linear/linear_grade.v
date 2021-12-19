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

Theorem grade_decompose_ex2 : ∀ v : V, ∃ l : ulist (SubspaceVector U V),
        v = ulist_sum (ulist_image l sub_vector_v) ∧
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                             subspace_set (sub_vector_sub S)) l ∧
        ulist_unique (ulist_image l (λ S, subspace_set (sub_vector_sub S))) ∧
        ulist_prop (λ S, 0 ≠ sub_vector_v S) l.
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
        +   apply ulist_prop_end.
        +   apply ulist_unique_end.
        +   apply ulist_prop_end.
    -   rewrite ulist_image_add in v_eq.
        rewrite ulist_sum_add in v_eq.
        rewrite ulist_prop_add in l_subs.
        destruct l_subs as [[i S_eq] l_subs].
        apply plus_rlmove in v_eq.
        specialize (IHl _ v_eq l_subs) as [l' [av_eq [l'_subs [l'_uni l'_nz]]]].
        classic_case (0 = sub_vector_v a) as [a_z|a_nz].
        {
            rewrite <- a_z in av_eq.
            rewrite neg_zero, plus_lid in av_eq.
            exists l'.
            repeat split; assumption.
        }
        classic_case (in_ulist (ulist_image l'
            (λ S, subspace_set (sub_vector_sub S)))
            (subspace_set (sub_vector_sub a))) as [a_in|a_nin].
        2: {
            exists (a ::: l').
            rewrite ulist_prop_add.
            repeat rewrite ulist_image_add.
            rewrite ulist_unique_add.
            rewrite ulist_prop_add.
            repeat split.
            -   rewrite ulist_sum_add.
                rewrite plus_rlmove.
                exact av_eq.
            -   exists i.
                exact S_eq.
            -   exact l'_subs.
            -   exact a_nin.
            -   exact l'_uni.
            -   exact a_nz.
            -   exact l'_nz.
        }
        apply image_in_ulist in a_in as [b [ab_eq b_in]].
        apply in_ulist_split in b_in as [l'' l_eq].
        subst l'.
        assert (subspace_set (sub_vector_sub a)
            (sub_vector_v a + sub_vector_v b)) as ab_in.
        {
            apply subspace_plus.
            -   exact (sub_vector_in a).
            -   rewrite <- ab_eq.
                exact (sub_vector_in b).
        }
        pose (ab := make_subspace_vector
            (sub_vector_sub a)
            (sub_vector_v a + sub_vector_v b)
            ab_in
        ).
        rewrite ulist_image_add, ulist_sum_add in av_eq.
        rewrite <- plus_rlmove in av_eq.
        rewrite plus_assoc in av_eq.
        rewrite ulist_prop_add in l'_subs.
        rewrite ulist_image_add, ulist_unique_add in l'_uni.
        rewrite ulist_prop_add in l'_nz.
        classic_case (0 = sub_vector_v ab) as [ab_z|ab_nz].
        +   exists l''.
            repeat split.
            *   cbn in ab_z.
                rewrite <- ab_z in av_eq.
                rewrite plus_lid in av_eq.
                exact av_eq.
            *   apply l'_subs.
            *   apply l'_uni.
            *   apply l'_nz.
        +   exists (ab ::: l'').
            repeat rewrite ulist_image_add.
            do 2 rewrite ulist_prop_add.
            rewrite ulist_unique_add.
            repeat split.
            *   rewrite ulist_sum_add.
                exact av_eq.
            *   exists i.
                rewrite S_eq.
                reflexivity.
            *   apply l'_subs.
            *   rewrite ab_eq in l'_uni.
                apply l'_uni.
            *   apply l'_uni.
            *   exact ab_nz.
            *   apply l'_nz.
Qed.

Definition grade_decomposition v := ex_val (grade_decompose_ex2 v).

Theorem grade_decomposition_eq : ∀ v,
        v = ulist_sum (ulist_image (grade_decomposition v) sub_vector_v).
    intros v.
    apply (ex_proof (grade_decompose_ex2 v)).
Qed.

Theorem grade_decomposition_in : ∀ v,
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                       subspace_set (sub_vector_sub S)) (grade_decomposition v).
    intros v.
    apply (ex_proof (grade_decompose_ex2 v)).
Qed.

Theorem grade_decomposition_uni : ∀ v,
        ulist_unique (ulist_image (grade_decomposition v)
                                (λ S, subspace_set (sub_vector_sub S))).
    intros v.
    apply (ex_proof (grade_decompose_ex2 v)).
Qed.

Theorem grade_decomposition_nz : ∀ v,
        ulist_prop (λ S, 0 ≠ sub_vector_v S) (grade_decomposition v).
    intros v.
    apply (ex_proof (grade_decompose_ex2 v)).
Qed.

Lemma grade_decomposition_perm_wlog :
        ∀ v al bl,
        v = ulist_sum (ulist_image al sub_vector_v) →
        v = ulist_sum (ulist_image bl sub_vector_v) →
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                              subspace_set (sub_vector_sub S)) al →
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                              subspace_set (sub_vector_sub S)) bl →
        ulist_unique (ulist_image al (λ S, subspace_set (sub_vector_sub S))) →
        ulist_unique (ulist_image bl (λ S, subspace_set (sub_vector_sub S))) →
        ulist_prop (λ S, 0 ≠ sub_vector_v S) al →
        ulist_prop (λ S, 0 ≠ sub_vector_v S) bl →
        ∀ x, in_ulist al x → in_ulist bl x.
    intros v al bl v_eq1 v_eq2 al_in bl_in al_uni bl_uni al_nz bl_nz x al_x.
    classic_contradiction bl_x.
    assert (∃ x' al bl,
        0 ≠ sub_vector_v x' ∧
        0 = sub_vector_v x' + ulist_sum (ulist_image al sub_vector_v)
                            - ulist_sum (ulist_image bl sub_vector_v) ∧
        (∃ i, subspace_set (grade_subspace i) =
              subspace_set (sub_vector_sub x')) ∧
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                              subspace_set (sub_vector_sub S)) al ∧
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                              subspace_set (sub_vector_sub S)) bl ∧
        ulist_unique (ulist_image (x' ::: al)
                                  (λ S, subspace_set (sub_vector_sub S))) ∧
        ulist_unique (ulist_image (x' ::: bl)
                                  (λ S, subspace_set (sub_vector_sub S))) ∧
        ulist_prop (λ S, 0 ≠ sub_vector_v S) al ∧
        ulist_prop (λ S, 0 ≠ sub_vector_v S) bl
    ) as lemma.
    {
        apply in_ulist_split in al_x as [al' al_eq].
        subst al.
        apply ulist_prop_add in al_in as [x_in al_in].
        rewrite ulist_image_add, ulist_unique_add in al_uni.
        destruct al_uni as [al_x al_uni].
        apply ulist_prop_add in al_nz as [x_nz al_nz].
        classic_case (∃ x', in_ulist bl x' ∧
            subspace_set (sub_vector_sub x) = subspace_set (sub_vector_sub x'))
            as [x'_ex|x'_nex].
        -   destruct x'_ex as [x' [x'_in x'_eq]].
            apply in_ulist_split in x'_in as [bl' bl_eq].
            subst bl.
            pose (x'' := sub_vector_v x - sub_vector_v x').
            assert (subspace_set (sub_vector_sub x) x'') as x''_in.
            {
                apply subspace_plus.
                -   apply sub_vector_in.
                -   apply subspace_neg.
                    rewrite x'_eq.
                    apply sub_vector_in.
            }
            rewrite in_ulist_add in bl_x.
            rewrite not_or in bl_x.
            exists (make_subspace_vector _ _ x''_in), al', bl'.
            unfold x''; cbn.
            repeat split.
            +   intros contr.
                apply (land bl_x).
                clear x_in.
                destruct x as [x_sub x x_in].
                destruct x' as [x'_sub x' x'_in].
                cbn in *.
                rewrite plus_0_anb_a_b in contr.
                subst x'.
                apply subspace_eq in x'_eq.
                subst x'_sub.
                rewrite (proof_irrelevance x'_in x_in).
                reflexivity.
            +   rewrite <- (plus_assoc (sub_vector_v x)).
                rewrite (plus_comm (-sub_vector_v x')).
                rewrite plus_assoc.
                rewrite ulist_image_add, ulist_sum_add in v_eq1, v_eq2.
                rewrite <- v_eq1.
                rewrite <- plus_assoc.
                rewrite <- neg_plus.
                rewrite <- v_eq2.
                rewrite plus_rinv.
                reflexivity.
            +   exact x_in.
            +   exact al_in.
            +   rewrite ulist_prop_add in bl_in.
                apply bl_in.
            +   rewrite ulist_image_add, ulist_unique_add.
                cbn.
                split.
                *   exact al_x.
                *   exact al_uni.
            +   rewrite ulist_image_add, ulist_unique_add.
                cbn.
                rewrite ulist_image_add, ulist_unique_add in bl_uni.
                split.
                *   intros contr.
                    rewrite x'_eq in contr.
                    destruct bl_uni; contradiction.
                *   apply bl_uni.
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
            +   exact x_in.
            +   exact al_in.
            +   exact bl_in.
            +   rewrite ulist_image_add, ulist_unique_add.
                split; assumption.
            +   rewrite ulist_image_add, ulist_unique_add.
                split.
                2: exact bl_uni.
                rewrite not_ex in x'_nex.
                intros contr.
                apply image_in_ulist in contr as [x' [x'_eq x'_in]].
                symmetry in x'_eq.
                specialize (x'_nex x').
                rewrite not_and in x'_nex.
                destruct x'_nex; contradiction.
            +   exact al_nz.
            +   exact bl_nz.
    }
    clear v al bl v_eq1 v_eq2 al_in bl_in al_uni bl_uni al_nz bl_nz x al_x bl_x.
    destruct lemma as [x [al [bl [x_nz [eq [x_in [al_in [bl_in [al_uni [bl_uni
        [al_nz bl_nz]]]]]]]]]]].
    assert (∃ l,
        ulist_sum (ulist_image al sub_vector_v) -
            ulist_sum (ulist_image bl sub_vector_v) =
            ulist_sum (ulist_image l sub_vector_v) ∧
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                              subspace_set (sub_vector_sub S)) (x ::: l) ∧
        ulist_unique (ulist_image (x ::: l)
                                  (λ S, subspace_set (sub_vector_sub S))))
        as [l [l_eq [l_in l_uni]]].
    {
        revert al eq al_in bl_in al_uni bl_uni al_nz bl_nz.
        induction bl using ulist_induction; intros.
        {
            exists al.
            rewrite ulist_prop_add.
            repeat split; try assumption.
            rewrite ulist_image_end, ulist_sum_end.
            rewrite neg_zero, plus_rid.
            reflexivity.
        }
        classic_case (∃ a',
            subspace_set (sub_vector_sub a') = subspace_set (sub_vector_sub a) ∧
            in_ulist al a') as [a'_in|a'_nin].
        -   destruct a'_in as [a' [aa' a'_in]].
            apply in_ulist_split in a'_in as [al' eq']; subst al.
            rename al' into al.
            pose (a'' := sub_vector_v a' - sub_vector_v a).
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
                    rewrite (plus_comm (sub_vector_v a')).
                    rewrite <- plus_assoc.
                    rewrite <- a'_z.
                    apply plus_rid.
                *   rewrite ulist_prop_add in al_in.
                    apply al_in.
                *   rewrite ulist_prop_add in bl_in.
                    apply bl_in.
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
                *   destruct IHbl as [l [l_eq [l_in l_uni]]].
                    exists l.
                    repeat split; try assumption.
                    do 2 rewrite ulist_image_add, ulist_sum_add.
                    rewrite neg_plus.
                    rewrite <- plus_assoc.
                    rewrite (plus_assoc _ (-sub_vector_v a)).
                    rewrite (plus_comm _ (-sub_vector_v a)).
                    do 2 rewrite plus_assoc.
                    rewrite <- a'_z.
                    rewrite plus_lid.
                    exact l_eq.
            +   assert (subspace_set (sub_vector_sub a) a'') as a''_in.
                {
                    apply subspace_plus.
                    -   rewrite <- aa'.
                        apply sub_vector_in.
                    -   apply subspace_neg.
                        apply sub_vector_in.
                }
                unfold a'' in *; clear a''.
                specialize (IHbl (make_subspace_vector _ _ a''_in ::: al)).
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
                *   rewrite ulist_prop_add; cbn.
                    split.
                    --  rewrite ulist_prop_add in bl_in.
                        apply bl_in.
                    --  rewrite ulist_prop_add in al_in.
                        apply al_in.
                *   rewrite ulist_prop_add in bl_in.
                    apply bl_in.
                *   do 2 rewrite ulist_image_add, ulist_unique_add; cbn.
                    rewrite in_ulist_add.
                    rewrite not_or.
                    rewrite <- aa'.
                    do 2 rewrite ulist_image_add, ulist_unique_add in al_uni.
                    rewrite in_ulist_add in al_uni.
                    rewrite not_or in al_uni.
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
                *   destruct IHbl as [l [l_eq [l_in l_uni]]].
                    exists l.
                    repeat split; try assumption.
                    rewrite ulist_image_add, ulist_sum_add in l_eq; cbn in l_eq.
                    do 2 rewrite ulist_image_add, ulist_sum_add.
                    rewrite neg_plus.
                    rewrite <- plus_assoc.
                    rewrite (plus_assoc _ (-sub_vector_v a)).
                    rewrite (plus_comm _ (-sub_vector_v a)).
                    do 2 rewrite plus_assoc.
                    exact l_eq.
        -   assert (subspace_set (sub_vector_sub a) (-sub_vector_v a)) as a'_in.
            {
                apply subspace_neg.
                apply sub_vector_in.
            }
            specialize (IHbl (make_subspace_vector _ _ a'_in ::: al)).
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
            +   rewrite ulist_prop_add; cbn.
                rewrite ulist_prop_add in bl_in.
                split.
                *   apply bl_in.
                *   exact al_in.
            +   rewrite ulist_prop_add in bl_in.
                apply bl_in.
            +   do 2 rewrite ulist_image_add, ulist_unique_add; cbn.
                rewrite in_ulist_add.
                rewrite not_or.
                rewrite ulist_image_add, ulist_unique_add in al_uni.
                destruct al_uni as [x_nin al_uni].
                repeat split; try assumption.
                *   do 2 rewrite ulist_image_add, ulist_unique_add in bl_uni.
                    rewrite in_ulist_add in bl_uni.
                    rewrite not_or in bl_uni.
                    apply bl_uni.
                *   intros contr.
                    apply image_in_ulist in contr.
                    contradiction.
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
            +   destruct IHbl as [l [l_eq [l_in l_uni]]].
                rewrite ulist_image_add in l_eq; cbn in l_eq.
                exists l.
                repeat split; try assumption.
                rewrite ulist_sum_add in l_eq.
                rewrite ulist_image_add, ulist_sum_add.
                rewrite neg_plus.
                rewrite plus_assoc.
                rewrite (plus_comm _ (-sub_vector_v a)).
                exact l_eq.
    }
    rewrite <- plus_assoc in eq.
    rewrite l_eq in eq.
    clear x_in al_in bl_in al_uni bl_uni al_nz bl_nz l_eq.
    rewrite <- ulist_sum_add in eq.
    rewrite <- ulist_image_add in eq.
    apply (grade_independent _ l_in l_uni) in eq.
    apply ulist_prop_add in eq as [eq l_z].
    contradiction.
Qed.

Theorem grade_decomposition_unique : ∀ v l,
        v = ulist_sum (ulist_image l sub_vector_v) →
        ulist_prop (λ S, ∃ i, subspace_set (grade_subspace i) =
                             subspace_set (sub_vector_sub S)) l →
        ulist_unique (ulist_image l (λ S, subspace_set (sub_vector_sub S))) →
        ulist_prop (λ S, 0 ≠ sub_vector_v S) l →
        grade_decomposition v = l.
    intros v l l_eq l_in l_uni l_nz.
    apply ulist_in_unique_eq.
    -   pose proof (grade_decomposition_uni v) as v_uni.
        apply ulist_image_unique in v_uni.
        exact v_uni.
    -   apply ulist_image_unique in l_uni.
        exact l_uni.
    -   intros x.
        pose proof (grade_decomposition_eq v).
        pose proof (grade_decomposition_in v).
        pose proof (grade_decomposition_uni v).
        pose proof (grade_decomposition_nz v).
        split; apply (grade_decomposition_perm_wlog v); try assumption.
Qed.

Theorem grade_decomposition_zero : grade_decomposition 0 = ulist_end.
    apply grade_decomposition_unique.
    -   rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    -   apply ulist_prop_end.
    -   rewrite ulist_image_end.
        apply ulist_unique_end.
    -   apply ulist_prop_end.
Qed.

Definition of_grade i v := subspace_set (grade_subspace i) v.

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
        make_subspace_vector (grade_subspace i) v H ::: ulist_end.
    intros v i v_nz v_in.
    apply grade_decomposition_unique.
    -   rewrite ulist_image_add, ulist_image_end; cbn.
        rewrite ulist_sum_add, ulist_sum_end.
        rewrite plus_rid.
        reflexivity.
    -   rewrite ulist_prop_add; cbn.
        split; [>exists i; reflexivity|apply ulist_prop_end].
    -   rewrite ulist_image_add, ulist_unique_add; cbn.
        rewrite ulist_image_end.
        split; [>apply in_ulist_end|apply ulist_unique_end].
    -   rewrite ulist_prop_add; cbn.
        split; [>exact v_nz|apply ulist_prop_end].
Qed.

Theorem of_grade_unique : ∀ v i j, 0 ≠ v → of_grade i v → of_grade j v → i = j.
    intros v i j v_nz vi vj.
    classic_contradiction contr.
    pose proof (grade_distinct i j contr v vi vj).
    contradiction.
Qed.

Definition homogeneous v := ∃ i, of_grade i v.

Theorem grade_decomposition_homo : ∀ v : set_type homogeneous, 0 ≠ [v|] →
        grade_decomposition [v|] = make_subspace_vector
            (grade_subspace (ex_val [|v]))
            [v|]
            (ex_proof [|v])
        ::: ulist_end.
    intros [v v_homo] v_neq; cbn in *.
    unfold ex_val, ex_proof.
    destruct (ex_to_type v_homo) as [i v_in]; cbn.
    apply grade_decomposition_unique.
    -   rewrite ulist_image_add, ulist_image_end; cbn.
        rewrite ulist_sum_add, ulist_sum_end.
        rewrite plus_rid.
        reflexivity.
    -   rewrite ulist_prop_add; cbn.
        split; [>exists i; reflexivity|apply ulist_prop_end].
    -   rewrite ulist_image_add, ulist_unique_add; cbn.
        rewrite ulist_image_end.
        split; [>apply in_ulist_end|apply ulist_unique_end].
    -   rewrite ulist_prop_add; cbn.
        split; [>exact v_neq|apply ulist_prop_end].
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
        ∃ a, subspace_set (sub_vector_sub a) = subspace_set (grade_subspace i) ∧
             in_ulist (grade_decomposition v) a
        )) with
    | strong_or_left H => sub_vector_v (ex_val H)
    | strong_or_right H => 0
    end.

Ltac case_grade_project v i vi vi_eq vi_in v_nin := let X := fresh in
    change (grade_project v i) with
        (match (strong_excluded_middle (
            ∃ a, subspace_set (sub_vector_sub a) = subspace_set (grade_subspace i) ∧
                 in_ulist (grade_decomposition v) a
            )) with
        | strong_or_left H => sub_vector_v (ex_val H)
        | strong_or_right H => 0
        end) in *;
    destruct (strong_excluded_middle (∃ a,
        subspace_set (sub_vector_sub a) = subspace_set (grade_subspace i) ∧
        in_ulist (grade_decomposition v) a)) as [X|v_nin];
    [>
        change (ex_val X) with (ex_type_val (ex_to_type X)) in *;
        destruct (ex_to_type X) as [vi [vi_eq vi_in]];
        clear X;
        change
            (ex_type_val
                (ex_type_constr
                   (λ a : SubspaceVector U V,
                      subspace_set (sub_vector_sub a) =
                      subspace_set (grade_subspace i)
                      ∧ in_ulist (grade_decomposition v) a) vi
                   (make_and vi_eq vi_in)))
            with vi in *
    |].

Theorem grade_project_in : ∀ v i, 0 ≠ grade_project v i →
        in_ulist (ulist_image (grade_decomposition v) sub_vector_v)
            (grade_project v i).
    intros v i vi_nz.
    case_grade_project v i vi vi_eq vi_in v_nin.
    -   apply in_ulist_image.
        exact vi_in.
    -   contradiction.
Qed.

Theorem grade_project_grade : ∀ v i, of_grade i (grade_project v i).
    intros v i.
    case_grade_project v i vi vi_eq vi_in v_nin.
    -   unfold of_grade.
        rewrite <- vi_eq.
        apply sub_vector_in.
    -   apply of_grade_zero.
Qed.

Theorem grade_project_homo : ∀ v i, homogeneous (grade_project v i).
    intros v i.
    exists i.
    apply grade_project_grade.
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
        unfold ex_val, ex_proof in v_eq.
        destruct (ex_to_type v_homo) as [j v_in']; cbn in *.
        specialize (v_nin (make_subspace_vector (grade_subspace j) v v_in')).
        cbn in v_nin.
        rewrite not_and in v_nin.
        destruct v_nin as [v_nin|v_nin].
        +   pose proof (of_grade_unique v i j v_nz v_in v_in').
            subst.
            contradiction.
        +   rewrite v_eq in v_nin.
            rewrite in_ulist_add in v_nin.
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
