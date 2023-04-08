Require Import init.

Require Export linear_base.
Require Import linear_subspace.
Require Export linear_grade_base.

Require Import set.
Require Import nat.
Require Import unordered_list.

(* begin hide *)
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
    VPZ : @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM,
    @ScalarComp U V UM SM
}.

Context `{VG : @GradedSpace U V VP VPC VPA VZ VPZ SM}.

(* end hide *)
Theorem grade_decomposition_zero : grade_decomposition 0 = ulist_end.
Proof.
    apply grade_decomposition_unique.
    -   rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    -   rewrite ulist_image_end.
        apply ulist_unique_end.
    -   apply ulist_prop_end.
Qed.

Theorem of_grade_zero : ∀ i, of_grade i 0.
Proof.
    intros i.
    apply subspace_zero.
Qed.

Theorem of_grade_scalar : ∀ a v i, of_grade i v → of_grade i (a · v).
Proof.
    intros a v i v_in.
    apply subspace_scalar.
    exact v_in.
Qed.

Theorem of_grade_neg : ∀ v i, of_grade i v → of_grade i (-v).
Proof.
    intros v i v_in.
    apply subspace_neg.
    exact v_in.
Qed.

Theorem of_grade_plus : ∀ u v i,
    of_grade i u → of_grade i v → of_grade i (u + v).
Proof.
    intros u v i u_in v_in.
    apply subspace_plus; assumption.
Qed.

Theorem grade_decomposition_of_grade : ∀ v i, 0 ≠ v → ∀ H : of_grade i v,
    grade_decomposition v =
    [v|ex_intro _ i H] ː ulist_end.
Proof.
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
    grade_decomposition [v|] = v ː ulist_end.
Proof.
    intros [v [i v_in]] v_neq; cbn in *.
    apply grade_decomposition_of_grade.
    exact v_neq.
Qed.

Theorem homo_scalar : ∀ a v, homogeneous v → homogeneous (a · v).
Proof.
    intros a v [i v_in].
    exists i.
    exact (of_grade_scalar _ _ _ v_in).
Qed.

Theorem homo_neg : ∀ v, homogeneous v → homogeneous (-v).
Proof.
    intros v [i v_in].
    exists i.
    exact (of_grade_neg _ _ v_in).
Qed.

Definition grade_project v i :=
    match (sem (
        ∃ a : set_type homogeneous, ex_val [|a] = i ∧
             in_ulist (grade_decomposition v) a
        )) with
    | strong_or_left H => [ex_val H|]
    | strong_or_right H => 0
    end.

Ltac case_grade_project v i vi vi_eq vi_in v_nin := let X := fresh in
    change (grade_project v i) with
        (match (sem (
            ∃ a : set_type homogeneous, ex_val [|a] = i ∧
                 in_ulist (grade_decomposition v) a
            )) with
        | strong_or_left H => [ex_val H|]
        | strong_or_right H => 0
        end) in *;
    destruct (sem (∃ a,
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
Proof.
    intros v i.
    case_grade_project v i vi vi_eq vi_in v_nin.
    -   unfold of_grade.
        rewrite <- vi_eq.
        apply (ex_proof [|vi]).
    -   apply of_grade_zero.
Qed.

Theorem grade_project_homo : ∀ v i, homogeneous (grade_project v i).
Proof.
    intros v i.
    exists i.
    apply grade_project_grade.
Qed.

Theorem grade_project_in : ∀ v i, 0 ≠ grade_project v i →
    in_ulist (grade_decomposition v)
        [grade_project v i|grade_project_homo v i].
Proof.
    intros v i vi_nz.
    assert (in_ulist (ulist_image
        (λ x, [x|]) (grade_decomposition v)) (grade_project v i)) as vi_in.
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
Proof.
    intros i.
    case_grade_project 0 i zi zi_eq zi_in v_nin.
    -   rewrite grade_decomposition_zero in zi_in.
        apply in_ulist_end in zi_in.
        contradiction zi_in.
    -   reflexivity.
Qed.

Theorem grade_project_of_grade : ∀ v i, of_grade i v → grade_project v i = v.
Proof.
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
        apply in_ulist_single_eq in vi_in.
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

Theorem grade_project_of_grade_neq : ∀ i j v, of_grade i v → i ≠ j →
    grade_project v j = 0.
Proof.
    intros i j v iv neq.
    case_grade_project v j vj vj_eq vj_in vj_nin; [>|reflexivity].
    assert (homogeneous v) as v_homo by (exists i; exact iv).
    classic_case (0 = v) as [v_z|v_nz].
    1: {
        subst v.
        rewrite grade_decomposition_zero in vj_in.
        contradiction (in_ulist_end _ vj_in).
    }
    pose proof (grade_decomposition_homo [v|v_homo] v_nz) as v_eq.
    cbn in v_eq.
    rewrite v_eq in vj_in.
    rewrite in_ulist_add in vj_in.
    destruct vj_in as [vj_eq'|vj_in]; [>|contradiction (in_ulist_end _ vj_in)].
    subst vj; cbn.
    cbn in vj_eq.
    rewrite_ex_val k vk.
    subst k.
    exfalso; apply neq.
    exact (of_grade_unique _ _ _ v_nz iv vk).
Qed.

Theorem grade_project_project : ∀ v i,
    grade_project (grade_project v i) i = grade_project v i.
Proof.
    intros v i.
    apply grade_project_of_grade.
    apply grade_project_grade.
Qed.

Theorem grade_project_eq_of_grade : ∀ v i, v = grade_project v i → of_grade i v.
Proof.
    intros v i v_eq.
    rewrite v_eq.
    apply grade_project_grade.
Qed.

Theorem grade_induction : ∀ S : V → Prop,
    S 0 → (∀ u v i, of_grade i u →
        0 = grade_project v i → S v → S (u + v)) → ∀ v, S v.
Proof.
    intros S S0 S_ind v.
    remember (grade_decomposition v) as l.
    pose proof (grade_decomposition_uni v) as l_uni.
    pose proof (grade_decomposition_nz v) as l_nz.
    rewrite (grade_decomposition_eq v).
    rewrite <- Heql.
    rewrite <- Heql in l_uni, l_nz.
    clear Heql.
    induction l using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        exact S0.
    }
    rewrite ulist_image_add, ulist_sum_add.
    clear v.
    remember (ulist_sum (ulist_image (λ x, [x|]) l)) as v.
    apply (S_ind _ _ (ex_val [|a])).
    -   apply (ex_proof [|a]).
    -   case_grade_project v (ex_val [|a]) vi vi_eq vi_in vi_nin;
            [>|reflexivity].
        assert (grade_decomposition v = l) as l_eq.
        {
            apply grade_decomposition_unique.
            -   exact Heqv.
            -   rewrite ulist_image_add, ulist_unique_add in l_uni.
                apply l_uni.
            -   rewrite ulist_prop_add in l_nz.
                apply l_nz.
        }
        rewrite l_eq in vi_in.
        rewrite ulist_image_add, ulist_unique_add in l_uni.
        exfalso; apply (land l_uni).
        rewrite <- vi_eq.
        apply (in_ulist_image (l:=l) (a:=vi)).
        exact vi_in.
    -   apply IHl.
        +   rewrite ulist_image_add, ulist_unique_add in l_uni.
            apply l_uni.
        +   rewrite ulist_prop_add in l_nz.
            apply l_nz.
Qed.

Lemma grade_decomposition_plus_homo : ∀ (a b : set_type homogeneous) v,
    ex_val [|a] ≠ ex_val [|b] →
    in_ulist (grade_decomposition v) a →
    in_ulist (grade_decomposition ([b|] + v)) a.
Proof.
    intros a b v neq a_in.
    classic_case (0 = [b|]) as [b_z|b_nz].
    1: {
        rewrite <- b_z.
        rewrite plus_lid.
        exact a_in.
    }
    classic_case (∃ c, ex_val [|b] = ex_val [|c] ∧
            in_ulist (grade_decomposition v) c) as [c_ex|c_nex].
    -   destruct c_ex as [c [c_eq c_in]].
        apply in_ulist_split in c_in as [l l_eq].
        classic_case (0 = [b|] + [c|]).
        +   assert (grade_decomposition ([b|] + v) = l) as l_eq2.
            {
                apply grade_decomposition_unique.
                -   apply plus_lcancel with [c|].
                    rewrite <- ulist_sum_add, <- ulist_image_add.
                    rewrite <- l_eq.
                    rewrite <- grade_decomposition_eq.
                    rewrite plus_assoc.
                    rewrite (plus_comm [c|]).
                    rewrite <- e.
                    apply plus_lid.
                -   pose proof (grade_decomposition_uni v) as l_uni.
                    rewrite l_eq in l_uni.
                    rewrite ulist_image_add, ulist_unique_add in l_uni.
                    apply l_uni.
                -   pose proof (grade_decomposition_nz v) as l_nz.
                    rewrite l_eq in l_nz.
                    rewrite ulist_prop_add in l_nz.
                    apply l_nz.
            }
            rewrite l_eq2.
            rewrite l_eq in a_in.
            apply in_ulist_add in a_in as [a_eq|a_in]; [>|exact a_in].
            subst c.
            symmetry in c_eq; contradiction.
        +   assert (homogeneous ([b|] + [c|])) as bc_homo.
            {
                exists (ex_val [|b]).
                apply of_grade_plus.
                -   exact (ex_proof [|b]).
                -   rewrite c_eq.
                    exact (ex_proof [|c]).
            }
            assert (grade_decomposition ([b|] + v) = [_|bc_homo] ː l)
                as l_eq2.
            {
                apply grade_decomposition_unique.
                -   rewrite ulist_image_add, ulist_sum_add; cbn.
                    rewrite (grade_decomposition_eq v).
                    rewrite l_eq.
                    rewrite ulist_image_add, ulist_sum_add.
                    apply plus_assoc.
                -   rewrite ulist_image_add, ulist_unique_add.
                    pose proof (grade_decomposition_uni v) as l_uni.
                    rewrite l_eq in l_uni.
                    rewrite ulist_image_add, ulist_unique_add in l_uni.
                    destruct l_uni as [c_nin l_uni].
                    split; [>|exact l_uni].
                    cbn.
                    intros bc_in.
                    apply image_in_ulist in bc_in as [bc [bc_eq bc_in]].
                    apply c_nin.
                    assert (ex_val [|c] = ex_val [|bc]) as c_bc_eq.
                    {
                        apply (of_grade_unique _ _ _ n).
                        -   apply of_grade_plus.
                            +   rewrite <- c_eq.
                                exact (ex_proof [|b]).
                            +   exact (ex_proof [|c]).
                        -   rewrite bc_eq.
                            exact (ex_proof bc_homo).
                    }
                    rewrite c_bc_eq.
                    apply (in_ulist_image (l:=l) (a:=bc)).
                    exact bc_in.
                -   rewrite ulist_prop_add; cbn.
                    split; [>exact n|].
                    pose proof (grade_decomposition_nz v) as v_nz.
                    rewrite l_eq in v_nz.
                    rewrite ulist_prop_add in v_nz.
                    apply v_nz.
            }
            rewrite l_eq2.
            rewrite in_ulist_add.
            right.
            rewrite l_eq in a_in.
            apply in_ulist_add in a_in as [a_eq|a_in]; [>|exact a_in].
            subst c.
            symmetry in c_eq; contradiction.
    -   rewrite not_ex in c_nex.
        assert (grade_decomposition ([b|] + v) = b ː grade_decomposition v)
            as l_eq.
        {
            apply grade_decomposition_unique.
            -   rewrite ulist_image_add, ulist_sum_add.
                rewrite <- grade_decomposition_eq.
                reflexivity.
            -   rewrite ulist_image_add, ulist_unique_add.
                split; [>|apply grade_decomposition_uni].
                intros contr.
                apply image_in_ulist in contr as [a' [a'_eq a'_in]].
                specialize (c_nex a').
                rewrite and_comm, not_and_impl in c_nex.
                specialize (c_nex a'_in).
                rewrite a'_eq in c_nex.
                contradiction.
            -   rewrite ulist_prop_add.
                split; [>exact b_nz|apply grade_decomposition_nz].
        }
        rewrite l_eq.
        rewrite in_ulist_add.
        right.
        exact a_in.
Qed.

Lemma grade_project_plus_neq : ∀ a v i j, i ≠ j → of_grade i a →
    grade_project (a + v) j = grade_project v j.
Proof.
    intros a v i j neq ai.
    classic_case (0 = a) as [a_z|a_nz].
    1: {
        rewrite <- a_z.
        rewrite plus_lid.
        reflexivity.
    }
    case_grade_project v j vj vj_eq vj_in vj_nin.
    -   assert (in_ulist (grade_decomposition (a + v)) vj) as vj_in2.
        {
            assert (homogeneous a) as a_homo by (exists i; exact ai).
            change a with [[a|a_homo]|].
            apply grade_decomposition_plus_homo; [>|exact vj_in].
            rewrite vj_eq.
            cbn.
            rewrite_ex_val i' ai'.
            assert (i = i') as i_eq.
            {
                apply (of_grade_unique _ _ _ a_nz); assumption.
            }
            subst i'.
            rewrite neq_sym; exact neq.
        }
        case_grade_project (a + v) j avj avj_eq avj_in avj_nin.
        +   apply in_ulist_split in vj_in2 as [l l_eq].
            rewrite l_eq in avj_in.
            rewrite in_ulist_add in avj_in.
            destruct avj_in as [eq|avj_in]; [>subst; reflexivity|].
            pose proof (grade_decomposition_uni (a + v)) as av_uni.
            rewrite l_eq in av_uni.
            rewrite ulist_image_add, ulist_unique_add in av_uni.
            destruct av_uni as [vj_nin av_uni].
            exfalso; apply vj_nin.
            rewrite vj_eq, <- avj_eq.
            apply (in_ulist_image (l:=l) (a:=avj)).
            exact avj_in.
        +   rewrite not_ex in avj_nin.
            specialize (avj_nin vj).
            rewrite not_and in avj_nin.
            destruct avj_nin; contradiction.
    -   rewrite not_ex in vj_nin.
        case_grade_project (a + v) j avj avj_eq avj_in avj_nin.
        +   specialize (vj_nin avj).
            rewrite not_and_impl in vj_nin.
            specialize (vj_nin avj_eq).
            exfalso; apply vj_nin.
            rewrite <- (plus_llinv v a).
            assert (homogeneous (-a)) as a_homo.
            {
                apply homo_neg.
                exists i.
                exact ai.
            }
            change (-a) with [[-a|a_homo]|].
            apply grade_decomposition_plus_homo; [>|exact avj_in].
            rewrite avj_eq.
            cbn.
            rewrite_ex_val i' ai'.
            assert (i = i') as i_eq.
            {
                apply (of_grade_unique _ _ _ a_nz ai).
                apply of_grade_neg in ai'.
                rewrite neg_neg in ai'.
                exact ai'.
            }
            subst i'.
            rewrite neq_sym; exact neq.
        +   reflexivity.
Qed.

Theorem grade_project_plus : ∀ u v i,
    grade_project (u + v) i = grade_project u i + grade_project v i.
Proof.
    intros u v i.
    revert v.
    induction u as [|u' u j u'j eq IHu] using grade_induction; intros.
    {
        rewrite grade_project_zero.
        do 2 rewrite plus_lid.
        reflexivity.
    }
    rewrite (plus_comm u' u).
    rewrite <- plus_assoc.
    rewrite IHu.
    rewrite IHu.
    rewrite <- plus_assoc.
    apply lplus.
    clear u eq IHu.

    rename u' into a.
    revert a j u'j.
    induction v as [|b v k bk eq IHv] using grade_induction; intros.
    {
        rewrite grade_project_zero.
        do 2 rewrite plus_rid.
        reflexivity.
    }
    classic_case (j = k) as [jk_eq|jk_neq].
    -   subst k.
        pose proof (of_grade_plus _ _ _ u'j bk) as ab_j.
        rewrite plus_assoc.
        rewrite (IHv _ j) by exact ab_j.
        rewrite (IHv _ j) by exact bk.
        rewrite plus_assoc.
        apply rplus.
        classic_case (i = j) as [ij_eq|ij_neq].
        +   subst j.
            do 3 rewrite grade_project_of_grade by assumption.
            reflexivity.
        +   rewrite neq_sym in ij_neq.
            rewrite (grade_project_of_grade_neq j i) by assumption.
            rewrite (grade_project_of_grade_neq j i) by assumption.
            rewrite (grade_project_of_grade_neq j i) by assumption.
            rewrite plus_rid.
            reflexivity.
    -   classic_case (i = j) as [ij_eq|ij_neq].
        +   subst j.
            rewrite plus_assoc.
            rewrite (plus_comm a b).
            rewrite <- plus_assoc.
            rewrite neq_sym in jk_neq.
            rewrite (grade_project_plus_neq _ _ k i) by assumption.
            rewrite (grade_project_plus_neq b _ k i) by assumption.
            rewrite (IHv _ i u'j).
            reflexivity.
        +   rewrite neq_sym in ij_neq.
            rewrite (grade_project_plus_neq _ _ j i) by assumption.
            rewrite (grade_project_of_grade_neq j i a) by assumption.
            rewrite plus_lid.
            reflexivity.
Qed.

Theorem grade_project_scalar : ∀ a v i,
    grade_project (a · v) i = a · grade_project v i.
Proof.
    intros a v i.
    induction v as [|u v j uj eq IHv] using grade_induction.
    1: {
        rewrite scalar_ranni.
        rewrite grade_project_zero.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite scalar_ldist.
    do 2 rewrite grade_project_plus.
    rewrite IHv.
    rewrite scalar_ldist.
    apply rplus.
    clear v eq IHv.
    pose proof (of_grade_scalar a u j uj) as auj.
    classic_case (i = j) as [eq|neq].
    -   subst j.
        rewrite grade_project_of_grade by exact auj.
        rewrite grade_project_of_grade by exact uj.
        reflexivity.
    -   rewrite neq_sym in neq.
        rewrite (grade_project_of_grade_neq j) by assumption.
        rewrite (grade_project_of_grade_neq j) by assumption.
        rewrite scalar_ranni.
        reflexivity.
Qed.

Theorem grade_project_neg : ∀ v i, grade_project (-v) i = -grade_project v i.
Proof.
    intros v i.
    rewrite <- scalar_neg_one.
    rewrite grade_project_scalar.
    apply scalar_neg_one.
Qed.

Theorem in_grade_decomposition_project : ∀ v u,
    in_ulist (grade_decomposition v) u → ∃ i, [u|] = grade_project v i.
Proof.
    intros v u u_in.
    destruct u as [u [i ui]]; cbn.
    assert (0 ≠ u) as u_nz.
    {
        intros contr; subst u.
        apply in_ulist_split in u_in as [l l_eq].
        pose proof (grade_decomposition_nz v) as v_nz.
        rewrite l_eq in v_nz.
        apply ulist_prop_add in v_nz as [neq v_nz].
        contradiction.
    }
    exists i.
    case_grade_project v i vi vi_eq vi_in vi_nin.
    -   pose proof (grade_decomposition_uni v) as v_uni.
        apply in_ulist_split in vi_in as [l l_eq].
        rewrite l_eq in v_uni, u_in.
        rewrite ulist_image_add, ulist_unique_add in v_uni.
        rewrite vi_eq in v_uni.
        destruct v_uni as [i_nin v_uni].
        apply in_ulist_add in u_in as [u_eq|u_in].
        +   rewrite u_eq.
            reflexivity.
        +   apply in_ulist_split in u_in as [l' l'_eq].
            subst l.
            rewrite ulist_image_add, in_ulist_add in i_nin.
            rewrite not_or in i_nin.
            cbn in i_nin.
            rewrite_ex_val i' i'_eq.
            exfalso; apply (land i_nin).
            apply (of_grade_unique _ _ _ u_nz); assumption.
    -   rewrite not_ex in vi_nin.
        specialize (vi_nin [u | ex_intro _ i ui]).
        rewrite not_and in vi_nin.
        destruct vi_nin as [neq|nin].
        +   rewrite_ex_val i' i'_eq.
            exfalso; apply neq.
            apply (of_grade_unique _ _ _ u_nz); assumption.
        +   contradiction.
Qed.

Theorem all_grade_project_eq : ∀ u v,
    (∀ i, grade_project u i = grade_project v i) → u = v.
Proof.
    intros u v all_eq.
    rewrite (grade_decomposition_eq u).
    rewrite (grade_decomposition_eq v).
    do 2 apply f_equal.
    apply ulist_in_unique_eq.
    1, 2: apply (ulist_image_unique (grade_decomposition _) (λ x, ex_val [|x])).
    1, 2: apply grade_decomposition_uni.
    intros x.
    split; intros x_in.
    -   assert (0 ≠ [x|]) as x_nz.
        {
            pose proof (grade_decomposition_nz u) as u_nz.
            apply in_ulist_split in x_in as [l l_eq].
            rewrite l_eq in u_nz.
            rewrite ulist_prop_add in u_nz.
            apply u_nz.
        }
        apply in_grade_decomposition_project in x_in as [i x_eq].
        rewrite all_eq in x_eq.
        case_grade_project v i vi vi_eq vi_in vi_nin.
        +   apply set_type_eq in x_eq.
            rewrite x_eq.
            exact vi_in.
        +   rewrite x_eq in x_nz.
            contradiction.
    -   assert (0 ≠ [x|]) as x_nz.
        {
            pose proof (grade_decomposition_nz v) as v_nz.
            apply in_ulist_split in x_in as [l l_eq].
            rewrite l_eq in v_nz.
            rewrite ulist_prop_add in v_nz.
            apply v_nz.
        }
        apply in_grade_decomposition_project in x_in as [i x_eq].
        rewrite <- all_eq in x_eq.
        case_grade_project u i ui ui_eq ui_in ui_nin.
        +   apply set_type_eq in x_eq.
            rewrite x_eq.
            exact ui_in.
        +   rewrite x_eq in x_nz.
            contradiction.
Qed.

(* begin hide *)
Context `{
    IP : Plus grade_I,
    @PlusLcancel grade_I IP,
    @PlusRcancel grade_I IP,
    VM : Mult V,
    @Ldist V VP VM,
    @Rdist V VP VM,
    @GradedAlgebraObj U V VP VPC VPA VZ VPZ SM VG IP VM
}.

(* end hide *)
Theorem of_grade_mult : ∀ u v i j, of_grade i u → of_grade j v →
    of_grade (i + j) (u * v).
Proof.
    apply grade_mult.
Qed.

Theorem homo_mult : ∀ u v, homogeneous u → homogeneous v → homogeneous (u * v).
Proof.
    intros u v [i ui] [j vj].
    exists (i + j).
    apply of_grade_mult; assumption.
Qed.

Theorem homo_lmult_project : ∀ i j u v, of_grade i u →
    grade_project (u * v) (i + j) = u * (grade_project v j).
Proof.
    intros i j u v ui.
    induction v as [|v' v j' v'j' vj' IHv] using grade_induction.
    1: {
        rewrite mult_ranni.
        do 2 rewrite grade_project_zero.
        rewrite mult_ranni.
        reflexivity.
    }
    rewrite ldist.
    do 2 rewrite grade_project_plus.
    rewrite ldist.
    rewrite IHv.
    apply rplus.
    clear v vj' IHv.
    rename v' into v.
    pose proof (of_grade_mult u v _ _ ui v'j') as uv_ij.
    classic_case (j = j') as [j_eq|j_neq].
    -   subst j'.
        rewrite grade_project_of_grade by exact uv_ij.
        rewrite grade_project_of_grade by exact v'j'.
        reflexivity.
    -   rewrite (grade_project_of_grade_neq (i + j')).
        +   rewrite neq_sym in j_neq.
            rewrite (grade_project_of_grade_neq j') by assumption.
            rewrite mult_ranni.
            reflexivity.
        +   exact uv_ij.
        +   intros contr.
            apply plus_lcancel in contr.
            symmetry in contr; contradiction.
Qed.

Theorem homo_rmult_project : ∀ i j u v, of_grade j v →
    grade_project (u * v) (i + j) = (grade_project u i) * v.
Proof.
    intros i j u v vj.
    induction u as [|u' u i' u'i' ui' IHu] using grade_induction.
    1: {
        rewrite mult_lanni.
        do 2 rewrite grade_project_zero.
        rewrite mult_lanni.
        reflexivity.
    }
    rewrite rdist.
    do 2 rewrite grade_project_plus.
    rewrite rdist.
    rewrite IHu.
    apply rplus.
    clear u ui' IHu.
    rename u' into u.
    pose proof (of_grade_mult u v _ _ u'i' vj) as uv_ij.
    classic_case (i = i') as [i_eq|i_neq].
    -   subst i'.
        rewrite grade_project_of_grade by exact uv_ij.
        rewrite grade_project_of_grade by exact u'i'.
        reflexivity.
    -   rewrite (grade_project_of_grade_neq (i' + j)).
        +   rewrite neq_sym in i_neq.
            rewrite (grade_project_of_grade_neq i') by assumption.
            rewrite mult_lanni.
            reflexivity.
        +   exact uv_ij.
        +   intros contr.
            apply plus_rcancel in contr.
            symmetry in contr; contradiction.
Qed.

Theorem grade_project_sum : ∀ f n a b,
    grade_project (sum f a b) n = sum (λ m, grade_project (f m) n) a b.
Proof.
    intros f n a b.
    nat_induction b.
    -   unfold zero; cbn.
        apply grade_project_zero.
    -   cbn.
        rewrite grade_project_plus.
        rewrite IHb.
        reflexivity.
Qed.

Theorem sum_grade_project_single : ∀ f A n a b, Injective f →
    ∀ m, f m = n → a ≤ m → m < a + b →
    sum (λ m, grade_project (grade_project A (f m)) n) a b =
    grade_project A n.
Proof.
    intros f A n a b f_inj m eq m_geq m_leq.
    subst n.
    nat_induction b.
    {
        rewrite plus_rid in m_leq.
        exfalso; clear - m_leq m_geq.
        destruct (lt_le_trans m_leq m_geq); contradiction.
    }
    cbn.
    classic_case (m = a + b) as [eq|neq].
    -   subst m.
        rewrite sum_zero_eq.
        {
            rewrite plus_lid.
            apply grade_project_project.
        }
        intros n n_lt.
        assert (f (a + n) ≠ f (a + b)) as neq.
        {
            intros contr.
            apply f_inj in contr.
            apply plus_lcancel in contr.
            subst n.
            destruct n_lt; contradiction.
        }
        pose proof (grade_project_grade A (f (a + n))) as A_grade.
        apply (grade_project_of_grade_neq _ _ _ A_grade neq).
    -   rewrite nat_plus_rsuc in m_leq.
        rewrite nat_lt_suc_le in m_leq.
        specialize (IHb (make_and m_leq neq)).
        rewrite IHb.
        assert (f (a + b) ≠ f m) as neq'.
        {
            intros contr.
            apply f_inj in contr.
            subst m.
            contradiction.
        }
        pose proof (grade_project_grade A (f (a + b))) as A_grade.
        rewrite (grade_project_of_grade_neq _ _ _ A_grade neq').
        apply plus_rid.
Qed.
(* begin hide *)

End LinearGrade.
(* end hide *)
