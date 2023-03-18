Require Import init.

Require Export linear_grade.
Require Import linear_transformation_space.

Require Import set.
Require Import unordered_list.

(* begin hide *)
Section LinearExtend.

Context {U V1 V2} `{
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

    VP1 : Plus V1,
    VZ1 : Zero V1,
    VN1 : Neg V1,
    VPC1 : @PlusComm V1 VP1,
    VPA1 : @PlusAssoc V1 VP1,
    VPZ1 : @PlusLid V1 VP1 VZ1,
    @PlusLinv V1 VP1 VZ1 VN1,

    SM1 : ScalarMult U V1,
    @ScalarId U V1 UO SM1,
    @ScalarLdist U V1 VP1 SM1,
    @ScalarRdist U V1 UP VP1 SM1,
    @ScalarComp U V1 UM SM1,

    VP2 : Plus V2,
    VZ2 : Zero V2,
    VN2 : Neg V2,
    VPC2 : @PlusComm V2 VP2,
    VPA2 : @PlusAssoc V2 VP2,
    @PlusLid V2 VP2 VZ2,
    @PlusLinv V2 VP2 VZ2 VN2,

    SM2 : ScalarMult U V2,
    @ScalarId U V2 UO SM2,
    @ScalarLdist U V2 VP2 SM2,
    @ScalarRdist U V2 UP VP2 SM2,
    @ScalarComp U V2 UM SM2
}.

Context `{VG : @GradedSpace U V1 VP1 VPC1 VPA1 VZ1 VPZ1 SM1}.

(* end hide *)
Definition linear_extend_plus_base (f_base : ∀ i a, of_grade i a → V2) :=
    ∀ (u v : V1) (i : grade_I) (H1 : of_grade i u) (H2 : of_grade i v),
    f_base i (u + v) (of_grade_plus u v i H1 H2) =
    f_base i u H1 + f_base i v H2.
Definition linear_extend_scalar_base (f_base : ∀ i a, of_grade i a → V2) :=
    ∀ a v i (H : of_grade i v),
    f_base i (a · v) (of_grade_scalar a v i H) = a · f_base i v H.

Variable f_base : ∀ i a, of_grade i a → V2.
Variable f_plus_base' : linear_extend_plus_base f_base.
Variable f_scalar_base' : linear_extend_scalar_base f_base.

(* begin hide *)
Lemma linear_extend_base_eq : ∀ i u v H1 H2,
    u = v → f_base i u H1 = f_base i v H2.
Proof.
    intros i u v iu iv uv.
    subst v.
    rewrite (proof_irrelevance iu iv).
    reflexivity.
Qed.

Theorem f_scalar_base : ∀ i a v H1 H2, f_base i (a · v) H1 = a · f_base i v H2.
Proof.
    intros i a v avi vi.
    pose proof (f_scalar_base' a v i vi) as eq.
    rewrite (proof_irrelevance _ avi) in eq.
    exact eq.
Qed.

Theorem linear_extend_zero_base : ∀ i H, f_base i 0 H = 0.
Proof.
    intros i i0.
    pose proof (scalar_lanni 0).
    pose proof i0 as i0'.
    rewrite <- (scalar_lanni 0) in i0'.
    pose proof (f_scalar_base i _ _ i0' i0) as eq.
    rewrite scalar_lanni in eq.
    rewrite <- eq.
    apply linear_extend_base_eq.
    rewrite scalar_lanni.
    reflexivity.
Qed.

Theorem f_plus_base : ∀ i u v H1 H2 H3,
    f_base i (u + v) H1 = f_base i u H2 + f_base i v H3.
Proof.
    intros i u v uvi ui vi.
    pose proof (f_plus_base' u v i ui vi) as eq.
    rewrite (proof_irrelevance _ uvi) in eq.
    exact eq.
Qed.

(* end hide *)
Definition linear_extend (v : V1) :=
    ulist_sum (ulist_image
        (λ x, f_base (ex_val [|x]) [x|] (ex_proof [|x])) (grade_decomposition v)).

Let f := linear_extend.

Theorem linear_extend_zero : f 0 = 0.
Proof.
    unfold f, linear_extend.
    rewrite grade_decomposition_zero.
    rewrite ulist_image_end.
    apply ulist_sum_end.
Qed.

Theorem linear_extend_plus : ∀ u v, f (u + v) = f u + f v.
Proof.
    intros u.
    induction u as [|a u i ai ui IHu] using grade_induction; intros.
    1: {
        rewrite linear_extend_zero.
        do 2 rewrite plus_lid.
        reflexivity.
    }
    rewrite (plus_comm a u).
    rewrite <- plus_assoc.
    do 2 rewrite IHu.
    rewrite <- plus_assoc.
    apply lplus.
    clear u ui IHu.
    classic_case (0 = a) as [a_z|a_nz].
    1: {
        subst a.
        rewrite linear_extend_zero.
        do 2 rewrite plus_lid.
        reflexivity.
    }
    unfold f, linear_extend.
    assert (homogeneous a) as a_homo by (exists i; exact ai).
    assert (ex_val a_homo = i) as i_homo.
    {
        apply (of_grade_unique _ _ _ a_nz).
        -   exact (ex_proof a_homo).
        -   exact ai.
    }
    rewrite (grade_decomposition_homo [a|a_homo] a_nz).
    rewrite ulist_image_add, ulist_sum_add.
    rewrite ulist_image_end, ulist_sum_end, plus_rid.
    classic_case (0 = grade_project v i) as [vi_z|vi_nz].
    -   assert (grade_decomposition (a + v) =
            [a|a_homo] ː grade_decomposition v) as eq.
        {
            apply grade_decomposition_unique.
            -   rewrite ulist_image_add, ulist_sum_add.
                apply lplus.
                apply grade_decomposition_eq.
            -   rewrite ulist_image_add, ulist_unique_add.
                split; [>|apply grade_decomposition_uni].
                intros contr.
                apply image_in_ulist in contr as [a' [a_eq a'_in]].
                cbn in a_eq.
                pose proof (in_grade_decomposition_project _ _ a'_in)
                    as [i' i'_eq].
                assert (i = i') as eq.
                {
                    apply (of_grade_unique [a'|]).
                    -   apply (in_grade_decomposition_nz v).
                        exact a'_in.
                    -   rewrite <- i_homo.
                        rewrite <- a_eq.
                        exact (ex_proof [|a']).
                    -   rewrite i'_eq.
                        apply grade_project_grade.
                }
                subst i'.
                rewrite <- i'_eq in vi_z.
                apply in_grade_decomposition_nz in a'_in.
                contradiction.
            -   rewrite ulist_prop_add; split.
                +   exact a_nz.
                +   apply grade_decomposition_nz.
        }
        rewrite eq.
        rewrite ulist_image_add, ulist_sum_add.
        reflexivity.
    -   pose proof (grade_project_in _ _ vi_nz) as vi_in.
        apply in_ulist_split in vi_in as [l l_eq].
        rewrite l_eq.
        cbn.
        unfold ex_val at 2, ex_proof at 2.
        destruct (ex_to_type _) as [i' ai']; cbn.
        assert (i = i').
        {
            apply (of_grade_unique _ _ _ a_nz); assumption.
        }
        subst i'.
        classic_case (0 = a + grade_project v i) as [b_z|b_nz].
        +   assert (grade_decomposition (a + v) = l) as eq.
            {
                apply grade_decomposition_unique.
                -   rewrite (grade_decomposition_eq v).
                    rewrite l_eq.
                    rewrite ulist_image_add, ulist_sum_add; cbn.
                    rewrite plus_assoc.
                    rewrite <- b_z.
                    apply plus_lid.
                -   pose proof (grade_decomposition_uni v) as v_uni.
                    rewrite l_eq in v_uni.
                    rewrite ulist_image_add, ulist_unique_add in v_uni.
                    apply v_uni.
                -   pose proof (grade_decomposition_nz v) as v_nz.
                    rewrite l_eq in v_nz.
                    rewrite ulist_prop_add in v_nz.
                    apply v_nz.
            }
            rewrite eq.
            rewrite ulist_image_add, ulist_sum_add.
            rewrite plus_assoc.
            cbn.
            unfold ex_val at 2, ex_proof at 2.
            destruct (ex_to_type _) as [i' vi']; cbn.
            assert (i = i').
            {
                apply (of_grade_unique _ _ _ vi_nz).
                -   apply grade_project_grade.
                -   exact vi'.
            }
            subst i'.
            rewrite <- (f_plus_base _ _ _ (of_grade_plus _ _ _ ai' vi')).
            replace (f_base i (a + grade_project v i) _) with
                (f_base i 0 (of_grade_zero i)).
            2: apply linear_extend_base_eq; exact b_z.
            rewrite linear_extend_zero_base.
            rewrite plus_lid.
            reflexivity.
        +   assert (homogeneous (a + grade_project v i)) as b_homo.
            {
                exists i.
                apply of_grade_plus.
                -   exact ai.
                -   apply grade_project_grade.
            }
            assert (grade_decomposition (a + v) = [_|b_homo] ː l) as eq.
            {
                apply grade_decomposition_unique.
                -   rewrite ulist_image_add, ulist_sum_add; cbn.
                    rewrite (grade_decomposition_eq v) at 1.
                    rewrite l_eq.
                    rewrite ulist_image_add, ulist_sum_add; cbn.
                    apply plus_assoc.
                -   rewrite ulist_image_add, ulist_unique_add; cbn.
                    split.
                    +   intros contr.
                        pose proof (grade_decomposition_uni v) as v_uni.
                        rewrite l_eq in v_uni.
                        rewrite ulist_image_add, ulist_unique_add in v_uni.
                        apply (land v_uni); cbn.
                        assert (ex_val (grade_project_homo v i) = ex_val b_homo)
                            as eq.
                        {
                            rewrite_ex_val i1 i1_eq.
                            rewrite_ex_val i2 i2_eq.
                            apply (of_grade_unique (a + grade_project v i)).
                            -   exact b_nz.
                            -   apply of_grade_plus; [>|exact i1_eq].
                                assert (i = i1) as eq.
                                {
                                    apply (of_grade_unique _ _ _ vi_nz).
                                    -   apply grade_project_grade.
                                    -   exact i1_eq.
                                }
                                subst i1.
                                exact ai.
                            -   exact i2_eq.
                        }
                        rewrite eq.
                        exact contr.
                    +   pose proof (grade_decomposition_uni v) as v_uni.
                        rewrite l_eq in v_uni.
                        rewrite ulist_image_add, ulist_unique_add in v_uni.
                        apply v_uni.
                -   rewrite ulist_prop_add.
                    split; [>exact b_nz|].
                    pose proof (grade_decomposition_nz v) as v_nz.
                    rewrite l_eq in v_nz.
                    rewrite ulist_prop_add in v_nz.
                    apply v_nz.
            }
            rewrite eq.
            do 2 rewrite ulist_image_add, ulist_sum_add.
            rewrite plus_assoc.
            apply rplus.
            cbn.
            unfold ex_val at 2, ex_proof at 2.
            destruct (ex_to_type _) as [i' vi']; cbn.
            assert (i = i').
            {
                apply (of_grade_unique _ _ _ vi_nz).
                -   apply grade_project_grade.
                -   exact vi'.
            }
            subst i'.
            rewrite <- (f_plus_base _ _ _ (of_grade_plus _ _ _ ai' vi')).
            unfold ex_val, ex_proof.
            destruct (ex_to_type _) as [i' bi']; cbn.
            assert (i = i').
            {
                apply (of_grade_unique _ _ _ b_nz).
                -   apply of_grade_plus; assumption.
                -   exact bi'.
            }
            subst i'.
            apply linear_extend_base_eq.
            reflexivity.
Qed.

Theorem linear_extend_scalar : ∀ a v, f (a · v) = a · f v.
Proof.
    intros a v.
    induction v as [|u v i ui vi IHv] using grade_induction.
    1: {
        rewrite scalar_ranni.
        rewrite linear_extend_zero.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite scalar_ldist.
    do 2 rewrite linear_extend_plus.
    rewrite scalar_ldist.
    rewrite IHv.
    apply rplus.
    clear v vi IHv.
    classic_case (0 = u) as [u_z|u_nz].
    1: {
        subst u.
        rewrite linear_extend_zero.
        do 2 rewrite scalar_ranni.
        apply linear_extend_zero.
    }
    unfold f, linear_extend.
    rewrite (grade_decomposition_of_grade u i u_nz ui).
    rewrite ulist_image_add, ulist_sum_add.
    rewrite ulist_image_end, ulist_sum_end, plus_rid.
    cbn.
    unfold ex_val, ex_proof.
    destruct (ex_to_type _) as [i' ui']; cbn.
    assert (i = i').
    {
        apply (of_grade_unique _ _ _ u_nz); assumption.
    }
    subst i'.
    rewrite <- (f_scalar_base _ _ _ (of_grade_scalar a _ _ ui')).
    classic_case (0 = a · u) as [au_z|au_nz].
    1: {
        rewrite <- au_z at 1.
        rewrite grade_decomposition_zero.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite <- (linear_extend_zero_base i (of_grade_zero i)).
        apply linear_extend_base_eq.
        exact au_z.
    }
    pose proof (homo_scalar a u (ex_intro _ i ui)) as au_homo.
    rewrite (grade_decomposition_homo [_|au_homo] au_nz).
    rewrite ulist_image_add, ulist_sum_add.
    rewrite ulist_image_end, ulist_sum_end.
    cbn.
    rewrite plus_rid.
    destruct (ex_to_type _) as [i' aui']; cbn.
    assert (i = i').
    {
        apply (of_grade_unique _ _ _ au_nz).
        -   apply of_grade_scalar.
            exact ui.
        -   exact aui'.
    }
    subst i'.
    apply linear_extend_base_eq.
    reflexivity.
Qed.

Theorem linear_extend_homo : ∀ i v H, f v = f_base i v H.
Proof.
    intros i v iv; cbn.
    unfold f, linear_extend.
    classic_case (0 = v) as [v_z|v_nz].
    -   subst v.
        rewrite grade_decomposition_zero.
        rewrite ulist_image_end, ulist_sum_end.
        symmetry; apply linear_extend_zero_base.
    -   assert (homogeneous v) as v_homo by (exists i; exact iv).
        change v with [[v|v_homo]|] at 1.
        rewrite grade_decomposition_homo by exact v_nz.
        rewrite ulist_image_add, ulist_sum_add.
        rewrite ulist_image_end, ulist_sum_end.
        cbn.
        rewrite plus_rid.
        unfold ex_val, ex_proof.
        destruct (ex_to_type v_homo) as [i' vi']; cbn.
        assert (i = i').
        {
            apply (of_grade_unique _ _ _ v_nz); assumption.
        }
        subst i'.
        apply linear_extend_base_eq.
        reflexivity.
Qed.

(* begin hide *)
End LinearExtend.

Section BilinearExtend.

Context {U V1 V2} `{
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

    VP1 : Plus V1,
    VZ1 : Zero V1,
    VN1 : Neg V1,
    VPC1 : @PlusComm V1 VP1,
    VPA1 : @PlusAssoc V1 VP1,
    VPZ1 : @PlusLid V1 VP1 VZ1,
    @PlusLinv V1 VP1 VZ1 VN1,

    SM1 : ScalarMult U V1,
    @ScalarId U V1 UO SM1,
    @ScalarLdist U V1 VP1 SM1,
    @ScalarRdist U V1 UP VP1 SM1,
    @ScalarComp U V1 UM SM1,

    VP2 : Plus V2,
    VZ2 : Zero V2,
    VN2 : Neg V2,
    VPC2 : @PlusComm V2 VP2,
    VPA2 : @PlusAssoc V2 VP2,
    @PlusLid V2 VP2 VZ2,
    @PlusLinv V2 VP2 VZ2 VN2,

    SM2 : ScalarMult U V2,
    @ScalarId U V2 UO SM2,
    @ScalarLdist U V2 VP2 SM2,
    @ScalarRdist U V2 UP VP2 SM2,
    @ScalarComp U V2 UM SM2
}.

Context `{VG : @GradedSpace U V1 VP1 VPC1 VPA1 VZ1 VPZ1 SM1}.

(* end hide *)
Definition bilinear_extend_ldist_base
    (op : ∀ i j a b, of_grade i a → of_grade j b → V2) :=
    ∀ u v w i j (H1 : of_grade i u) (H2 : of_grade j v) (H3 : of_grade j w),
    op i j u (v + w) H1 (of_grade_plus v w j H2 H3) =
    op i j u v H1 H2 + op i j u w H1 H3.
Definition bilinear_extend_rdist_base
    (op : ∀ i j a b, of_grade i a → of_grade j b → V2) :=
    ∀ u v w i j (H1 : of_grade i u) (H2 : of_grade i v) (H3: of_grade j w),
    op i j (u + v) w (of_grade_plus u v i H1 H2) H3 =
    op i j u w H1 H3 + op i j v w H2 H3.
Definition bilinear_extend_lscalar_base
    (op : ∀ i j a b, of_grade i a → of_grade j b → V2) :=
    ∀ a u v i j (H1 : of_grade i u) (H2 : of_grade j v),
    op i j (a · u) v (of_grade_scalar a u i H1) H2 = a · op i j u v H1 H2.
Definition bilinear_extend_rscalar_base
    (op : ∀ i j a b, of_grade i a → of_grade j b → V2) :=
    ∀ a u v i j (H1 : of_grade i u) (H2 : of_grade j v),
    op i j u (a · v) H1 (of_grade_scalar a v j H2) = a · op i j u v H1 H2.

Variable op : ∀ i j a b, of_grade i a → of_grade j b → V2.

Variable op_ldist' : bilinear_extend_ldist_base op.
Variable op_rdist' : bilinear_extend_rdist_base op.
Variable op_lscalar' : bilinear_extend_lscalar_base op.
Variable op_rscalar' : bilinear_extend_rscalar_base op.

(* begin hide *)
Lemma bilinear_extend_base_leq : ∀ i j u v w H1 H2 H3,
    u = v → op i j u w H1 H3 = op i j v w H2 H3.
Proof.
    intros i j u v w iu iv jw eq.
    subst v.
    rewrite (proof_irrelevance iu iv).
    reflexivity.
Qed.

Lemma bilinear_extend_base_req : ∀ i j u v w H1 H2 H3,
    v = w → op i j u v H1 H2 = op i j u w H1 H3.
Proof.
    intros i j u v w iu jv jw eq.
    subst v.
    rewrite (proof_irrelevance jv jw).
    reflexivity.
Qed.

Lemma op_ldist : ∀ i j u v w H1 H2 H3 H4,
    op i j u (v + w) H1 H2 = op i j u v H1 H3 + op i j u w H1 H4.
Proof.
    intros i j u v w iu jvw jv jw.
    rewrite <- op_ldist'.
    rewrite (proof_irrelevance (of_grade_plus _ _ _ _ _) jvw).
    reflexivity.
Qed.

Lemma op_rdist : ∀ i j u v w H1 H2 H3 H4,
    op i j (u + v) w H1 H2 = op i j u w H3 H2 + op i j v w H4 H2.
Proof.
    intros i j u v w iuv jw iu iv.
    rewrite <- op_rdist'.
    rewrite (proof_irrelevance (of_grade_plus _ _ _ _ _) iuv).
    reflexivity.
Qed.

Lemma op_lscalar : ∀ i j a u v H1 H2 H3,
    op i j (a · u) v H1 H3 = a · op i j u v H2 H3.
Proof.
    intros i j a u v iau iu jv.
    rewrite <- op_lscalar'.
    rewrite (proof_irrelevance (of_grade_scalar _ _ _ _) iau).
    reflexivity.
Qed.

Lemma op_rscalar : ∀ i j a u v H1 H2 H3,
    op i j u (a · v) H1 H2 = a · op i j u v H1 H3.
Proof.
    intros i j a u v iu jav jv.
    rewrite <- op_rscalar'.
    rewrite (proof_irrelevance (of_grade_scalar _ _ _ _) jav).
    reflexivity.
Qed.

Lemma bilinear_extend_lanni_base : ∀ i j v H1 H2, op i j 0 v H1 H2 = 0.
Proof.
    intros i j v i0 jv.
    pose (op' i u H1 j v H2 := op j i v u H2 H1).
    change (op i j 0 v i0 jv) with (op' j v jv i 0 i0).
    apply linear_extend_zero_base.
    unfold op'.
    clear i i0 op'.
    unfold linear_extend_scalar_base.
    intros a u i iu.
    apply op_lscalar.
Qed.

Lemma bilinear_extend_ranni_base : ∀ i j v H1 H2, op i j v 0 H1 H2 = 0.
Proof.
    intros i j v iv j0.
    pose (op' i u H1 j v H2 := op i j u v H1 H2).
    change (op i j v 0 iv j0) with (op' i v iv j 0 j0).
    apply linear_extend_zero_base.
    clear j j0.
    unfold linear_extend_scalar_base, op'.
    intros a u j vj.
    apply op_rscalar.
Qed.

Section BilinearBase.

Context i a (ia : of_grade i a).

Let f1_base := λ j v jv, op i j a v ia jv.

Lemma bilinear_extend_base_plus : linear_extend_plus_base f1_base.
Proof.
    intros u v j ju jv.
    unfold f1_base.
    apply op_ldist.
Qed.

Lemma bilinear_extend_base_scalar : linear_extend_scalar_base f1_base.
Proof.
    intros α v j jv.
    unfold f1_base.
    apply op_rscalar.
Qed.

Definition bilinear_extend_base := linear_extend f1_base.

End BilinearBase.

Let TP := linear_func_plus V1 V2.
Let TZ := linear_func_zero V1 V2.
Let TN := linear_func_neg V1 V2.
Let TPC := linear_func_plus_comm V1 V2.
Let TPA := linear_func_plus_assoc V1 V2.
Let TPZ := linear_func_plus_lid V1 V2.
Let TPN := linear_func_plus_linv V1 V2.
Let TSM := linear_func_scalar V1 V2.
Let TSMO := linear_func_scalar_id V1 V2.
Let TSML := linear_func_scalar_ldist V1 V2.
Let TSMR := linear_func_scalar_rdist V1 V2.
Let TSMC := linear_func_scalar_comp V1 V2.
Local Existing Instances TP TZ TN TPC TPA TPZ TPN TSM TSMO TSML TSMR TSMC.

Let f_base := bilinear_extend_base.

Lemma bilinear_extend_plus_base : linear_extend_plus_base f_base.
Proof.
    intros u v i iu iv.
    unfold f_base, bilinear_extend_base.
    apply functional_ext.
    intros x.
    unfold plus at 2; cbn.
    unfold linear_extend.
    remember (grade_decomposition x) as l.
    clear Heql x.
    induction l using ulist_induction.
    1: {
        do 3 rewrite ulist_image_end.
        rewrite ulist_sum_end.
        rewrite plus_rid.
        reflexivity.
    }
    do 3 rewrite ulist_image_add, ulist_sum_add.
    rewrite IHl.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite <- plus_assoc.
    rewrite (plus_comm _ (op _ _ v _ _ _)).
    rewrite plus_assoc.
    apply rplus.
    clear IHl l.
    apply op_rdist.
Qed.

Lemma bilinear_extend_scalar_base : linear_extend_scalar_base f_base.
Proof.
    intros a v i vi.
    unfold f_base, bilinear_extend_base.
    apply functional_ext.
    intros x.
    unfold scalar_mult at 2; cbn.
    unfold linear_extend.
    remember (grade_decomposition x) as l.
    clear Heql x.
    induction l using ulist_induction.
    1: {
        do 2 rewrite ulist_image_end.
        rewrite ulist_sum_end.
        rewrite scalar_ranni.
        reflexivity.
    }
    do 2 rewrite ulist_image_add, ulist_sum_add.
    rewrite IHl.
    rewrite scalar_ldist.
    apply rplus.
    apply op_lscalar.
Qed.

(* end hide *)
Definition bilinear_extend := linear_extend f_base.
Let f := bilinear_extend.

Theorem bilinear_extend_ldist : ∀ u v w, f u (v + w) = f u v + f u w.
Proof.
    intros u v w.
    unfold f, bilinear_extend.
    unfold linear_extend.
    remember (grade_decomposition u) as l.
    clear Heql.
    induction l using ulist_induction.
    1: {
        rewrite ulist_image_end, ulist_sum_end.
        unfold zero; cbn.
        rewrite plus_lid.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    unfold plus at 1 4 5; cbn.
    rewrite IHl; clear IHl.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite <- plus_assoc.
    rewrite (plus_comm _ (f_base _ [a|] _ _)).
    rewrite plus_assoc.
    apply rplus.
    clear l u.
    unfold f_base, bilinear_extend_base.
    apply linear_extend_plus.
    -   unfold linear_extend_plus_base; apply bilinear_extend_base_plus.
    -   unfold linear_extend_scalar_base; apply bilinear_extend_base_scalar.
Qed.

Theorem bilinear_extend_rdist : ∀ u v w, f (u + v) w = f u w + f v w.
Proof.
    intros u v w.
    unfold f, bilinear_extend.
    rewrite linear_extend_plus.
    -   reflexivity.
    -   unfold linear_extend_plus_base; apply bilinear_extend_plus_base.
    -   unfold linear_extend_scalar_base; apply bilinear_extend_scalar_base.
Qed.

Theorem bilinear_extend_lscalar : ∀ a u v, f (a · u) v = a · f u v.
Proof.
    intros a u v.
    unfold f, bilinear_extend.
    rewrite linear_extend_scalar.
    -   reflexivity.
    -   unfold linear_extend_plus_base; apply bilinear_extend_plus_base.
    -   unfold linear_extend_scalar_base; apply bilinear_extend_scalar_base.
Qed.

Theorem bilinear_extend_rscalar : ∀ a u v, f u (a · v) = a · f u v.
Proof.
    intros a u v.
    unfold f, bilinear_extend, linear_extend.
    remember (grade_decomposition u) as l.
    clear Heql u.
    induction l using ulist_induction.
    1: {
        rewrite ulist_image_end, ulist_sum_end.
        unfold zero; cbn.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    unfold plus at 1 2; cbn.
    rewrite IHl; clear IHl.
    rewrite scalar_ldist.
    apply rplus.
    (* This makes a huge speed difference for some reason *)
    unfold f_base, bilinear_extend_base.
    apply linear_extend_scalar.
    -   unfold linear_extend_plus_base; apply bilinear_extend_base_plus.
    -   unfold linear_extend_scalar_base; apply bilinear_extend_base_scalar.
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

Theorem bilinear_extend_homo : ∀ i j u v H1 H2, f u v = op i j u v H1 H2.
Proof.
    intros i j u v iu jv.
    classic_case (0 = u) as [u_z|u_nz].
    2: classic_case (0 = v) as [v_z|v_nz].
    -   subst u.
        rewrite bilinear_extend_lanni_base.
        apply bilinear_extend_lanni.
    -   subst v.
        rewrite bilinear_extend_ranni_base.
        apply bilinear_extend_ranni.
    -   unfold f.
        unfold bilinear_extend.
        rewrite (linear_extend_homo f_base bilinear_extend_scalar_base _ _ iu).
        unfold f_base.
        unfold bilinear_extend_base.
        pose proof (linear_extend_homo (λ j v jv, op i j u v iu jv)) as eq.
        prove_parts eq.
        1: apply bilinear_extend_base_scalar.
        apply (eq _ _ jv).
Qed.
(* begin hide *)

End BilinearExtend.
(* end hide *)
