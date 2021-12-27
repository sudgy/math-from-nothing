Require Import init.

Require Export linear_grade.
Require Import linear_transformation_space.

Require Import set.
Require Import unordered_list.

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
    @PlusLid V1 VP1 VZ1,
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

Context `{VG : @GradedSpace U V1 VP1 VPC1 VPA1 VZ1 SM1}.

Variable f_base : set_type homogeneous → V2.
Variable f_plus_base' : ∀ (u v : V1) (i : grade_I)
    (H1 : of_grade i u) (H2 : of_grade i v),
    f_base [u + v|ex_intro _ i (of_grade_plus u v i H1 H2)] =
    f_base [u|ex_intro _ i H1] + f_base [v|ex_intro _ i H2].
Variable f_scalar_base' : ∀ a v i (H : of_grade i v),
    f_base [a · v|ex_intro _ i (of_grade_scalar a v i H)] =
    a · f_base [v|ex_intro _ i H].

Theorem f_scalar_base : ∀ a v H1 H2, f_base [a · v|H1] = a · f_base [v|H2].
    intros a v av_homo v_homo.
    destruct v_homo as [i vi].
    pose proof (of_grade_scalar a v i vi) as avi.
    pose proof (f_scalar_base' a v i vi) as eq.
    rewrite (proof_irrelevance _ av_homo) in eq.
    exact eq.
Qed.

Theorem linear_extend_zero_base : ∀ H, f_base [0|H] = 0.
    intros z_homo.
    assert (homogeneous (0 · 0)) as z_homo2.
    {
        rewrite scalar_lanni.
        exact z_homo.
    }
    assert ([_|z_homo] = [_|z_homo2]) as eq.
    {
        apply set_type_eq; cbn.
        rewrite scalar_lanni.
        reflexivity.
    }
    rewrite eq.
    rewrite (f_scalar_base _ _ _ z_homo).
    apply scalar_lanni.
Qed.

Theorem f_plus_base : ∀ u v H1 H2 H3,
        f_base [u + v|H1] = f_base [u|H2] + f_base [v|H3].
    intros u v uv_homo u_homo v_homo.
    classic_case (0 = u) as [u_z|u_nz].
    {
        subst u.
        rewrite linear_extend_zero_base.
        rewrite plus_lid.
        apply f_equal.
        apply set_type_eq; cbn.
        apply plus_lid.
    }
    classic_case (0 = v) as [v_z|v_nz].
    {
        subst v.
        rewrite linear_extend_zero_base.
        rewrite plus_rid.
        apply f_equal.
        apply set_type_eq; cbn.
        apply plus_rid.
    }
    pose proof u_homo as [i1 ui1].
    pose proof v_homo as [i2 vi2].
    assert (ex_val u_homo = i1) as i1_eq.
    {
        apply (of_grade_unique _ _ _ u_nz).
        -   exact (ex_proof u_homo).
        -   exact ui1.
    }
    assert (ex_val v_homo = i2) as i2_eq.
    {
        apply (of_grade_unique _ _ _ v_nz).
        -   exact (ex_proof v_homo).
        -   exact vi2.
    }
    assert (i1 = i2) as i_eq.
    {
        classic_contradiction contr.
        assert (grade_decomposition (u + v) =
            [u|u_homo] ::: [v|v_homo] ::: ulist_end) as uv_eq.
        {
            apply grade_decomposition_unique.
            -   do 2 rewrite ulist_image_add, ulist_sum_add.
                rewrite ulist_image_end, ulist_sum_end, plus_rid.
                reflexivity.
            -   do 2 rewrite ulist_image_add, ulist_unique_add.
                rewrite ulist_image_end.
                rewrite in_ulist_add.
                rewrite not_or.
                repeat split.
                +   cbn.
                    rewrite i1_eq, i2_eq.
                    rewrite neq_sym.
                    exact contr.
                +   apply in_ulist_end.
                +   apply in_ulist_end.
                +   apply ulist_unique_end.
            -   do 2 rewrite ulist_prop_add.
                repeat split.
                +   exact u_nz.
                +   exact v_nz.
                +   apply ulist_prop_end.
        }
        classic_case (0 = u + v) as [uv_z|uv_nz].
        -   rewrite <- uv_z in uv_eq.
            rewrite grade_decomposition_zero in uv_eq.
            assert (in_ulist ulist_end [u|u_homo]) as u_in.
            {
                rewrite uv_eq.
                rewrite in_ulist_add.
                left; reflexivity.
            }
            apply (in_ulist_end _ u_in).
        -   pose proof (grade_decomposition_homo [_|uv_homo] uv_nz) as uv_eq2.
            cbn in uv_eq2.
            rewrite uv_eq2 in uv_eq.
            assert (ulist_size ([u + v|uv_homo] ::: ulist_end) = 1) as eq1.
            {
                unfold ulist_size, ulist_end, ulist_add; equiv_simpl.
                reflexivity.
            }
            assert (ulist_size ([u|u_homo] ::: [v|v_homo] ::: ulist_end) = 2)
                as eq2.
            {
                unfold ulist_size, ulist_end, ulist_add; equiv_simpl.
                reflexivity.
            }
            rewrite uv_eq in eq1.
            rewrite eq1 in eq2.
            inversion eq2.
    }
    clear i2_eq.
    subst i2.
    pose proof (f_plus_base' _ _ _ ui1 vi2) as eq.
    rewrite (proof_irrelevance _ uv_homo) in eq.
    rewrite (proof_irrelevance _ u_homo) in eq.
    rewrite (proof_irrelevance _ v_homo) in eq.
    exact eq.
Qed.

Definition linear_extend (v : V1) :=
    ulist_sum (ulist_image (grade_decomposition v) f_base).

Let f := linear_extend.

Theorem linear_extend_zero : f 0 = 0.
    unfold f, linear_extend.
    rewrite grade_decomposition_zero.
    rewrite ulist_image_end.
    apply ulist_sum_end.
Qed.

Theorem linear_extend_plus : ∀ u v, f (u + v) = f u + f v.
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
            [a|a_homo] ::: grade_decomposition v) as eq.
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
            assert (homogeneous 0) as z_homo by (exists i; apply of_grade_zero).
            assert (homogeneous (a + grade_project v i)) as b_homo.
            {
                rewrite <- b_z.
                exact z_homo.
            }
            rewrite <- (f_plus_base _ _ b_homo).
            assert ([_|b_homo] = [_|z_homo]) as eq'.
            {
                apply set_type_eq; symmetry; exact b_z.
            }
            rewrite eq'.
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
            assert (grade_decomposition (a + v) = [_|b_homo] ::: l) as eq.
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
            rewrite <- (f_plus_base _ _ b_homo).
            reflexivity.
Qed.

Theorem linear_extend_scalar : ∀ a v, f (a · v) = a · f v.
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
    pose proof (homo_scalar a u (ex_intro _ i ui)) as au_homo.
    rewrite <- (f_scalar_base _ _ au_homo).
    classic_case (0 = a · u) as [au_z|au_nz].
    1: {
        assert (homogeneous 0) as z_homo by (exists i; apply of_grade_zero).
        assert ([_|au_homo] = [_|z_homo]) as eq
            by (apply set_type_eq; symmetry; exact au_z).
        rewrite eq.
        rewrite <- au_z.
        rewrite linear_extend_zero_base.
        rewrite grade_decomposition_zero.
        rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    }
    rewrite (grade_decomposition_homo [_|au_homo] au_nz).
    rewrite ulist_image_add, ulist_sum_add.
    rewrite ulist_image_end, ulist_sum_end.
    apply plus_rid.
Qed.

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
    @PlusLid V1 VP1 VZ1,
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

Context `{VG : @GradedSpace U V1 VP1 VPC1 VPA1 VZ1 SM1}.

Variable op : set_type homogeneous → set_type homogeneous → V2.
Variable op_ldist' : ∀ u v w i (H1 : of_grade i v) (H2 : of_grade i w),
    op u [v + w|ex_intro _ i (of_grade_plus v w i H1 H2)] =
    op u [v|ex_intro _ i H1] + op u [w|ex_intro _ i H2].
Variable op_rdist' : ∀ u v w i (H1 : of_grade i u) (H2 : of_grade i v),
    op [u + v|ex_intro _ i (of_grade_plus u v i H1 H2)] w =
    op [u|ex_intro _ i H1] w + op [v|ex_intro _ i H2] w.
Variable op_lscalar' : ∀ a u v i (H : of_grade i u),
    op [a · u|ex_intro _ i (of_grade_scalar a u i H)] v =
    a · op [u|ex_intro _ i H] v.
Variable op_rscalar' : ∀ a u v i (H : of_grade i v),
    op u [a · v|ex_intro _ i (of_grade_scalar a v i H)] =
    a · op u [v|ex_intro _ i H].

Lemma op_ldist : ∀ u v w H1 H2 H3, op u [v + w|H1] = op u [v|H2] + op u [w|H3].
    intros u v w vw_homo v_homo w_homo.
    apply f_plus_base.
    -   apply op_ldist'.
    -   intros; apply op_rscalar'.
Qed.

Lemma op_rdist : ∀ u v w H1 H2 H3, op [u + v|H1] w = op [u|H2] w + op [v|H3] w.
    intros u v w uv_homo u_homo v_homo.
    pose (op' a b := op b a).
    change (op [_|uv_homo] w) with (op' w [_|uv_homo]).
    change (op [_|u_homo] w) with (op' w [_|u_homo]).
    change (op [_|v_homo] w) with (op' w [_|v_homo]).
    apply f_plus_base; unfold op'.
    -   intros; apply op_rdist'.
    -   intros; apply op_lscalar'.
Qed.

Lemma op_lscalar : ∀ a u v H1 H2, op [a · u|H1] v = a · op [u|H2] v.
    intros a u v au_homo u_homo.
    pose (op' a b := op b a).
    change (op [_|au_homo] v) with (op' v [_|au_homo]).
    change (op [_|u_homo] v) with (op' v [_|u_homo]).
    apply f_scalar_base.
    intros; apply op_lscalar'.
Qed.

Lemma op_rscalar : ∀ a u v H1 H2, op u [a · v|H1] = a · op u [v|H2].
    intros a u v av_homo v_homo.
    apply f_scalar_base.
    intros; apply op_rscalar'.
Qed.

Lemma bilinear_extend_lanni_base : ∀ v H, op [0|H] v = 0.
    intros v z_homo.
    assert (homogeneous (0 · 0)) as z_homo2.
    {
        rewrite scalar_lanni.
        exact z_homo.
    }
    assert ([_|z_homo] = [_|z_homo2]) as eq.
    {
        apply set_type_eq; cbn.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite eq.
    rewrite (op_lscalar _ _ _ _ z_homo).
    apply scalar_lanni.
Qed.

Lemma bilinear_extend_ranni_base : ∀ v H, op v [0|H] = 0.
    intros v z_homo.
    assert (homogeneous (0 · 0)) as z_homo2.
    {
        rewrite scalar_lanni.
        exact z_homo.
    }
    assert ([_|z_homo] = [_|z_homo2]) as eq.
    {
        apply set_type_eq; cbn.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite eq.
    rewrite (op_rscalar _ _ _ _ z_homo).
    apply scalar_lanni.
Qed.

Section BilinearBase.

Variable a : set_type homogeneous.

Let f1_base := op a.

Lemma bilinear_extend_base_plus : ∀ (u v : V1) (i : grade_I)
        (H1 : of_grade i u) (H2 : of_grade i v),
        f1_base [u + v|ex_intro _ i (of_grade_plus u v i H1 H2)] =
        f1_base [u|ex_intro _ i H1] + f1_base [v|ex_intro _ i H2].
    intros u v i iu iv.
    unfold f1_base.
    apply op_ldist.
Qed.

Lemma bilinear_extend_base_scalar : ∀ a v i (H : of_grade i v),
        f1_base [a · v|ex_intro _ i (of_grade_scalar a v i H)] =
        a · f1_base [v|ex_intro _ i H].
    intros α v i iv.
    unfold f1_base.
    apply op_rscalar.
Qed.

Definition bilinear_extend_base := linear_extend f1_base.

End BilinearBase.

Let TP := linear_trans_plus V1 V2.
Let TZ := linear_trans_zero V1 V2.
Let TN := linear_trans_neg V1 V2.
Let TPC := linear_trans_plus_comm V1 V2.
Let TPA := linear_trans_plus_assoc V1 V2.
Let TPZ := linear_trans_plus_lid V1 V2.
Let TPN := linear_trans_plus_linv V1 V2.
Let TSM := linear_trans_scalar V1 V2.
Let TSMO := linear_trans_scalar_id V1 V2.
Let TSML := linear_trans_scalar_ldist V1 V2.
Let TSMR := linear_trans_scalar_rdist V1 V2.
Let TSMC := linear_trans_scalar_comp V1 V2.
Local Existing Instances TP TZ TN TPC TPA TPZ TPN TSM TSMO TSML TSMR TSMC.

Let f_base := bilinear_extend_base.

Lemma bilinear_extend_plus_base : ∀ (u v : V1) (i : grade_I)
        (H1 : of_grade i u) (H2 : of_grade i v),
        f_base [u + v|ex_intro _ i (of_grade_plus u v i H1 H2)] =
        f_base [u|ex_intro _ i H1] + f_base [v|ex_intro _ i H2].
    intros u v i iu iv.
    assert (homogeneous (u + v)) as uv_homo
        by (exists i; apply of_grade_plus; assumption).
    assert (homogeneous u) as u_homo by (exists i; exact iu).
    assert (homogeneous v) as v_homo by (exists i; exact iv).
    rewrite (proof_irrelevance _ uv_homo).
    rewrite (proof_irrelevance _ u_homo).
    rewrite (proof_irrelevance _ v_homo).
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
    rewrite (plus_comm _ (op _ a)).
    rewrite plus_assoc.
    apply rplus.
    clear IHl l.
    apply op_rdist.
Qed.

Lemma bilinear_extend_scalar_base : ∀ a v i (H : of_grade i v),
        f_base [a · v|ex_intro _ i (of_grade_scalar a v i H)] =
        a · f_base [v|ex_intro _ i H].
    intros a v i vi.
    assert (homogeneous (a · v)) as av_homo
        by (exists i; apply of_grade_scalar; exact vi).
    assert (homogeneous v) as v_homo by (exists i; exact vi).
    rewrite (proof_irrelevance _ av_homo).
    rewrite (proof_irrelevance _ v_homo).
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

Definition bilinear_extend := linear_extend f_base.
Let f := bilinear_extend.

Theorem bilinear_extend_ldist : ∀ u v w, f u (v + w) = f u v + f u w.
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
    rewrite (plus_comm _ (f_base a w)).
    rewrite plus_assoc.
    apply rplus.
    clear l u.
    unfold f_base, bilinear_extend_base.
    apply linear_extend_plus.
    -   apply bilinear_extend_base_plus.
    -   apply bilinear_extend_base_scalar.
Qed.

Theorem bilinear_extend_rdist : ∀ u v w, f (u + v) w = f u w + f v w.
    intros u v w.
    unfold f, bilinear_extend.
    rewrite linear_extend_plus.
    -   reflexivity.
    -   apply bilinear_extend_plus_base.
    -   apply bilinear_extend_scalar_base.
Qed.

Theorem bilinear_extend_lscalar : ∀ a u v, f (a · u) v = a · f u v.
    intros a u v.
    unfold f, bilinear_extend.
    rewrite linear_extend_scalar.
    -   reflexivity.
    -   apply bilinear_extend_plus_base.
    -   apply bilinear_extend_scalar_base.
Qed.

Theorem bilinear_extend_rscalar : ∀ a u v, f u (a · v) = a · f u v.
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
    -   apply bilinear_extend_base_plus.
    -   apply bilinear_extend_base_scalar.
Qed.

Theorem bilinear_extend_prod2 : ∀ u v,
        f u v = ulist_sum (ulist_prod2 op
            (grade_decomposition u) (grade_decomposition v)).
    intros u v.
    unfold f, bilinear_extend, linear_extend.
    remember (grade_decomposition u) as l.
    clear Heql u.
    induction l using ulist_induction.
    1: {
        rewrite ulist_image_end.
        rewrite ulist_prod2_lend.
        do 2 rewrite ulist_sum_end.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    unfold plus; cbn.
    rewrite ulist_prod2_ladd, ulist_sum_plus.
    rewrite IHl; clear IHl.
    apply rplus.
    clear l.
    unfold f_base, bilinear_extend_base.
    unfold linear_extend.
    remember (grade_decomposition v) as l.
    clear v Heql.
    induction l as [|b l] using ulist_induction.
    1: {
        do 2 rewrite ulist_image_end.
        reflexivity.
    }
    do 2 rewrite ulist_image_add, ulist_sum_add.
    rewrite IHl.
    reflexivity.
Qed.

Theorem bilinear_extend_lanni : ∀ v, f 0 v = 0.
    intros v.
    rewrite bilinear_extend_prod2.
    rewrite grade_decomposition_zero.
    rewrite ulist_prod2_lend.
    apply ulist_sum_end.
Qed.

Theorem bilinear_extend_ranni : ∀ v, f v 0 = 0.
    intros v.
    rewrite bilinear_extend_prod2.
    rewrite grade_decomposition_zero.
    rewrite ulist_prod2_rend.
    apply ulist_sum_end.
Qed.

Theorem bilinear_extend_homo : ∀ u v, f [u|] [v|] = op u v.
    intros [u u_homo] [v v_homo]; cbn.
    classic_case (0 = u) as [u_z|u_nz].
    2: classic_case (0 = v) as [v_z|v_nz].
    -   subst u.
        rewrite bilinear_extend_lanni_base.
        apply bilinear_extend_lanni.
    -   subst v.
        rewrite bilinear_extend_ranni_base.
        apply bilinear_extend_ranni.
    -   rewrite bilinear_extend_prod2.
        rewrite (grade_decomposition_homo [u|u_homo] u_nz).
        rewrite (grade_decomposition_homo [v|v_homo] v_nz).
        rewrite ulist_prod2_ladd.
        rewrite ulist_prod2_lend, ulist_conc_rid.
        rewrite ulist_image_add, ulist_sum_add.
        rewrite ulist_image_end, ulist_sum_end.
        apply plus_rid.
Qed.

End BilinearExtend.
