Require Import init.

Require Export linear_grade.
Require Import linear_subspace.
Require Export module_category.
Require Import algebra_category.
Require Import set.
Require Import unordered_list.

(** This maybe doesn't belong here, but oh well *)
Section SubspaceHomomorphism.

Context {F : CRingObj} {M N : ModuleObj F}.

Variable (f : cat_morphism (MODULE F) M N).

(* begin hide *)
Let U := cring_U F.
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Let V1 := module_V M.
Let VP1 := module_plus M.
Let VZ1 := module_zero M.
Let VN1 := module_neg M.
Let VPA1 := module_plus_assoc M.
Let VPC1 := module_plus_comm M.
Let VPZ1 := module_plus_lid M.
Let VPN1 := module_plus_linv M.
Let SM1 := module_scalar M.
Let SMO1 := module_scalar_id M.
Let SML1 := module_scalar_ldist M.
Let SMR1 := module_scalar_rdist M.
Let SMC1 := module_scalar_comp M.
Let V2 := module_V N.
Let VP2 := module_plus N.
Let VZ2 := module_zero N.
Let VN2 := module_neg N.
Let VPA2 := module_plus_assoc N.
Let VPC2 := module_plus_comm N.
Let VPZ2 := module_plus_lid N.
Let VPN2 := module_plus_linv N.
Let SM2 := module_scalar N.
Let SMO2 := module_scalar_id N.
Let SML2 := module_scalar_ldist N.
Let SMR2 := module_scalar_rdist N.
Let SMC2 := module_scalar_comp N.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP1 VZ1 VN1
    VPA1 VPC1 VPZ1 VPN1 SM1 SMO1 SML1 SMR1 SMC1 VP2 VZ2 VN2 VPA2 VPC2 VPZ2 VPN2
    SM2 SMO2 SML2 SMR2 SMC2.

(* end hide *)
Definition subspace_homo_set (S : Subspace U V1) y
    := ∃ x, subspace_set S x ∧ module_homo_f f x = y.

Lemma subspace_homo_zero : ∀ S, subspace_homo_set S 0.
Proof.
    intros S.
    unfold subspace_homo_set.
    exists 0.
    split.
    -   apply subspace_zero.
    -   apply module_homo_zero.
Qed.

Lemma subspace_homo_plus : ∀ S, ∀ a b,
    subspace_homo_set S a → subspace_homo_set S b →
    subspace_homo_set S (a + b).
Proof.
    intros S x y [a [Sa a_eq]] [b [Sb b_eq]].
    exists (a + b).
    split.
    -   apply subspace_plus; assumption.
    -   rewrite (module_homo_plus _ _ f).
        rewrite a_eq, b_eq.
        reflexivity.
Qed.

Lemma subspace_homo_scalar : ∀ S, ∀ a v,
    subspace_homo_set S v → subspace_homo_set S (a · v).
Proof.
    intros S a y [x [Sx x_eq]].
    exists (a · x).
    split.
    -   apply subspace_scalar.
        exact Sx.
    -   rewrite (module_homo_scalar _ _ f).
        rewrite x_eq.
        reflexivity.
Qed.

Definition subspace_homo S := make_subspace
    (subspace_homo_set S)
    (subspace_homo_zero S)
    (subspace_homo_plus S)
    (subspace_homo_scalar S).

End SubspaceHomomorphism.

(* begin hide *)
Section Grade.

(* end hide *)
Context {F : CRingObj} {M N : ModuleObj F}.

Variables (f : cat_morphism (MODULE F) M N) (f_iso : isomorphism f).

(* begin hide *)
Let U := cring_U F.
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Let V1 := module_V M.
Let VP1 := module_plus M.
Let VZ1 := module_zero M.
Let VN1 := module_neg M.
Let VPA1 := module_plus_assoc M.
Let VPC1 := module_plus_comm M.
Let VPZ1 := module_plus_lid M.
Let VPN1 := module_plus_linv M.
Let SM1 := module_scalar M.
Let SMO1 := module_scalar_id M.
Let SML1 := module_scalar_ldist M.
Let SMR1 := module_scalar_rdist M.
Let SMC1 := module_scalar_comp M.
Let V2 := module_V N.
Let VP2 := module_plus N.
Let VZ2 := module_zero N.
Let VN2 := module_neg N.
Let VPA2 := module_plus_assoc N.
Let VPC2 := module_plus_comm N.
Let VPZ2 := module_plus_lid N.
Let VPN2 := module_plus_linv N.
Let SM2 := module_scalar N.
Let SMO2 := module_scalar_id N.
Let SML2 := module_scalar_ldist N.
Let SMR2 := module_scalar_rdist N.
Let SMC2 := module_scalar_comp N.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP1 VZ1 VN1
    VPA1 VPC1 VPZ1 VPN1 SM1 SMO1 SML1 SMR1 SMC1 VP2 VZ2 VN2 VPA2 VPC2 VPZ2 VPN2
    SM2 SMO2 SML2 SMR2 SMC2.

(* end hide *)
Context `{VG : @GradedSpace U V1 VP1 VPC1 VPA1 VZ1 SM1}.

Let g := ex_val f_iso.

Lemma grade_iso_fg : ∀ x, module_homo_f f (module_homo_f g x) = x.
Proof.
    intros x.
    pose proof (land (ex_proof f_iso)) as eq.
    change (ex_type_val (ex_to_type f_iso)) with g in eq.
    cbn in eq.
    unfold module_homo_compose, module_homo_id in eq.
    inversion eq as [eq2].
    apply (func_eq _ _ eq2).
Qed.
Lemma grade_iso_gf : ∀ x, module_homo_f g (module_homo_f f x) = x.
Proof.
    intros x.
    pose proof (rand (ex_proof f_iso)) as eq.
    change (ex_type_val (ex_to_type f_iso)) with g in eq.
    cbn in eq.
    unfold module_homo_compose, module_homo_id in eq.
    inversion eq as [eq2].
    apply (func_eq _ _ eq2).
Qed.

Program Instance grade_isomorphism : GradedSpace U V2 := {
    grade_I := grade_I (V := V1);
    grade_subspace i := subspace_homo f (grade_subspace i);
}.
Next Obligation.
    rename H into neq.
    destruct H0 as [u1 [iu1 u1_eq]].
    destruct H1 as [u2 [ju2 u2_eq]].
    rewrite <- u2_eq in u1_eq.
    apply (f_equal (module_homo_f g)) in u1_eq.
    do 2 rewrite grade_iso_gf in u1_eq.
    subst u2.
    pose proof (grade_distinct i j neq u1 iu1 ju2) as u1_z.
    subst u1.
    rewrite <- u2_eq.
    symmetry; apply module_homo_zero.
Qed.
Next Obligation.
    pose (u := module_homo_f g v).
    pose proof (grade_decompose_ex u) as [l [u_eq u_in]].
    assert (∀ S : SubspaceVector U V1, subspace_homo_set f
        (sub_vector_sub S) (module_homo_f f (sub_vector_v S))) as S_in.
    {
        clear u v l u_eq u_in.
        intros [S v Sv]; cbn.
        exists v.
        split.
        -   exact Sv.
        -   reflexivity.
    }
    pose (Sf S := make_subspace_vector
        (subspace_homo f (sub_vector_sub S))
        (module_homo_f f (sub_vector_v S))
        (S_in S)).
    exists (ulist_image l Sf).
    split.
    -   rewrite ulist_image_comp.
        unfold Sf; cbn.
        apply (f_equal (module_homo_f f)) in u_eq.
        unfold u in u_eq.
        rewrite grade_iso_fg in u_eq.
        rewrite u_eq.
        clear u v u_eq u_in S_in Sf.
        induction l using ulist_induction.
        +   do 2 rewrite ulist_image_end, ulist_sum_end.
            apply module_homo_zero.
        +   do 2 rewrite ulist_image_add, ulist_sum_add.
            rewrite <- IHl.
            rewrite (module_homo_plus _ _ f).
            reflexivity.
    -   clear u_eq.
        induction l using ulist_induction.
        +   rewrite ulist_image_end.
            apply ulist_prop_end.
        +   unfold U, V1, V2, VP2, VZ2, SM2.
            rewrite ulist_image_add, ulist_prop_add.
            apply ulist_prop_add in u_in as [a_in u_in].
            split; [>|exact (IHl u_in)].
            unfold Sf; cbn; clear u_in S_in Sf IHl.
            destruct a_in as [i i_eq].
            exists i.
            apply predicate_ext.
            clear u v l.
            intros v; split; intros [u [u_in u_eq]].
            *   exists u.
                unfold U, V1, V2, VP1, VZ1, SM1, VP2, VZ2, SM2 in *.
                split.
                --  rewrite <- i_eq.
                    exact u_in.
                --  exact u_eq.
            *   exists u.
                unfold U, V1, V2, VP1, VZ1, SM1, VP2, VZ2, SM2 in *.
                split.
                --  rewrite i_eq.
                    exact u_in.
                --  exact u_eq.
Qed.
Next Obligation.
    rename H into l_in, H0 into l_uni, H1 into l_eq.
    assert (∀ S : SubspaceVector U V2, subspace_homo_set g
        (sub_vector_sub S) (module_homo_f g (sub_vector_v S))) as S_in.
    {
        intros [S v Sv]; cbn.
        exists v.
        split.
        -   exact Sv.
        -   reflexivity.
    }
    pose (Sg S := make_subspace_vector
        (subspace_homo g (sub_vector_sub S))
        (module_homo_f g (sub_vector_v S))
        (S_in S)).
    pose proof (grade_independent (ulist_image l Sg)) as l'_eq.
    prove_parts l'_eq.
    -   clear l_uni l_eq.
        induction l using ulist_induction.
        +   rewrite ulist_image_end.
            apply ulist_prop_end.
        +   rewrite ulist_image_add, ulist_prop_add.
            apply ulist_prop_add in l_in as [a_in l_in].
            split; [>clear IHl l_in|exact (IHl l_in)].
            unfold Sg; cbn; clear S_in Sg.
            destruct a_in as [i a_eq].
            exists i.
            apply predicate_ext.
            intros x; split; intros x_in.
            *   exists (module_homo_f f x).
                unfold U, V1, V2, VP1, VZ1, SM1, VP2, VZ2, SM2 in *.
                split.
                --  rewrite <- a_eq.
                    exists x.
                    split.
                    ++  exact x_in.
                    ++  reflexivity.
                --  apply grade_iso_gf.
            *   destruct x_in as [y [y_in y_eq]].
                unfold U, V1, V2, VP1, VZ1, SM1, VP2, VZ2, SM2 in *.
                subst x.
                rewrite <- a_eq in y_in.
                destruct y_in as [x [x_in x_eq]].
                rewrite <- x_eq.
                rewrite grade_iso_gf.
                exact x_in.
    -   clear l_in l_eq.
        rewrite ulist_image_comp; cbn.
        clear S_in Sg.
        induction l using ulist_induction.
        +   rewrite ulist_image_end.
            apply ulist_unique_end.
        +   rewrite ulist_image_add, ulist_unique_add.
            rewrite ulist_image_add, ulist_unique_add in l_uni.
            destruct l_uni as [a_nin l_uni].
            split; [>clear l_uni IHl|exact (IHl l_uni)].
            intros a_in; apply a_nin; clear a_nin.
            apply image_in_ulist in a_in as [b [b_eq b_in]].
            assert (subspace_set (sub_vector_sub a) =
                    subspace_set (sub_vector_sub b)) as eq.
            {
                assert (∀ a b,
                    subspace_homo_set g (sub_vector_sub a) =
                    subspace_homo_set g (sub_vector_sub b) →
                    ∀ x, subspace_set (sub_vector_sub a) x →
                         subspace_set (sub_vector_sub b) x) as wlog.
                {
                    clear a b b_eq b_in.
                    intros a b b_eq x x_in.
                    assert (subspace_homo_set g
                        (sub_vector_sub a) (module_homo_f g x)) as x_in'.
                    {
                        exists x.
                        split.
                        -   exact x_in.
                        -   reflexivity.
                    }
                    unfold U, V1, V2, VP1, VZ1, SM1, VP2, VZ2, SM2 in *.
                    rewrite b_eq in x_in'.
                    destruct x_in' as [y [y_in y_eq]].
                    apply (f_equal (module_homo_f f)) in y_eq.
                    do 2 rewrite grade_iso_fg in y_eq.
                    subst y.
                    exact y_in.
                }
                apply predicate_ext; intros x.
                split; intros x_in.
                -   symmetry in b_eq.
                    exact (wlog a b b_eq x x_in).
                -   exact (wlog b a b_eq x x_in).
            }
            rewrite eq.
            apply (in_ulist_image l b).
            exact b_in.
    -   clear l_in l_uni.
        rewrite <- (module_homo_zero g).
        unfold VZ1, VZ2 in *.
        unfold U, V1, V2, VP1, VZ1, SM1, VP2, VZ2, SM2 in *.
        rewrite l_eq.
        clear l_eq.
        rewrite ulist_image_comp; cbn.
        clear S_in Sg.
        induction l using ulist_induction.
        +   do 2 rewrite ulist_image_end, ulist_sum_end.
            apply module_homo_zero.
        +   do 2 rewrite ulist_image_add, ulist_sum_add.
            rewrite <- IHl; clear IHl.
            apply module_homo_plus.
    -   clear l_in l_uni l_eq.
        induction l using ulist_induction.
        +   apply ulist_prop_end.
        +   rewrite ulist_prop_add.
            rewrite ulist_image_add, ulist_prop_add in l'_eq.
            destruct l'_eq as [a_z l_z].
            split; [>clear l_z IHl|exact (IHl l_z)].
            cbn in a_z.
            apply (f_equal (module_homo_f f)) in a_z.
            rewrite grade_iso_fg in a_z.
            rewrite module_homo_zero in a_z.
            exact a_z.
Qed.

(* begin hide *)
End Grade.

Section GradeAlgebraObj.

Context {F : CRingObj} {M N : AlgebraObj F}.

Variables (f : cat_morphism (ALGEBRA F) M N) (f_iso : isomorphism f).

Let U := cring_U F.
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Let V1 := algebra_V M.
Let VP1 := algebra_plus M.
Let VZ1 := algebra_zero M.
Let VN1 := algebra_neg M.
Let VPA1 := algebra_plus_assoc M.
Let VPC1 := algebra_plus_comm M.
Let VPZ1 := algebra_plus_lid M.
Let VPN1 := algebra_plus_linv M.
Let SM1 := algebra_scalar M.
Let SMO1 := algebra_scalar_id M.
Let SML1 := algebra_scalar_ldist M.
Let SMR1 := algebra_scalar_rdist M.
Let SMC1 := algebra_scalar_comp M.
Let VM1 := algebra_mult M.
Let V2 := algebra_V N.
Let VP2 := algebra_plus N.
Let VZ2 := algebra_zero N.
Let VN2 := algebra_neg N.
Let VPA2 := algebra_plus_assoc N.
Let VPC2 := algebra_plus_comm N.
Let VPZ2 := algebra_plus_lid N.
Let VPN2 := algebra_plus_linv N.
Let SM2 := algebra_scalar N.
Let SMO2 := algebra_scalar_id N.
Let SML2 := algebra_scalar_ldist N.
Let SMR2 := algebra_scalar_rdist N.
Let SMC2 := algebra_scalar_comp N.
Let VM2 := algebra_mult N.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP1 VZ1 VN1
    VPA1 VPC1 VPZ1 VPN1 SM1 SMO1 SML1 SMR1 SMC1 VM1 VP2 VZ2 VN2 VPA2 VPC2 VPZ2
    VPN2 SM2 SMO2 SML2 SMR2 SMC2 VM2.
(* end hide *)
Context `{VG : @GradedSpace U V1 VP1 VPC1 VPA1 VZ1 SM1}.
Context `{IP : Plus grade_I}.
Context `{GA : @GradedAlgebraObj U V1 VP1 VPC1 VPA1 VZ1 SM1 VG IP VM1}.
(* begin hide *)
Let VG2 := grade_isomorphism
    (algebra_to_module_homomorphism f)
    (algebra_to_module_iso f f_iso).
Existing Instance VG2.
(* end hide *)
Program Instance graded_algebra_isomorphism : GradedAlgebraObj U V2.
Next Obligation.
    destruct H as [a [a_in a_eq]].
    destruct H0 as [b [b_in b_eq]].
    exists (a * b).
    split.
    -   apply grade_mult.
        +   exact a_in.
        +   exact b_in.
    -   cbn in *.
        rewrite (algebra_homo_mult _ _ f).
        rewrite a_eq, b_eq.
        reflexivity.
Qed.
(* begin hide *)

End GradeAlgebraObj.
(* end hide *)
