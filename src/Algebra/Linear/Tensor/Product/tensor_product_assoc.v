Require Import init.

Require Import linear_bilinear.
Require Import tensor_product_universal.

Require Import set.
Require Import unordered_list.

Require Import module_category.

(* begin hide *)
Section TensorProductIsomorphisms.

(* end hide *)
Context {F : CRingObj} (M N O : ModuleObj F).

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
Let V3 := module_V O.
Let VP3 := module_plus O.
Let VZ3 := module_zero O.
Let VN3 := module_neg O.
Let VPA3 := module_plus_assoc O.
Let VPC3 := module_plus_comm O.
Let VPZ3 := module_plus_lid O.
Let VPN3 := module_plus_linv O.
Let SM3 := module_scalar O.
Let SMO3 := module_scalar_id O.
Let SML3 := module_scalar_ldist O.
Let SMR3 := module_scalar_rdist O.
Let SMC3 := module_scalar_comp O.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP1 VZ1 VN1
    VPA1 VPC1 VPZ1 VPN1 SM1 SMO1 SML1 SMR1 SMC1 VP2 VZ2 VN2 VPA2 VPC2 VPZ2 VPN2
    SM2 SMO2 SML2 SMR2 SMC2 VP3 VZ3 VN3 VPA3 VPC3 VPZ3 VPN3 SM3 SMO3 SML3 SMR3
    SMC3.

(* end hide *)
(* begin show *)
Local Infix "⊗12" := (tensor_mult M N) (at level 40, left associativity).
Local Infix "⊗23" := (tensor_mult N O) (at level 40, left associativity).
Local Infix "⊗1_23" := (tensor_mult M (tensor_product N O)) (at level 40, left associativity).
Local Infix "⊗12_3" := (tensor_mult (tensor_product M N) O) (at level 40, left associativity).
(* end show *)

(* begin hide *)
Let V12 := tensor_product M N.
Let V23 := tensor_product N O.
Let V1_23 := tensor_product M V23.
Let V12_3 := tensor_product V12 O.
Let T1_23_plus := module_plus V1_23.
Let T1_23_scalar := module_scalar V1_23.
Let T12_3_plus := module_plus V12_3.
Let T12_3_scalar := module_scalar V12_3.
Existing Instances T1_23_plus T1_23_scalar T12_3_plus T12_3_scalar.

(* end hide *)
Theorem tensor_product_assoc :
    ∃ f : morphism
            (tensor_product M (tensor_product N O))
            (tensor_product (tensor_product M N) O),
        isomorphism f ∧
        ∀ a b c, f (a ⊗1_23 (b ⊗23 c)) = (a ⊗12 b) ⊗12_3 c.
Proof.
    pose (T12_plus := module_plus V12).
    pose (T12_zero := module_zero V12).
    pose (T12_neg := module_neg V12).
    pose (T12_plus_comm := module_plus_comm V12).
    pose (T12_plus_assoc := module_plus_assoc V12).
    pose (T12_plus_lid := module_plus_lid V12).
    pose (T12_plus_linv := module_plus_linv V12).
    pose (T12_scalar := module_scalar V12).
    pose (T12_scalar_comp := module_scalar_comp V12).
    pose (T12_scalar_id := module_scalar_id V12).
    pose (T12_scalar_ldist := module_scalar_ldist V12).
    pose (T12_scalar_rdist := module_scalar_rdist V12).
    pose (T23_plus := module_plus V23).
    pose (T23_zero := module_zero V23).
    pose (T23_neg := module_neg V23).
    pose (T23_plus_comm := module_plus_comm V23).
    pose (T23_plus_assoc := module_plus_assoc V23).
    pose (T23_plus_lid := module_plus_lid V23).
    pose (T23_plus_linv := module_plus_linv V23).
    pose (T23_scalar := module_scalar V23).
    pose (T23_scalar_comp := module_scalar_comp V23).
    pose (T23_scalar_id := module_scalar_id V23).
    pose (T23_scalar_ldist := module_scalar_ldist V23).
    pose (T23_scalar_rdist := module_scalar_rdist V23).
    pose (T1_23_zero := module_zero V1_23).
    pose (T1_23_neg := module_neg V1_23).
    pose (T1_23_plus_comm := module_plus_comm V1_23).
    pose (T1_23_plus_assoc := module_plus_assoc V1_23).
    pose (T1_23_plus_lid := module_plus_lid V1_23).
    pose (T1_23_plus_linv := module_plus_linv V1_23).
    pose (T1_23_scalar_comp := module_scalar_comp V1_23).
    pose (T1_23_scalar_id := module_scalar_id V1_23).
    pose (T1_23_scalar_ldist := module_scalar_ldist V1_23).
    pose (T1_23_scalar_rdist := module_scalar_rdist V1_23).
    pose (T12_3_zero := module_zero V12_3).
    pose (T12_3_neg := module_neg V12_3).
    pose (T12_3_plus_comm := module_plus_comm V12_3).
    pose (T12_3_plus_assoc := module_plus_assoc V12_3).
    pose (T12_3_plus_lid := module_plus_lid V12_3).
    pose (T12_3_plus_linv := module_plus_linv V12_3).
    pose (T12_3_scalar_comp := module_scalar_comp V12_3).
    pose (T12_3_scalar_id := module_scalar_id V12_3).
    pose (T12_3_scalar_ldist := module_scalar_ldist V12_3).
    pose (T12_3_scalar_rdist := module_scalar_rdist V12_3).
    pose (f1 a b c := (a ⊗12 b) ⊗12_3 c).
    assert (∀ a, bilinear (f1 a)) as f1_bil.
    {
        intros v.
        unfold f1.
        repeat split; intros.
        -   rewrite (tensor_rscalar M N).
            rewrite tensor_lscalar.
            reflexivity.
        -   rewrite (tensor_rscalar _ O).
            reflexivity.
        -   rewrite (tensor_ldist M N).
            rewrite tensor_rdist.
            reflexivity.
        -   rewrite (tensor_ldist _ O).
            reflexivity.
    }
    pose (f2_base a := make_bilinear _ _ _ _ (f1_bil a)).
    pose (f2 a := ex_singleton (tensor_product_universal _ _ (f2_base a))).
    cbn in f2.
    pose (f3 a b := [f2 a|] b).
    assert (bilinear f3) as f3_bil.
    {
        repeat split; intros.
        -   unfold f3.
            unfold f2.
            destruct (ex_singleton _) as [fav fav_in].
            destruct (ex_singleton _) as [fv fv_in]; cbn.
            unfold bilinear_from_set in fav_in, fv_in.
            cbn in fav, fav_in, fv, fv_in.
            pose proof (tensor_sum _ _ v2) as [l v2_eq]; subst v2.
            induction l using ulist_induction.
            +   rewrite ulist_image_end, ulist_sum_end.
                do 2 rewrite module_homo_zero.
                rewrite scalar_ranni.
                reflexivity.
            +   rewrite ulist_image_add, ulist_sum_add.
                rewrite (@module_homo_plus _ _ _ fav).
                rewrite (@module_homo_plus _ _ _ fv).
                rewrite scalar_ldist.
                rewrite <- IHl.
                apply rplus.
                destruct a0 as [a0 [u [v eq]]]; subst a0; cbn.
                unfold tensor_mult; cbn.
                rewrite fav_in, fv_in.
                unfold f1.
                rewrite (tensor_lscalar M N).
                rewrite tensor_lscalar.
                reflexivity.
        -   unfold f3.
            apply (@module_homo_scalar _ _ _ [f2 v1|]).
        -   unfold f3.
            unfold f2.
            destruct (ex_singleton _) as [fv12 fv12_in].
            destruct (ex_singleton _) as [fv1 fv1_in].
            destruct (ex_singleton _) as [fv2 fv2_in].
            cbn.
            unfold bilinear_from_set in fv12_in, fv1_in, fv2_in.
            cbn in fv12, fv12_in, fv1, fv1_in, fv2, fv2_in.
            pose proof (tensor_sum _ _ v3) as [l v3_eq]; subst v3.
            induction l using ulist_induction.
            +   rewrite ulist_image_end, ulist_sum_end.
                do 3 rewrite module_homo_zero.
                rewrite plus_lid.
                reflexivity.
            +   rewrite ulist_image_add, ulist_sum_add.
                rewrite (@module_homo_plus _ _ _ fv12).
                rewrite (@module_homo_plus _ _ _ fv1).
                rewrite (@module_homo_plus _ _ _ fv2).
                rewrite IHl; clear IHl.
                do 2 rewrite plus_assoc.
                apply rplus.
                rewrite plus_comm.
                rewrite (plus_comm (fv1 [a|])).
                rewrite <- plus_assoc.
                apply lplus.
                destruct a as [a [u [v eq]]]; subst a; cbn.
                unfold tensor_mult; rewrite fv12_in, fv1_in, fv2_in.
                unfold f1.
                rewrite (tensor_rdist M N).
                rewrite tensor_rdist.
                reflexivity.
        -   unfold f3.
            apply (@module_homo_plus _ _ _ [f2 v1|]).
    }
    pose (f_base := make_bilinear _ _ _ _ f3_bil).
    pose proof (tensor_product_universal _ _ f_base) as f_ex.
    apply ex_singleton in f_ex as [f f_in].
    cbn in f.
    unfold bilinear_from_set in f_in; cbn in f_in.
    clear f_base.
    exists f.
    split.
    -   pose (g1 c a b := a ⊗1_23 (b ⊗23 c)).
        assert (∀ c, bilinear (g1 c)) as g1_bil.
        {
            intros v.
            unfold g1.
            repeat split; intros.
            -   apply tensor_lscalar.
            -   rewrite (tensor_lscalar N O).
                rewrite tensor_rscalar.
                reflexivity.
            -   apply tensor_rdist.
            -   rewrite (tensor_rdist N O).
                rewrite tensor_ldist.
                reflexivity.
        }
        pose (g2_base c := make_bilinear _ _ _ _ (g1_bil c)).
        pose (g2 c := ex_singleton (tensor_product_universal _ _ (g2_base c))).
        cbn in g2.
        pose (g3 b a := [g2 a|] b).
        assert (bilinear g3) as g3_bil.
        {
            repeat split; intros.
            -   unfold g3.
                apply (@module_homo_scalar _ _ _ [g2 v2|]).
            -   unfold g3.
                unfold g2.
                destruct (ex_singleton _) as [gav gav_in].
                destruct (ex_singleton _) as [gv gv_in]; cbn.
                unfold bilinear_from_set in gav_in, gv_in.
                cbn in gav, gav_in, gv, gv_in.
                pose proof (tensor_sum _ _ v1) as [l v1_eq]; subst v1.
                induction l using ulist_induction.
                +   rewrite ulist_image_end, ulist_sum_end.
                    do 2 rewrite module_homo_zero.
                    rewrite scalar_ranni.
                    reflexivity.
                +   rewrite ulist_image_add, ulist_sum_add.
                    rewrite (@module_homo_plus _ _ _ gav).
                    rewrite (@module_homo_plus _ _ _ gv).
                    rewrite scalar_ldist.
                    rewrite <- IHl.
                    apply rplus.
                    destruct a0 as [a0 [u [v eq]]]; subst a0; cbn.
                    unfold tensor_mult; cbn.
                    rewrite gav_in, gv_in.
                    unfold g1.
                    rewrite (tensor_rscalar N O).
                    rewrite tensor_rscalar.
                    reflexivity.
            -   unfold g3.
                apply (@module_homo_plus _ _ _ [g2 v3|]).
            -   unfold g3.
                unfold g2.
                destruct (ex_singleton _) as [gv12 gv12_in].
                destruct (ex_singleton _) as [gv1 gv1_in].
                destruct (ex_singleton _) as [gv2 gv2_in].
                cbn.
                unfold bilinear_from_set in gv12_in, gv1_in, gv2_in.
                cbn in gv12, gv12_in, gv1, gv1_in, gv2, gv2_in.
                pose proof (tensor_sum _ _ v1) as [l v1_eq]; subst v1.
                induction l using ulist_induction.
                +   rewrite ulist_image_end, ulist_sum_end.
                    do 3 rewrite module_homo_zero.
                    rewrite plus_lid.
                    reflexivity.
                +   rewrite ulist_image_add, ulist_sum_add.
                    rewrite (@module_homo_plus _ _ _ gv12).
                    rewrite (@module_homo_plus _ _ _ gv1).
                    rewrite (@module_homo_plus _ _ _ gv2).
                    rewrite IHl; clear IHl.
                    do 2 rewrite plus_assoc.
                    apply rplus.
                    rewrite plus_comm.
                    rewrite (plus_comm (gv1 [a|])).
                    rewrite <- plus_assoc.
                    apply lplus.
                    destruct a as [a [u [v eq]]]; subst a; cbn.
                    unfold tensor_mult; rewrite gv12_in, gv1_in, gv2_in.
                    unfold g1.
                    rewrite (tensor_ldist N O).
                    apply tensor_ldist.
        }
        pose (g_base := make_bilinear _ _ _ _ g3_bil).
        pose proof (tensor_product_universal _ _ g_base) as g_ex.
        apply ex_singleton in g_ex as [g g_in].
        cbn in g.
        unfold bilinear_from_set in g_in; cbn in g_in.
        clear g_base.
        exists g.
        cbn.
        unfold module_homo_compose, module_homo_id; cbn.
        split; apply module_homomorphism_eq; cbn.
        +   intros x.
            pose proof (tensor_sum _ _ x) as [l1 x_eq]; subst x.
            induction l1 using ulist_induction.
            *   rewrite ulist_image_end, ulist_sum_end.
                do 2 rewrite module_homo_zero.
                reflexivity.
            *   rewrite ulist_image_add, ulist_sum_add.
                rewrite (@module_homo_plus _ _ _ g).
                rewrite (@module_homo_plus _ _ _ f).
                rewrite <- IHl1 at 2.
                apply rplus.
                destruct a as [a [u [v a_eq]]]; subst a; cbn.
                unfold tensor_mult at 1; rewrite g_in.
                unfold g3.
                unfold g2.
                destruct (ex_singleton _) as [h h_in]; cbn.
                unfold bilinear_from_set in h_in.
                pose proof (tensor_sum _ _ u) as [l2 u_eq]; subst u.
                induction l2 using ulist_induction.
                --  rewrite ulist_image_end, ulist_sum_end.
                    rewrite tensor_product_lanni.
                    do 2 rewrite module_homo_zero.
                    reflexivity.
                --  rewrite ulist_image_add, ulist_sum_add.
                    rewrite (@module_homo_plus _ _ _ h).
                    rewrite (@module_homo_plus _ _ _ f).
                    rewrite tensor_rdist.
                    rewrite IHl2.
                    apply rplus.
                    destruct a as [a [u' [v' eq]]]; subst a.
                    cbn.
                    unfold tensor_mult at 1; rewrite h_in.
                    unfold g2_base; cbn.
                    unfold g1.
                    unfold tensor_mult at 1 2; rewrite f_in.
                    unfold f3, f2.
                    destruct (ex_singleton _) as [h' h'_in]; cbn.
                    unfold bilinear_from_set in h'_in; cbn in h', h'_in.
                    rewrite h'_in.
                    unfold f1.
                    reflexivity.
        +   intros x.
            pose proof (tensor_sum _ _ x) as [l x_eq]; subst x.
            induction l using ulist_induction.
            *   rewrite ulist_image_end, ulist_sum_end.
                do 2 rewrite module_homo_zero.
                reflexivity.
            *   rewrite ulist_image_add, ulist_sum_add.
                rewrite (@module_homo_plus _ _ _ f).
                rewrite (@module_homo_plus _ _ _ g).
                rewrite <- IHl at 2.
                apply rplus.
                destruct a as [a [u [v a_eq]]]; subst a; cbn.
                unfold tensor_mult at 1; rewrite f_in.
                unfold f3, f2.
                destruct (ex_singleton _) as [h h_in]; cbn.
                unfold bilinear_from_set in h_in.
                pose proof (tensor_sum _ _ v) as [l2 v_eq]; subst v.
                induction l2 using ulist_induction.
                --  rewrite ulist_image_end, ulist_sum_end.
                    rewrite tensor_product_ranni.
                    do 2 rewrite module_homo_zero.
                    reflexivity.
                --  rewrite ulist_image_add, ulist_sum_add.
                    rewrite (@module_homo_plus _ _ _ h).
                    rewrite (@module_homo_plus _ _ _ g).
                    rewrite tensor_ldist.
                    rewrite IHl2.
                    apply rplus.
                    destruct a as [a [u' [v' eq]]]; subst a.
                    cbn.
                    unfold tensor_mult at 1; rewrite h_in.
                    unfold f2_base; cbn.
                    unfold f1.
                    unfold tensor_mult at 1 2; rewrite g_in.
                    unfold g3, g2.
                    destruct (ex_singleton _) as [h' h'_in]; cbn.
                    unfold bilinear_from_set in h'_in; cbn in h'_in.
                    rewrite h'_in.
                    unfold g1.
                    reflexivity.
    -   intros a b c.
        unfold tensor_mult at 1 2.
        rewrite f_in.
        unfold f3, f2.
        destruct (ex_singleton _) as [fa fa_in]; cbn.
        unfold bilinear_from_set in fa_in.
        rewrite fa_in.
        reflexivity.
Qed.

Definition tensor_product_assoc_homo := ex_val tensor_product_assoc.
Definition tensor_product_assoc_f := module_homo_f tensor_product_assoc_homo.
Let af := tensor_product_assoc_f.

Theorem tensor_product_assoc_eq :
    ∀ a b c, af (a ⊗1_23 (b ⊗23 c)) = (a ⊗12 b) ⊗12_3 c.
Proof.
    apply (ex_proof tensor_product_assoc).
Qed.

Theorem tensor_product_assoc_plus : ∀ a b, af (a + b) = af a + af b.
Proof.
    apply (@module_homo_plus _ _ _ (ex_val tensor_product_assoc)).
Qed.
Theorem tensor_product_assoc_scalar : ∀ a v, af (a · v) = a · af v.
Proof.
    apply (@module_homo_scalar _ _ _ (ex_val tensor_product_assoc)).
Qed.

Theorem tensor_product_assoc_iso : isomorphism tensor_product_assoc_homo.
Proof.
    apply (ex_proof tensor_product_assoc).
Qed.

Theorem tensor_product_assoc_bij : Bijective af.
Proof.
    pose proof (land (ex_proof tensor_product_assoc))
        as [[g g_plus g_scalar] [fg gf]].
    cbn in *.
    unfold module_homo_compose, module_homo_id in *; cbn in *.
    inversion fg as [fg']; clear fg.
    inversion gf as [gf']; clear gf.
    apply (inverse_ex_bijective af g); split.
    -   apply func_eq.
        exact fg'.
    -   apply func_eq.
        exact gf'.
Qed.

Definition tensor_product_assoc_inv_homo
    := ex_val (land (ex_proof tensor_product_assoc)).
Definition tensor_product_assoc_inv_f
    := module_homo_f tensor_product_assoc_inv_homo.

Let af' := tensor_product_assoc_inv_f.

Theorem tensor_product_assoc_inv_eq :
    ∀ a b c, af' ((a ⊗12 b) ⊗12_3 c) = a ⊗1_23 (b ⊗23 c).
Proof.
    intros a b c.
    unfold af', tensor_product_assoc_inv_f, tensor_product_assoc_inv_homo.
    rewrite_ex_val f [fg gf].
    destruct (ex_to_type _) as [g [g_iso g_eq]]; cbn in *.
    unfold module_homo_compose, module_homo_id in gf; cbn in gf.
    inversion gf as [gf']; clear gf.
    pose proof (func_eq _ _ gf') as gf; clear gf'; cbn in gf.
    rewrite <- gf.
    apply f_equal.
    rewrite g_eq.
    reflexivity.
Qed.

Theorem tensor_product_assoc_inv_plus : ∀ a b, af' (a + b) = af' a + af' b.
Proof.
    apply (@module_homo_plus _ _ _ tensor_product_assoc_inv_homo).
Qed.
Theorem tensor_product_assoc_inv_scalar : ∀ a v, af' (a · v) = a · af' v.
Proof.
    apply (@module_homo_scalar _ _ _ tensor_product_assoc_inv_homo).
Qed.

Theorem tensor_product_assoc_inv_iso : isomorphism tensor_product_assoc_inv_homo.
Proof.
    unfold af', tensor_product_assoc_inv_f, tensor_product_assoc_inv_homo.
    rewrite_ex_val f fg.
    destruct (ex_to_type _) as [g [g_iso g_eq]]; cbn in *.
    exists g.
    cbn.
    split; apply fg.
Qed.

Theorem tensor_product_assoc_inv_bij : Bijective af'.
Proof.
    pose proof tensor_product_assoc_inv_iso as [[g g_plus g_scalar] [fg gf]].
    unfold module_homo_compose, module_homo_id in *; cbn in *.
    inversion fg as [fg']; clear fg.
    inversion gf as [gf']; clear gf.
    apply (inverse_ex_bijective _ g); split.
    -   apply func_eq.
        exact fg'.
    -   apply func_eq.
        exact gf'.
Qed.
(* begin hide *)

End TensorProductIsomorphisms.
(* end hide *)
