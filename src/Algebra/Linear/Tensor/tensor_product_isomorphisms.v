Require Import init.

Require Import linear_bilinear.
Require Import tensor_product_universal.
Require Import plus_sum.

Require Import set.
Require Import unordered_list.
Require Import card.

Require Import module_category.

(* begin hide *)
Unset Keyed Unification.

Section TensorProductIsomorphisms.

(* end hide *)
Context {F : CRing} (M : Module F).

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
Let USM := module_scalar (cring_module F).
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP1 VZ1 VN1
    VPA1 VPC1 VPZ1 VPN1 SM1 SMO1 SML1 SMR1 SMC1 USM.

Local Infix "⊗" := (tensor_mult (cring_module F) M).

Let TU1_plus := module_plus (tensor_product (cring_module F) M).
Let TU1_scalar := module_scalar (tensor_product (cring_module F) M).

Existing Instances TU1_plus TU1_scalar.

(* end hide *)
Theorem tensor_product_lid :
    ∃ f : cat_morphism (MODULE F) (tensor_product (cring_module F) M) M,
        isomorphism f ∧ ∀ a v, module_homo_f f (a ⊗ v) = a · v.
    assert (bilinear (λ (a : U) (v : V1), a · v)) as f_bil.
    {
        repeat split; intros.
        -   rewrite scalar_comp.
            reflexivity.
        -   do 2 rewrite scalar_comp.
            rewrite mult_comm.
            reflexivity.
        -   apply scalar_rdist.
        -   apply scalar_ldist.
    }
    pose (f_base := make_bilinear (cring_module F) M _ (λ a (v : V1), a · v) f_bil).
    pose proof (tensor_product_universal _ _ f_base) as f_ex.
    apply card_one_ex in f_ex as [f f_in].
    cbn in *.
    unfold bilinear_from_set in f_in; cbn in f_in.
    clear f_base.
    exists f.
    split.
    -   pose (g v := 1 ⊗ v).
        assert (∀ u v, g (u + v) = g u + g v) as g_plus.
        {
            intros u v.
            unfold g.
            apply tensor_ldist.
        }
        assert (∀ a v, g (a · v) = a · g v) as g_scalar.
        {
            intros a v.
            unfold g.
            apply tensor_rscalar.
        }
        exists (make_module_homomorphism _ M _ g g_plus g_scalar).
        cbn.
        unfold module_homo_compose, module_homo_id; cbn.
        split; apply module_homomorphism_eq; cbn.
        +   intros x.
            unfold g.
            unfold tensor_mult; rewrite f_in.
            apply scalar_id.
        +   intros x.
            unfold g.
            pose proof (tensor_sum _ _ x) as [l eq]; subst x.
            induction l using ulist_induction.
            *   rewrite ulist_image_end, ulist_sum_end.
                rewrite module_homo_zero.
                apply tensor_product_ranni.
            *   rewrite ulist_image_add, ulist_sum_add.
                rewrite (@module_homo_plus _ _ _ f).
                rewrite tensor_ldist.
                rewrite <- IHl at 2; clear IHl.
                apply rplus.
                destruct a as [a [u [v eq]]]; subst a; cbn.
                unfold tensor_mult at 2; rewrite f_in.
                unfold V1, SM1.
                rewrite tensor_rscalar.
                rewrite <- tensor_lscalar.
                unfold scalar_mult; cbn.
                rewrite mult_rid.
                reflexivity.
    -   exact f_in.
Qed.

Definition tensor_product_lid_homo := ex_val tensor_product_lid.
Definition tensor_product_lid_f := module_homo_f tensor_product_lid_homo.
Let lf := tensor_product_lid_f.

Theorem tensor_product_lid_eq : ∀ a v, lf (a ⊗ v) = a · v.
    apply (ex_proof tensor_product_lid).
Qed.

Theorem tensor_product_lid_plus : ∀ a b, lf (a + b) = lf a + lf b.
    apply (@module_homo_plus _ _ _ tensor_product_lid_homo).
Qed.
Theorem tensor_product_lid_scalar : ∀ a v, lf (a · v) = a · lf v.
    apply (@module_homo_scalar _ _ _ tensor_product_lid_homo).
Qed.

Theorem tensor_product_lid_iso : isomorphism tensor_product_lid_homo.
    apply (ex_proof tensor_product_lid).
Qed.

Theorem tensor_product_lid_bij : bijective lf.
    pose proof (land (ex_proof tensor_product_lid))
        as [[g g_plus g_scalar] [fg gf]].
    cbn in *.
    unfold module_homo_compose, module_homo_id in *; cbn in *.
    inversion fg as [fg']; clear fg.
    inversion gf as [gf']; clear gf.
    apply (inverse_ex_bijective lf g).
    -   apply func_eq.
        exact fg'.
    -   apply func_eq.
        exact gf'.
Qed.

Context (N : Module F).
(* begin hide *)
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
Existing Instances VP2 VZ2 VN2 VPA2 VPC2 VPZ2 VPN2 SM2 SMO2 SML2 SMR2 SMC2.

(* end hide *)
Local Infix "⊗12" := (tensor_mult M N) (at level 40, left associativity).
Local Infix "⊗21" := (tensor_mult N M) (at level 40, left associativity).

(* begin hide *)
Let T12_plus := module_plus (tensor_product M N).
Let T12_scalar := module_scalar (tensor_product M N).
Let T21_plus := module_plus (tensor_product N M).
Let T21_scalar := module_scalar (tensor_product N M).
Existing Instances T12_plus T12_scalar T21_plus T21_scalar.

(* end hide *)
Theorem tensor_product_comm :
    ∃ f : cat_morphism (MODULE F) (tensor_product M N) (tensor_product N M),
        isomorphism f ∧ ∀ a b, module_homo_f f (a ⊗12 b) = b ⊗21 a.
    assert (bilinear (λ a b, b ⊗21 a)) as f_bil
        by (repeat split; intros; apply tensor_bilinear).
    pose (f_base := make_bilinear M N _ _ f_bil).
    pose proof (tensor_product_universal M N f_base) as f_ex.
    apply card_one_ex in f_ex as [f f_in].
    cbn in *.
    unfold bilinear_from_set in f_in; cbn in f_in.
    clear f_base.
    exists f.
    split.
    -   assert (bilinear (λ b a, a ⊗12 b)) as g_bil
            by (repeat split; intros; apply tensor_bilinear).
        pose (g_base := make_bilinear N M _ _ g_bil).
        pose proof (tensor_product_universal N M g_base) as g_ex.
        apply card_one_ex in g_ex as [g g_in].
        cbn in *.
        unfold bilinear_from_set in g_in; cbn in g_in.
        clear g_base.
        exists g.
        cbn.
        unfold module_homo_compose, module_homo_id; cbn.
        change (bilinear_from_f M N (tensor_bilinear_from M N)) with
            (tensor_mult M N) in f_in.
        change (bilinear_from_f N M (tensor_bilinear_from N M)) with
            (tensor_mult N M) in g_in.
        split; apply module_homomorphism_eq; cbn.
        +   intros x.
            pose proof (tensor_sum _ _ x) as [l x_eq]; subst x.
            induction l using ulist_induction.
            *   rewrite ulist_image_end, ulist_sum_end.
                rewrite <- (tensor_product_zero N M).
                rewrite g_in.
                rewrite f_in.
                reflexivity.
            *   rewrite ulist_image_add, ulist_sum_add.
                rewrite (@module_homo_plus _ _ _ g).
                rewrite (@module_homo_plus _ _ _ f).
                cbn in *.
                rewrite <- IHl at 2; clear IHl.
                apply rplus.
                destruct a as [a [u [v a_eq]]]; subst a; cbn.
                rewrite g_in.
                rewrite f_in.
                reflexivity.
        +   intros x.
            pose proof (tensor_sum _ _ x) as [l x_eq]; subst x.
            induction l using ulist_induction.
            *   rewrite ulist_image_end, ulist_sum_end.
                rewrite <- (tensor_product_zero M N).
                rewrite f_in.
                rewrite g_in.
                reflexivity.
            *   rewrite ulist_image_add, ulist_sum_add.
                rewrite (@module_homo_plus _ _ _ f).
                rewrite (@module_homo_plus _ _ _ g).
                cbn in *.
                rewrite <- IHl at 2; clear IHl.
                apply rplus.
                destruct a as [a [u [v a_eq]]]; subst a; cbn.
                rewrite f_in.
                rewrite g_in.
                reflexivity.
    -   exact f_in.
Qed.

Definition tensor_product_comm_homo := ex_val tensor_product_comm.
Definition tensor_product_comm_f := module_homo_f tensor_product_comm_homo.
Let cf := tensor_product_comm_f.

Theorem tensor_product_comm_eq : ∀ a b, cf (a ⊗12 b) = b ⊗21 a.
    apply (ex_proof tensor_product_comm).
Qed.

Theorem tensor_product_comm_plus : ∀ a b, cf (a + b) = cf a + cf b.
    apply (@module_homo_plus _ _ _ tensor_product_comm_homo).
Qed.
Theorem tensor_product_comm_scalar : ∀ a v, cf (a · v) = a · cf v.
    apply (@module_homo_scalar _ _ _ tensor_product_comm_homo).
Qed.

Theorem tensor_product_comm_iso : isomorphism tensor_product_comm_homo.
    apply (ex_proof tensor_product_comm).
Qed.

Theorem tensor_product_comm_bij : bijective cf.
    pose proof (land (ex_proof tensor_product_comm))
        as [[g g_plus g_scalar] [fg gf]].
    cbn in *.
    unfold module_homo_compose, module_homo_id in *; cbn in *.
    inversion fg as [fg']; clear fg.
    inversion gf as [gf']; clear gf.
    apply (inverse_ex_bijective cf g).
    -   apply func_eq.
        exact fg'.
    -   apply func_eq.
        exact gf'.
Qed.

(* begin hide *)
End TensorProductIsomorphisms.

Section TensorProductIsomorphism.

Context {F : CRing} (M : Module F).

Let U := cring_U.
Let UP := cring_plus.
Let UZ := cring_zero.
Let UN := cring_neg.
Let UPA := cring_plus_assoc.
Let UPC := cring_plus_comm.
Let UPZ := cring_plus_lid.
Let UPN := cring_plus_linv.
Let UM := cring_mult.
Let UO := cring_one.
Let UMA := cring_mult_assoc.
Let UMC := cring_mult_comm.
Let UMO := cring_mult_lid.
Let UMD := cring_ldist.
Let V := module_V M.
Let VP := module_plus M.
Let VZ := module_zero M.
Let VN := module_neg M.
Let VPA := module_plus_assoc M.
Let VPC := module_plus_comm M.
Let VPZ := module_plus_lid M.
Let VPN := module_plus_linv M.
Let SM := module_scalar M.
Let SMO := module_scalar_id M.
Let SML := module_scalar_ldist M.
Let SMR := module_scalar_rdist M.
Let SMC := module_scalar_comp M.
Let USM := module_scalar (cring_module F).
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP VZ VN
    VPA VPC VPZ VPN SM SMO SML SMR SMC USM.

Local Infix "⊗" := (tensor_mult M (cring_module F)).

Existing Instances scalar_scalar_mult.

Let TVU_plus := module_plus (tensor_product M (cring_module F)).
Let TVU_scalar := module_scalar (tensor_product M (cring_module F)).

Existing Instances TVU_plus TVU_scalar.

(* end hide *)
Definition tensor_product_rid_homo :=
    tensor_product_lid_homo M ∘ tensor_product_comm_homo M (cring_module F).
Definition tensor_product_rid_f := module_homo_f tensor_product_rid_homo.
Let f := tensor_product_rid_f.

Theorem tensor_product_rid_eq : ∀ a v, f (v ⊗ a) = a · v.
    intros a v.
    unfold f, tensor_product_rid_f.
    cbn.
    change (module_homo_f (tensor_product_lid_homo M)) with
        (tensor_product_lid_f M).
    change (module_homo_f (tensor_product_comm_homo M (cring_module F))) with
        (tensor_product_comm_f M (cring_module F)).
    rewrite tensor_product_comm_eq.
    rewrite tensor_product_lid_eq.
    reflexivity.
Qed.

Theorem tensor_product_rid_plus : ∀ a b, f (a + b) = f a + f b.
    intros a b.
    unfold f, tensor_product_rid_f.
    cbn.
    change (module_homo_f (tensor_product_lid_homo M)) with
        (tensor_product_lid_f M).
    change (module_homo_f (tensor_product_comm_homo M (cring_module F))) with
        (tensor_product_comm_f M (cring_module F)).
    rewrite (tensor_product_comm_plus M).
    rewrite tensor_product_lid_plus.
    reflexivity.
Qed.
Theorem tensor_product_rid_scalar : ∀ a v, f (a · v) = a · f v.
    intros a v.
    unfold f, tensor_product_rid_f.
    cbn.
    change (module_homo_f (tensor_product_lid_homo M)) with
        (tensor_product_lid_f M).
    change (module_homo_f (tensor_product_comm_homo M (cring_module F))) with
        (tensor_product_comm_f M (cring_module F)).
    rewrite (tensor_product_comm_scalar M).
    rewrite tensor_product_lid_scalar.
    reflexivity.
Qed.

Theorem tensor_product_rid_iso : isomorphism tensor_product_rid_homo.
    apply compose_isomorphism.
    -   apply tensor_product_lid_iso.
    -   apply tensor_product_comm_iso.
Qed.

Theorem tensor_product_rid_bij : bijective f.
    unfold f, tensor_product_rid_f.
    cbn.
    apply bij_comp.
    -   apply tensor_product_comm_bij.
    -   apply tensor_product_lid_bij.
Qed.

(* begin hide *)
End TensorProductIsomorphism.

Section TensorProductIsomorphism.

(* end hide *)
Context {F : CRing} (M1 M2 N1 N2 : Module F).

(* begin hide *)
Let U := cring_U.
Let UP := cring_plus.
Let UZ := cring_zero.
Let UN := cring_neg.
Let UPA := cring_plus_assoc.
Let UPC := cring_plus_comm.
Let UPZ := cring_plus_lid.
Let UPN := cring_plus_linv.
Let UM := cring_mult.
Let UO := cring_one.
Let UMA := cring_mult_assoc.
Let UMC := cring_mult_comm.
Let UMO := cring_mult_lid.
Let UMD := cring_ldist.
Let V11 := module_V M1.
Let VP11 := module_plus M1.
Let VZ11 := module_zero M1.
Let VN11 := module_neg M1.
Let VPA11 := module_plus_assoc M1.
Let VPC11 := module_plus_comm M1.
Let VPZ11 := module_plus_lid M1.
Let VPN11 := module_plus_linv M1.
Let SM11 := module_scalar M1.
Let SMO11 := module_scalar_id M1.
Let SML11 := module_scalar_ldist M1.
Let SMR11 := module_scalar_rdist M1.
Let SMC11 := module_scalar_comp M1.
Let V12 := module_V M2.
Let VP12 := module_plus M2.
Let VZ12 := module_zero M2.
Let VN12 := module_neg M2.
Let VPA12 := module_plus_assoc M2.
Let VPC12 := module_plus_comm M2.
Let VPZ12 := module_plus_lid M2.
Let VPN12 := module_plus_linv M2.
Let SM12 := module_scalar M2.
Let SMO12 := module_scalar_id M2.
Let SML12 := module_scalar_ldist M2.
Let SMR12 := module_scalar_rdist M2.
Let SMC12 := module_scalar_comp M2.
Let V21 := module_V N1.
Let VP21 := module_plus N1.
Let VZ21 := module_zero N1.
Let VN21 := module_neg N1.
Let VPA21 := module_plus_assoc N1.
Let VPC21 := module_plus_comm N1.
Let VPZ21 := module_plus_lid N1.
Let VPN21 := module_plus_linv N1.
Let SM21 := module_scalar N1.
Let SMO21 := module_scalar_id N1.
Let SML21 := module_scalar_ldist N1.
Let SMR21 := module_scalar_rdist N1.
Let SMC21 := module_scalar_comp N1.
Let V22 := module_V N2.
Let VP22 := module_plus N2.
Let VZ22 := module_zero N2.
Let VN22 := module_neg N2.
Let VPA22 := module_plus_assoc N2.
Let VPC22 := module_plus_comm N2.
Let VPZ22 := module_plus_lid N2.
Let VPN22 := module_plus_linv N2.
Let SM22 := module_scalar N2.
Let SMO22 := module_scalar_id N2.
Let SML22 := module_scalar_ldist N2.
Let SMR22 := module_scalar_rdist N2.
Let SMC22 := module_scalar_comp N2.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP11 VZ11 VN11
    VPA11 VPC11 VPZ11 VPN11 SM11 SMO11 SML11 SMR11 SMC11 VP12 VZ12 VN12 VPA12
    VPC12 VPZ12 VPN12 SM12 SMO12 SML12 SMR12 SMC12 VP21 VZ21 VN21 VPA21 VPC21
    VPZ21 VPN21 SM21 SMO21 SML21 SMR21 SMC21 VP22 VZ22 VN22 VPA22 VPC22 VPZ22
    VPN22 SM22 SMO22 SML22 SMR22 SMC22.

Local Infix "⊗1" := (tensor_mult M1 N1) (at level 40, left associativity).
Local Infix "⊗2" := (tensor_mult M2 N2) (at level 40, left associativity).

Let T1_plus := module_plus (tensor_product M1 N1).
Let T1_scalar := module_scalar (tensor_product M1 N1).
Let T2_plus := module_plus (tensor_product M2 N2).
Let T2_scalar := module_scalar (tensor_product M2 N2).

Existing Instances T1_plus T1_scalar T2_plus T2_scalar.

(* end hide *)
Theorem tensor_product_lriso :
    ∀ (f1 : cat_morphism (MODULE F) M1 M2) (f2 : cat_morphism (MODULE F) N1 N2),
    ∃ h : cat_morphism (MODULE F) (tensor_product M1 N1) (tensor_product M2 N2),
        ∀ u v, module_homo_f h (u ⊗1 v) = module_homo_f f1 u ⊗2 module_homo_f f2
        v.
    intros f1 f2.
    cbn in *.
    pose (h u v := module_homo_f f1 u ⊗2 module_homo_f f2 v).
    assert (bilinear h) as h_bil.
    {
        unfold h.
        repeat split; intros.
        -   rewrite (@module_homo_scalar _ _ _ f1).
            apply tensor_lscalar.
        -   rewrite (@module_homo_scalar _ _ _ f2).
            apply tensor_rscalar.
        -   rewrite (@module_homo_plus _ _ _ f1).
            apply tensor_rdist.
        -   rewrite (@module_homo_plus _ _ _ f2).
            apply tensor_ldist.
    }
    pose (h1_base := make_bilinear _ _ _ _ h_bil).
    pose proof (tensor_product_universal _ _ h1_base) as h1_ex.
    apply card_one_ex in h1_ex as [h1 h1_in].
    cbn in *.
    unfold bilinear_from_set in h1_in; cbn in h1_in.
    clear h1_base.
    exists h1.
    exact h1_in.
Qed.

Definition tensor_product_lriso_homo f1 f2
    := ex_val (tensor_product_lriso f1 f2).
Definition tensor_product_lriso_f f1 f2
    := module_homo_f (tensor_product_lriso_homo f1 f2).

Variables (f1 : cat_morphism (MODULE F) M1 M2) (f2 : cat_morphism (MODULE F) N1 N2).

Let lrf := tensor_product_lriso_f f1 f2.

Theorem tensor_product_lriso_eq : ∀ a b,
        lrf (a ⊗1 b) = module_homo_f f1 a ⊗2 module_homo_f f2 b.
    apply (ex_proof (tensor_product_lriso f1 f2)).
Qed.

Theorem tensor_product_lriso_plus : ∀ a b, lrf (a + b) = lrf a + lrf b.
    apply (@module_homo_plus _ _ _ (ex_val (tensor_product_lriso f1 f2))).
Qed.
Theorem tensor_product_lriso_scalar : ∀ a v, lrf (a · v) = a · lrf v.
    apply (@module_homo_scalar _ _ _ (ex_val (tensor_product_lriso f1 f2))).
Qed.

Theorem tensor_product_lriso_iso : isomorphism f1 → isomorphism f2 →
        isomorphism (tensor_product_lriso_homo f1 f2).
    intros [g1 [fg1 gf1]] [g2 [fg2 gf2]].
    inversion fg1 as [fg1']; clear fg1.
    inversion gf1 as [gf1']; clear gf1.
    inversion fg2 as [fg2']; clear fg2.
    inversion gf2 as [gf2']; clear gf2.
    pose proof (func_eq _ _ fg1') as fg1; clear fg1'.
    pose proof (func_eq _ _ gf1') as gf1; clear gf1'.
    pose proof (func_eq _ _ fg2') as fg2; clear fg2'.
    pose proof (func_eq _ _ gf2') as gf2; clear gf2'.
    pose (h' u v := module_homo_f g1 u ⊗1 module_homo_f g2 v).
    assert (bilinear h') as h'_bil.
    {
        unfold h'.
        repeat split; intros.
        -   rewrite (@module_homo_scalar _ _ _ g1).
            apply tensor_lscalar.
        -   rewrite (@module_homo_scalar _ _ _ g2).
            apply tensor_rscalar.
        -   rewrite (@module_homo_plus _ _ _ g1).
            apply tensor_rdist.
        -   rewrite (@module_homo_plus _ _ _ g2).
            apply tensor_ldist.
    }
    pose (h2_base := make_bilinear _ _ _ _ h'_bil).
    pose proof (tensor_product_universal _ _ h2_base) as h2_ex.
    apply card_one_ex in h2_ex as [h2 h2_in].
    cbn in *.
    unfold bilinear_from_set in h2_in; cbn in h2_in.
    clear h2_base.
    exists h2.
    cbn.
    unfold module_homo_compose, module_homo_id; cbn.
    split; apply module_homomorphism_eq; cbn.
    +   intros x.
        pose proof (tensor_sum _ _ x) as [l eq]; subst x.
        induction l using ulist_induction.
        *   rewrite ulist_image_end, ulist_sum_end.
            do 2 rewrite module_homo_zero.
            reflexivity.
        *   rewrite ulist_image_add, ulist_sum_add.
            rewrite (@module_homo_plus _ _ _ h2).
            rewrite tensor_product_lriso_plus.
            rewrite <- IHl at 2; clear IHl.
            apply rplus.
            destruct a as [a [u [v eq]]]; subst a; cbn.
            unfold tensor_mult at 1; rewrite h2_in.
            unfold h'.
            rewrite tensor_product_lriso_eq.
            rewrite fg1, fg2.
            reflexivity.
    +   intros x.
        pose proof (tensor_sum _ _ x) as [l eq]; subst x.
        induction l using ulist_induction.
        *   rewrite ulist_image_end, ulist_sum_end.
            do 2 rewrite module_homo_zero.
            reflexivity.
        *   rewrite ulist_image_add, ulist_sum_add.
            rewrite tensor_product_lriso_plus.
            rewrite (@module_homo_plus _ _ _ h2).
            rewrite <- IHl at 2; clear IHl.
            apply rplus.
            destruct a as [a [u [v eq]]]; subst a; cbn.
            rewrite tensor_product_lriso_eq.
            unfold tensor_mult at 1; rewrite h2_in.
            unfold h'.
            rewrite gf1, gf2.
            reflexivity.
Qed.

Theorem tensor_product_lriso_bij : isomorphism f1 → isomorphism f2 →
        bijective lrf.
    intros f1_iso f2_iso.
    pose proof (tensor_product_lriso_iso f1_iso f2_iso)
        as [[g g_plus g_scalar] [fg gf]].
    cbn in *.
    unfold module_homo_compose, module_homo_id in *; cbn in *.
    inversion fg as [fg']; clear fg.
    inversion gf as [gf']; clear gf.
    apply (inverse_ex_bijective lrf g).
    -   apply func_eq.
        exact fg'.
    -   apply func_eq.
        exact gf'.
Qed.

(* begin hide *)
End TensorProductIsomorphism.

Section TensorProductIsomorphism.

(* end hide *)
Context {F : CRing} (M1 M2 N : Module F).

(* begin hide *)
Let U := cring_U.
Let UP := cring_plus.
Let UZ := cring_zero.
Let UN := cring_neg.
Let UPA := cring_plus_assoc.
Let UPC := cring_plus_comm.
Let UPZ := cring_plus_lid.
Let UPN := cring_plus_linv.
Let UM := cring_mult.
Let UO := cring_one.
Let UMA := cring_mult_assoc.
Let UMC := cring_mult_comm.
Let UMO := cring_mult_lid.
Let UMD := cring_ldist.
Let V11 := module_V M1.
Let VP11 := module_plus M1.
Let VZ11 := module_zero M1.
Let VN11 := module_neg M1.
Let VPA11 := module_plus_assoc M1.
Let VPC11 := module_plus_comm M1.
Let VPZ11 := module_plus_lid M1.
Let VPN11 := module_plus_linv M1.
Let SM11 := module_scalar M1.
Let SMO11 := module_scalar_id M1.
Let SML11 := module_scalar_ldist M1.
Let SMR11 := module_scalar_rdist M1.
Let SMC11 := module_scalar_comp M1.
Let V12 := module_V M2.
Let VP12 := module_plus M2.
Let VZ12 := module_zero M2.
Let VN12 := module_neg M2.
Let VPA12 := module_plus_assoc M2.
Let VPC12 := module_plus_comm M2.
Let VPZ12 := module_plus_lid M2.
Let VPN12 := module_plus_linv M2.
Let SM12 := module_scalar M2.
Let SMO12 := module_scalar_id M2.
Let SML12 := module_scalar_ldist M2.
Let SMR12 := module_scalar_rdist M2.
Let SMC12 := module_scalar_comp M2.
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
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP11 VZ11 VN11
    VPA11 VPC11 VPZ11 VPN11 SM11 SMO11 SML11 SMR11 SMC11 VP12 VZ12 VN12 VPA12
    VPC12 VPZ12 VPN12 SM12 SMO12 SML12 SMR12 SMC12 VP2 VZ2 VN2 VPA2 VPC2
    VPZ2 VPN2 SM2 SMO2 SML2 SMR2 SMC2.

Local Infix "⊗1" := (tensor_mult M1 N) (at level 40, left associativity).
Local Infix "⊗2" := (tensor_mult M2 N) (at level 40, left associativity).

Let T1_plus := module_plus (tensor_product M1 N).
Let T1_scalar := module_scalar (tensor_product M1 N).
Let T2_plus := module_plus (tensor_product M2 N).
Let T2_scalar := module_scalar (tensor_product M2 N).

Existing Instances T1_plus T1_scalar T2_plus T2_scalar.

(* end hide *)
Theorem tensor_product_liso :
    ∀ (f : cat_morphism (MODULE F) M1 M2),
    ∃ g : cat_morphism (MODULE F) (tensor_product M1 N) (tensor_product M2 N),
        (isomorphism f → isomorphism g) ∧
        ∀ u v, module_homo_f g (u ⊗1 v) = module_homo_f f u ⊗2 v.
    intros f.
    exists (tensor_product_lriso_homo M1 M2 N N f (cat_id (MODULE F) N)).
    split.
    -   intros f_iso.
        apply (tensor_product_lriso_iso _ _ _ _ _ _ f_iso (id_isomorphism _)).
    -   apply tensor_product_lriso_eq.
Qed.

Definition tensor_product_liso_homo f := ex_val (tensor_product_liso f).
Definition tensor_product_liso_f f := module_homo_f (tensor_product_liso_homo f).

Variable (f : cat_morphism (MODULE F) M1 M2).

Let lf := tensor_product_liso_f f.

Theorem tensor_product_liso_eq : ∀ a b,
        lf (a ⊗1 b) = module_homo_f f a ⊗2 b.
    apply (ex_proof (tensor_product_liso f)).
Qed.

Theorem tensor_product_liso_plus : ∀ a b, lf (a + b) = lf a + lf b.
    apply (@module_homo_plus _ _ _ (ex_val (tensor_product_liso f))).
Qed.
Theorem tensor_product_liso_scalar : ∀ a v, lf (a · v) = a · lf v.
    apply (@module_homo_scalar _ _ _ (ex_val (tensor_product_liso f))).
Qed.

Theorem tensor_product_liso_iso : isomorphism f →
        isomorphism (tensor_product_liso_homo f).
    apply (ex_proof (tensor_product_liso f)).
Qed.

Theorem tensor_product_liso_bij : isomorphism f → bijective lf.
    intros f_iso.
    pose proof (tensor_product_liso_iso f_iso) as [[g g_plus g_scalar] [fg gf]].
    cbn in *.
    unfold module_homo_compose, module_homo_id in *; cbn in *.
    inversion fg as [fg']; clear fg.
    inversion gf as [gf']; clear gf.
    apply (inverse_ex_bijective lf g).
    -   apply func_eq.
        exact fg'.
    -   apply func_eq.
        exact gf'.
Qed.

(* begin hide *)
End TensorProductIsomorphism.

Section TensorProductIsomorphism.

(* end hide *)
Context {F : CRing} (M N1 N2 : Module F).

(* begin hide *)
Let U := cring_U.
Let UP := cring_plus.
Let UZ := cring_zero.
Let UN := cring_neg.
Let UPA := cring_plus_assoc.
Let UPC := cring_plus_comm.
Let UPZ := cring_plus_lid.
Let UPN := cring_plus_linv.
Let UM := cring_mult.
Let UO := cring_one.
Let UMA := cring_mult_assoc.
Let UMC := cring_mult_comm.
Let UMO := cring_mult_lid.
Let UMD := cring_ldist.
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
Let V21 := module_V N1.
Let VP21 := module_plus N1.
Let VZ21 := module_zero N1.
Let VN21 := module_neg N1.
Let VPA21 := module_plus_assoc N1.
Let VPC21 := module_plus_comm N1.
Let VPZ21 := module_plus_lid N1.
Let VPN21 := module_plus_linv N1.
Let SM21 := module_scalar N1.
Let SMO21 := module_scalar_id N1.
Let SML21 := module_scalar_ldist N1.
Let SMR21 := module_scalar_rdist N1.
Let SMC21 := module_scalar_comp N1.
Let V22 := module_V N2.
Let VP22 := module_plus N2.
Let VZ22 := module_zero N2.
Let VN22 := module_neg N2.
Let VPA22 := module_plus_assoc N2.
Let VPC22 := module_plus_comm N2.
Let VPZ22 := module_plus_lid N2.
Let VPN22 := module_plus_linv N2.
Let SM22 := module_scalar N2.
Let SMO22 := module_scalar_id N2.
Let SML22 := module_scalar_ldist N2.
Let SMR22 := module_scalar_rdist N2.
Let SMC22 := module_scalar_comp N2.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP1 VZ1 VN1
    VPA1 VPC1 VPZ1 VPN1 SM1 SMO1 SML1 SMR1 SMC1 VP21 VZ21 VN21 VPA21 VPC21 VPZ21
    VPN21 SM21 SMO21 SML21 SMR21 SMC21 VP22 VZ22 VN22 VPA22 VPC22 VPZ22 VPN22
    SM22 SMO22 SML22 SMR22 SMC22.

Local Infix "⊗1" := (tensor_mult M N1) (at level 40, left associativity).
Local Infix "⊗2" := (tensor_mult M N2) (at level 40, left associativity).

Let T1_plus := module_plus (tensor_product M N1).
Let T1_scalar := module_scalar (tensor_product M N1).
Let T2_plus := module_plus (tensor_product M N2).
Let T2_scalar := module_scalar (tensor_product M N2).

Existing Instances T1_plus T1_scalar T2_plus T2_scalar.

(* end hide *)
Theorem tensor_product_riso :
    ∀ (f : cat_morphism (MODULE F) N1 N2),
    ∃ g : cat_morphism (MODULE F) (tensor_product M N1) (tensor_product M N2),
        (isomorphism f → isomorphism g) ∧
        ∀ u v, module_homo_f g (u ⊗1 v) = u ⊗2 module_homo_f f v.
    intros f.
    exists (tensor_product_lriso_homo M M N1 N2 (cat_id (MODULE F) M) f).
    split.
    -   intros f_iso.
        apply (tensor_product_lriso_iso _ _ _ _ _ _ (id_isomorphism _) f_iso).
    -   apply tensor_product_lriso_eq.
Qed.

Definition tensor_product_riso_homo f := ex_val (tensor_product_riso f).
Definition tensor_product_riso_f f := module_homo_f (tensor_product_riso_homo f).

Variable (f : cat_morphism (MODULE F) N1 N2).

Let rf := tensor_product_riso_f f.

Theorem tensor_product_riso_eq : ∀ a b, rf (a ⊗1 b) = a ⊗2 module_homo_f f b.
    apply (ex_proof (tensor_product_riso f)).
Qed.

Theorem tensor_product_riso_plus : ∀ a b, rf (a + b) = rf a + rf b.
    apply (@module_homo_plus _ _ _ (ex_val (tensor_product_riso f))).
Qed.
Theorem tensor_product_riso_scalar : ∀ a v, rf (a · v) = a · rf v.
    apply (@module_homo_scalar _ _ _ (ex_val (tensor_product_riso f))).
Qed.

Theorem tensor_product_riso_iso : isomorphism f →
        isomorphism (tensor_product_riso_homo f).
    apply (ex_proof (tensor_product_riso f)).
Qed.

Theorem tensor_product_riso_bij : isomorphism f → bijective rf.
    intros f_iso.
    pose proof (tensor_product_riso_iso f_iso) as [[g g_plus g_scalar] [fg gf]].
    cbn in *.
    unfold module_homo_compose, module_homo_id in *; cbn in *.
    inversion fg as [fg']; clear fg.
    inversion gf as [gf']; clear gf.
    apply (inverse_ex_bijective rf g).
    -   apply func_eq.
        exact fg'.
    -   apply func_eq.
        exact gf'.
Qed.
(* begin hide *)

End TensorProductIsomorphism.
(* end hide *)
