Require Import init.

Require Import linear_bilinear.
Require Import tensor_product_universal.
Require Import plus_sum.

Require Import set.
Require Import list.
Require Import card.

Require Import module_category.

Section TensorProductIsomorphisms.

Context U V1 V2 `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UPA : @PlusAssoc U UP,
    UPC : @PlusComm U UP,
    UPZ : @PlusLid U UP UZ,
    UPN : @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    UMA : @MultAssoc U UM,
    UMC : @MultComm U UM,
    UMO : @MultLid U UM UO,
    UMD : @Ldist U UP UM,

    VP1 : Plus V1,
    VZ1 : Zero V1,
    VN1 : Neg V1,
    VPA1 : @PlusAssoc V1 VP1,
    VPC1 : @PlusComm V1 VP1,
    VPZ1 : @PlusLid V1 VP1 VZ1,
    VPN1 : @PlusLinv V1 VP1 VZ1 VN1,

    SM1 : ScalarMult U V1,
    SMO1 : @ScalarId U V1 UO SM1,
    SML1 : @ScalarLdist U V1 VP1 SM1,
    SMR1 : @ScalarRdist U V1 UP VP1 SM1,
    SMC1 : @ScalarComp U V1 UM SM1,

    VP2 : Plus V2,
    VZ2 : Zero V2,
    VN2 : Neg V2,
    VPA2 : @PlusAssoc V2 VP2,
    VPC2 : @PlusComm V2 VP2,
    VPZ2 : @PlusLid V2 VP2 VZ2,
    VPN2 : @PlusLinv V2 VP2 VZ2 VN2,

    SM2 : ScalarMult U V2,
    SMO2 : @ScalarId U V2 UO SM2,
    SML2 : @ScalarLdist U V2 VP2 SM2,
    SMR2 : @ScalarRdist U V2 UP VP2 SM2,
    SMC2 : @ScalarComp U V2 UM SM2
}.

Local Infix "⊗" := (tensor_mult U U V1).

Existing Instances scalar_scalar_mult.

Let TU1_plus := module_plus (tensor_product U U V1).
Let TU1_scalar := module_scalar (tensor_product U U V1).

Existing Instances TU1_plus TU1_scalar.

Theorem tensor_product_lid :
    ∃ f : ModuleHomomorphism (tensor_product U U V1) (vector_module U V1),
        isomorphism (C0 := MODULE (scalar_cring U)) f ∧
        ∀ a v, module_homo_f f (a ⊗ v) = a · v.
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
    pose (f_base := make_bilinear U U V1 (vector_module U V1) (λ a (v : V1), a · v) f_bil).
    pose proof (tensor_product_universal U U V1 f_base) as f_ex.
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
        exists (make_module_homomorphism _ (vector_module U V1) _ g g_plus g_scalar).
        cbn.
        unfold module_homo_compose, module_homo_id; cbn.
        split; apply module_homomorphism_eq; cbn.
        +   intros x.
            unfold g.
            unfold tensor_mult; rewrite f_in.
            apply scalar_id.
        +   intros x.
            unfold g.
            pose proof (tensor_sum _ _ _ x) as [l eq]; subst x.
            induction l.
            *   cbn.
                rewrite module_homo_zero.
                apply tensor_product_ranni.
                exact VPZ1.
            *   cbn.
                rewrite (@module_homo_plus _ _ _ f).
                rewrite tensor_ldist.
                rewrite <- IHl at 2; clear IHl.
                apply rplus.
                destruct a as [a [u [v eq]]]; subst a; cbn.
                unfold tensor_mult at 2; rewrite f_in.
                rewrite tensor_rscalar.
                rewrite <- tensor_lscalar.
                unfold scalar_mult; cbn.
                rewrite mult_rid.
                reflexivity.
    -   exact f_in.
Qed.

Definition tensor_product_lid_f := module_homo_f (ex_val tensor_product_lid).
Let lf := tensor_product_lid_f.

Theorem tensor_product_lid_eq : ∀ a v, lf (a ⊗ v) = a · v.
    apply (ex_proof tensor_product_lid).
Qed.

Theorem tensor_product_lid_plus : ∀ a b, lf (a + b) = lf a + lf b.
    apply (@module_homo_plus _ _ _ (ex_val tensor_product_lid)).
Qed.
Theorem tensor_product_lid_scalar : ∀ a v, lf (a · v) = a · lf v.
    apply (@module_homo_scalar _ _ _ (ex_val tensor_product_lid)).
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

Local Infix "⊗12" := (tensor_mult U V1 V2) (at level 40, left associativity).
Local Infix "⊗21" := (tensor_mult U V2 V1) (at level 40, left associativity).

Let T12_plus := module_plus (tensor_product U V1 V2).
Let T12_scalar := module_scalar (tensor_product U V1 V2).
Let T21_plus := module_plus (tensor_product U V2 V1).
Let T21_scalar := module_scalar (tensor_product U V2 V1).
Existing Instances T12_plus T12_scalar T21_plus T21_scalar.

Theorem tensor_product_comm :
    ∃ f : ModuleHomomorphism (tensor_product U V1 V2) (tensor_product U V2 V1),
        isomorphism (C0 := MODULE (scalar_cring U)) f ∧
        ∀ a b, module_homo_f f (a ⊗12 b) = b ⊗21 a.
    assert (bilinear (λ a b, b ⊗21 a)) as f_bil
        by (repeat split; intros; apply tensor_bilinear).
    pose (f_base := make_bilinear U V1 V2 _ _ f_bil).
    pose proof (tensor_product_universal U V1 V2 f_base) as f_ex.
    apply card_one_ex in f_ex as [f f_in].
    cbn in *.
    unfold bilinear_from_set in f_in; cbn in f_in.
    clear f_base.
    exists f.
    split.
    -   assert (bilinear (λ b a, a ⊗12 b)) as g_bil
            by (repeat split; intros; apply tensor_bilinear).
        pose (g_base := make_bilinear U V2 V1 _ _ g_bil).
        pose proof (tensor_product_universal U V2 V1 g_base) as g_ex.
        apply card_one_ex in g_ex as [g g_in].
        cbn in *.
        unfold bilinear_from_set in g_in; cbn in g_in.
        clear g_base.
        exists g.
        cbn.
        unfold module_homo_compose, module_homo_id; cbn.
        change (bilinear_from_f U V1 V2 (tensor_bilinear_from U V1 V2)) with
            (tensor_mult U V1 V2) in f_in.
        change (bilinear_from_f U V2 V1 (tensor_bilinear_from U V2 V1)) with
            (tensor_mult U V2 V1) in g_in.
        split; apply module_homomorphism_eq; cbn.
        +   intros x.
            pose proof (tensor_sum U V2 V1 x) as [l x_eq]; subst x.
            induction l.
            *   cbn.
                rewrite <- (tensor_product_zero U V2 V1).
                rewrite g_in.
                rewrite f_in.
                reflexivity.
            *   cbn.
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
            pose proof (tensor_sum U V1 V2 x) as [l x_eq]; subst x.
            induction l.
            *   cbn.
                rewrite <- (tensor_product_zero U V1 V2).
                rewrite f_in.
                rewrite g_in.
                reflexivity.
            *   cbn.
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

Definition tensor_product_comm_f := module_homo_f (ex_val tensor_product_comm).
Let cf := tensor_product_comm_f.

Theorem tensor_product_comm_eq : ∀ a b, cf (a ⊗12 b) = b ⊗21 a.
    apply (ex_proof tensor_product_comm).
Qed.

Theorem tensor_product_comm_plus : ∀ a b, cf (a + b) = cf a + cf b.
    apply (@module_homo_plus _ _ _ (ex_val tensor_product_comm)).
Qed.
Theorem tensor_product_comm_scalar : ∀ a v, cf (a · v) = a · cf v.
    apply (@module_homo_scalar _ _ _ (ex_val tensor_product_comm)).
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

End TensorProductIsomorphisms.

Section TensorProductIsomorphism.

Context U V `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UPA : @PlusAssoc U UP,
    UPC : @PlusComm U UP,
    UPZ : @PlusLid U UP UZ,
    UPN : @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    UMA : @MultAssoc U UM,
    UMC : @MultComm U UM,
    UMO : @MultLid U UM UO,
    UMD : @Ldist U UP UM,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    VPA : @PlusAssoc V VP,
    VPC : @PlusComm V VP,
    VPZ : @PlusLid V VP VZ,
    VPN : @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    SMO : @ScalarId U V UO SM,
    SML : @ScalarLdist U V VP SM,
    SMR : @ScalarRdist U V UP VP SM,
    SMC : @ScalarComp U V UM SM
}.

Local Infix "⊗" := (tensor_mult U V U).

Existing Instances scalar_scalar_mult.

Let TVU_plus := module_plus (tensor_product U V U).
Let TVU_scalar := module_scalar (tensor_product U V U).

Existing Instances TVU_plus TVU_scalar.

Definition tensor_product_rid_f :=
    module_homo_f (module_homo_compose
        (ex_val (tensor_product_lid U V))
        (ex_val (tensor_product_comm U V U))).
Let f := tensor_product_rid_f.

Theorem tensor_product_rid_eq : ∀ a v, f (v ⊗ a) = a · v.
    intros a v.
    unfold f, tensor_product_rid_f.
    cbn.
    change (module_homo_f (ex_val (tensor_product_lid U V))) with
        (tensor_product_lid_f U V).
    change (module_homo_f (ex_val (tensor_product_comm U V U))) with
        (tensor_product_comm_f U V U).
    rewrite tensor_product_comm_eq.
    rewrite tensor_product_lid_eq.
    reflexivity.
Qed.

Theorem tensor_product_rid_plus : ∀ a b, f (a + b) = f a + f b.
    intros a b.
    unfold f, tensor_product_rid_f.
    cbn.
    change (module_homo_f (ex_val (tensor_product_lid U V))) with
        (tensor_product_lid_f U V).
    change (module_homo_f (ex_val (tensor_product_comm U V U))) with
        (tensor_product_comm_f U V U).
    rewrite tensor_product_comm_plus.
    rewrite tensor_product_lid_plus.
    reflexivity.
Qed.
Theorem tensor_product_rid_scalar : ∀ a v, f (a · v) = a · f v.
    intros a v.
    unfold f, tensor_product_rid_f.
    cbn.
    change (module_homo_f (ex_val (tensor_product_lid U V))) with
        (tensor_product_lid_f U V).
    change (module_homo_f (ex_val (tensor_product_comm U V U))) with
        (tensor_product_comm_f U V U).
    rewrite tensor_product_comm_scalar.
    rewrite tensor_product_lid_scalar.
    reflexivity.
Qed.

Theorem tensor_product_rid_bij : bijective f.
    unfold f, tensor_product_rid_f.
    cbn.
    apply bij_comp.
    -   apply tensor_product_comm_bij.
    -   apply tensor_product_lid_bij.
Qed.

End TensorProductIsomorphism.

Section TensorProductIsomorphism.

Context U V11 V12 V21 V22 `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UPA : @PlusAssoc U UP,
    UPC : @PlusComm U UP,
    UPZ : @PlusLid U UP UZ,
    UPN : @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    UMA : @MultAssoc U UM,
    UMC : @MultComm U UM,
    UMO : @MultLid U UM UO,
    UMD : @Ldist U UP UM,

    VP11 : Plus V11,
    VZ11 : Zero V11,
    VN11 : Neg V11,
    VPA11 : @PlusAssoc V11 VP11,
    VPC11 : @PlusComm V11 VP11,
    VPZ11 : @PlusLid V11 VP11 VZ11,
    VPN11 : @PlusLinv V11 VP11 VZ11 VN11,

    SM11 : ScalarMult U V11,
    SMO11 : @ScalarId U V11 UO SM11,
    SML11 : @ScalarLdist U V11 VP11 SM11,
    SMR11 : @ScalarRdist U V11 UP VP11 SM11,
    SMC11 : @ScalarComp U V11 UM SM11,

    VP12 : Plus V12,
    VZ12 : Zero V12,
    VN12 : Neg V12,
    VPA12 : @PlusAssoc V12 VP12,
    VPC12 : @PlusComm V12 VP12,
    VPZ12 : @PlusLid V12 VP12 VZ12,
    VPN12 : @PlusLinv V12 VP12 VZ12 VN12,

    SM12 : ScalarMult U V12,
    SMO12 : @ScalarId U V12 UO SM12,
    SML12 : @ScalarLdist U V12 VP12 SM12,
    SMR12 : @ScalarRdist U V12 UP VP12 SM12,
    SMC12 : @ScalarComp U V12 UM SM12,

    VP21 : Plus V21,
    VZ21 : Zero V21,
    VN21 : Neg V21,
    VPA21 : @PlusAssoc V21 VP21,
    VPC21 : @PlusComm V21 VP21,
    VPZ21 : @PlusLid V21 VP21 VZ21,
    VPN21 : @PlusLinv V21 VP21 VZ21 VN21,

    SM21 : ScalarMult U V21,
    SMO21 : @ScalarId U V21 UO SM21,
    SML21 : @ScalarLdist U V21 VP21 SM21,
    SMR21 : @ScalarRdist U V21 UP VP21 SM21,
    SMC21 : @ScalarComp U V21 UM SM21,

    VP22 : Plus V22,
    VZ22 : Zero V22,
    VN22 : Neg V22,
    VPA22 : @PlusAssoc V22 VP22,
    VPC22 : @PlusComm V22 VP22,
    VPZ22 : @PlusLid V22 VP22 VZ22,
    VPN22 : @PlusLinv V22 VP22 VZ22 VN22,

    SM22 : ScalarMult U V22,
    SMO22 : @ScalarId U V22 UO SM22,
    SML22 : @ScalarLdist U V22 VP22 SM22,
    SMR22 : @ScalarRdist U V22 UP VP22 SM22,
    SMC22 : @ScalarComp U V22 UM SM22
}.

Local Infix "⊗1" := (tensor_mult U V11 V21) (at level 40, left associativity).
Local Infix "⊗2" := (tensor_mult U V12 V22) (at level 40, left associativity).

Let T1_plus := module_plus (tensor_product U V11 V21).
Let T1_scalar := module_scalar (tensor_product U V11 V21).
Let T2_plus := module_plus (tensor_product U V12 V22).
Let T2_scalar := module_scalar (tensor_product U V12 V22).

Existing Instances T1_plus T1_scalar T2_plus T2_scalar.

Theorem tensor_product_lriso :
    ∀ (f1 : ModuleHomomorphism (vector_module U V11) (vector_module U V12))
      (f2 : ModuleHomomorphism (vector_module U V21) (vector_module U V22)),
    isomorphism (C0 := MODULE (scalar_cring U)) f1 →
    isomorphism (C0 := MODULE (scalar_cring U)) f2 →
    ∃ h : ModuleHomomorphism (tensor_product U V11 V21) (tensor_product U V12 V22),
        isomorphism (C0 := MODULE (scalar_cring U)) h ∧
        ∀ u v, module_homo_f h (u ⊗1 v) = module_homo_f f1 u ⊗2 module_homo_f f2
        v.
    intros f1 f2 [g1 [fg1 gf1]] [g2 [fg2 gf2]].
    inversion fg1 as [fg1']; clear fg1.
    inversion gf1 as [gf1']; clear gf1.
    inversion fg2 as [fg2']; clear fg2.
    inversion gf2 as [gf2']; clear gf2.
    pose proof (func_eq _ _ fg1') as fg1; clear fg1'.
    pose proof (func_eq _ _ gf1') as gf1; clear gf1'.
    pose proof (func_eq _ _ fg2') as fg2; clear fg2'.
    pose proof (func_eq _ _ gf2') as gf2; clear gf2'.
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
    pose (h1_base := make_bilinear _ _ _ _ _ h_bil).
    pose proof (tensor_product_universal _ _ _ h1_base) as h1_ex.
    apply card_one_ex in h1_ex as [h1 h1_in].
    cbn in *.
    unfold bilinear_from_set in h1_in; cbn in h1_in.
    clear h1_base.
    exists h1.
    split.
    -   pose (h' u v := module_homo_f g1 u ⊗1 module_homo_f g2 v).
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
        pose (h2_base := make_bilinear _ _ _ _ _ h'_bil).
        pose proof (tensor_product_universal _ _ _ h2_base) as h2_ex.
        apply card_one_ex in h2_ex as [h2 h2_in].
        cbn in *.
        unfold bilinear_from_set in h2_in; cbn in h2_in.
        clear h2_base.
        exists h2.
        cbn.
        unfold module_homo_compose, module_homo_id; cbn.
        split; apply module_homomorphism_eq; cbn.
        +   intros x.
            pose proof (tensor_sum _ _ _ x) as [l eq]; subst x.
            induction l.
            *   cbn.
                do 2 rewrite module_homo_zero.
                reflexivity.
            *   cbn.
                rewrite (@module_homo_plus _ _ _ h2).
                rewrite (@module_homo_plus _ _ _ h1).
                rewrite <- IHl at 2; clear IHl.
                apply rplus.
                destruct a as [a [u [v eq]]]; subst a; cbn.
                unfold tensor_mult at 1; rewrite h2_in.
                unfold h'.
                unfold tensor_mult at 1; rewrite h1_in.
                unfold h.
                rewrite fg1, fg2.
                reflexivity.
        +   intros x.
            pose proof (tensor_sum _ _ _ x) as [l eq]; subst x.
            induction l.
            *   cbn.
                do 2 rewrite module_homo_zero.
                reflexivity.
            *   cbn.
                rewrite (@module_homo_plus _ _ _ h1).
                rewrite (@module_homo_plus _ _ _ h2).
                rewrite <- IHl at 2; clear IHl.
                apply rplus.
                destruct a as [a [u [v eq]]]; subst a; cbn.
                unfold tensor_mult at 1; rewrite h1_in.
                unfold h.
                unfold tensor_mult at 1; rewrite h2_in.
                unfold h'.
                rewrite gf1, gf2.
                reflexivity.
    -   exact h1_in.
Qed.

Definition tensor_product_lriso_f f1 f2 f1_iso f2_iso
    := module_homo_f (ex_val (tensor_product_lriso f1 f2 f1_iso f2_iso)).

Variables
    (f1 : ModuleHomomorphism (vector_module U V11) (vector_module U V12))
    (f2 : ModuleHomomorphism (vector_module U V21) (vector_module U V22))
    (f1_iso : isomorphism (C0 := MODULE (scalar_cring U)) f1)
    (f2_iso : isomorphism (C0 := MODULE (scalar_cring U)) f2).

Let lrf := tensor_product_lriso_f f1 f2 f1_iso f2_iso.

Theorem tensor_product_lriso_eq : ∀ a b,
        lrf (a ⊗1 b) = module_homo_f f1 a ⊗2 module_homo_f f2 b.
    apply (ex_proof (tensor_product_lriso f1 f2 f1_iso f2_iso)).
Qed.

Theorem tensor_product_lriso_plus : ∀ a b, lrf (a + b) = lrf a + lrf b.
    apply (@module_homo_plus _ _ _ (ex_val (tensor_product_lriso f1 f2 f1_iso f2_iso))).
Qed.
Theorem tensor_product_lriso_scalar : ∀ a v, lrf (a · v) = a · lrf v.
    apply (@module_homo_scalar _ _ _ (ex_val (tensor_product_lriso f1 f2 f1_iso f2_iso))).
Qed.

Theorem tensor_product_lriso_bij : bijective lrf.
    pose proof (land (ex_proof (tensor_product_lriso f1 f2 f1_iso f2_iso)))
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

End TensorProductIsomorphism.

Section TensorProductIsomorphism.

Context U V11 V12 V2 `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UPA : @PlusAssoc U UP,
    UPC : @PlusComm U UP,
    UPZ : @PlusLid U UP UZ,
    UPN : @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    UMA : @MultAssoc U UM,
    UMC : @MultComm U UM,
    UMO : @MultLid U UM UO,
    UMD : @Ldist U UP UM,

    VP11 : Plus V11,
    VZ11 : Zero V11,
    VN11 : Neg V11,
    VPA11 : @PlusAssoc V11 VP11,
    VPC11 : @PlusComm V11 VP11,
    VPZ11 : @PlusLid V11 VP11 VZ11,
    VPN11 : @PlusLinv V11 VP11 VZ11 VN11,

    SM11 : ScalarMult U V11,
    SMO11 : @ScalarId U V11 UO SM11,
    SML11 : @ScalarLdist U V11 VP11 SM11,
    SMR11 : @ScalarRdist U V11 UP VP11 SM11,
    SMC11 : @ScalarComp U V11 UM SM11,

    VP12 : Plus V12,
    VZ12 : Zero V12,
    VN12 : Neg V12,
    VPA12 : @PlusAssoc V12 VP12,
    VPC12 : @PlusComm V12 VP12,
    VPZ12 : @PlusLid V12 VP12 VZ12,
    VPN12 : @PlusLinv V12 VP12 VZ12 VN12,

    SM12 : ScalarMult U V12,
    SMO12 : @ScalarId U V12 UO SM12,
    SML12 : @ScalarLdist U V12 VP12 SM12,
    SMR12 : @ScalarRdist U V12 UP VP12 SM12,
    SMC12 : @ScalarComp U V12 UM SM12,

    VP2 : Plus V2,
    VZ2 : Zero V2,
    VN2 : Neg V2,
    VPA2 : @PlusAssoc V2 VP2,
    VPC2 : @PlusComm V2 VP2,
    VPZ2 : @PlusLid V2 VP2 VZ2,
    VPN2 : @PlusLinv V2 VP2 VZ2 VN2,

    SM2 : ScalarMult U V2,
    SMO2 : @ScalarId U V2 UO SM2,
    SML2 : @ScalarLdist U V2 VP2 SM2,
    SMR2 : @ScalarRdist U V2 UP VP2 SM2,
    SMC2 : @ScalarComp U V2 UM SM2
}.

Local Infix "⊗1" := (tensor_mult U V11 V2) (at level 40, left associativity).
Local Infix "⊗2" := (tensor_mult U V12 V2) (at level 40, left associativity).

Let T1_plus := module_plus (tensor_product U V11 V2).
Let T1_scalar := module_scalar (tensor_product U V11 V2).
Let T2_plus := module_plus (tensor_product U V12 V2).
Let T2_scalar := module_scalar (tensor_product U V12 V2).

Existing Instances T1_plus T1_scalar T2_plus T2_scalar.

Theorem tensor_product_liso :
    ∀ (f : ModuleHomomorphism (vector_module U V11) (vector_module U V12)),
    isomorphism (C0 := MODULE (scalar_cring U)) f →
    ∃ g : ModuleHomomorphism (tensor_product U V11 V2) (tensor_product U V12 V2),
        isomorphism (C0 := MODULE (scalar_cring U)) g ∧
        ∀ u v, module_homo_f g (u ⊗1 v) = module_homo_f f u ⊗2 v.
    intros f f_iso.
    exact (tensor_product_lriso U V11 V12 V2 V2 f
        (cat_id (MODULE (scalar_cring U)) (vector_module U V2)) f_iso
        (id_isomorphism (C0 := MODULE (scalar_cring U))(vector_module U V2))).
Qed.

Definition tensor_product_liso_f f f_iso
    := module_homo_f (ex_val (tensor_product_liso f f_iso)).

Variables
    (f : ModuleHomomorphism (vector_module U V11) (vector_module U V12))
    (f_iso : isomorphism (C0 := MODULE (scalar_cring U)) f).

Let lf := tensor_product_liso_f f f_iso.

Theorem tensor_product_liso_eq : ∀ a b,
        lf (a ⊗1 b) = module_homo_f f a ⊗2 b.
    apply (ex_proof (tensor_product_liso f f_iso)).
Qed.

Theorem tensor_product_liso_plus : ∀ a b, lf (a + b) = lf a + lf b.
    apply (@module_homo_plus _ _ _ (ex_val (tensor_product_liso f f_iso))).
Qed.
Theorem tensor_product_liso_scalar : ∀ a v, lf (a · v) = a · lf v.
    apply (@module_homo_scalar _ _ _ (ex_val (tensor_product_liso f f_iso))).
Qed.

Theorem tensor_product_liso_bij : bijective lf.
    pose proof (land (ex_proof (tensor_product_liso f f_iso)))
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

End TensorProductIsomorphism.

Section TensorProductIsomorphism.

Context U V1 V21 V22 `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UPA : @PlusAssoc U UP,
    UPC : @PlusComm U UP,
    UPZ : @PlusLid U UP UZ,
    UPN : @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    UMA : @MultAssoc U UM,
    UMC : @MultComm U UM,
    UMO : @MultLid U UM UO,
    UMD : @Ldist U UP UM,

    VP1 : Plus V1,
    VZ1 : Zero V1,
    VN1 : Neg V1,
    VPA1 : @PlusAssoc V1 VP1,
    VPC1 : @PlusComm V1 VP1,
    VPZ1 : @PlusLid V1 VP1 VZ1,
    VPN1 : @PlusLinv V1 VP1 VZ1 VN1,

    SM1 : ScalarMult U V1,
    SMO1 : @ScalarId U V1 UO SM1,
    SML1 : @ScalarLdist U V1 VP1 SM1,
    SMR1 : @ScalarRdist U V1 UP VP1 SM1,
    SMC1 : @ScalarComp U V1 UM SM1,

    VP21 : Plus V21,
    VZ21 : Zero V21,
    VN21 : Neg V21,
    VPA21 : @PlusAssoc V21 VP21,
    VPC21 : @PlusComm V21 VP21,
    VPZ21 : @PlusLid V21 VP21 VZ21,
    VPN21 : @PlusLinv V21 VP21 VZ21 VN21,

    SM21 : ScalarMult U V21,
    SMO21 : @ScalarId U V21 UO SM21,
    SML21 : @ScalarLdist U V21 VP21 SM21,
    SMR21 : @ScalarRdist U V21 UP VP21 SM21,
    SMC21 : @ScalarComp U V21 UM SM21,

    VP22 : Plus V22,
    VZ22 : Zero V22,
    VN22 : Neg V22,
    VPA22 : @PlusAssoc V22 VP22,
    VPC22 : @PlusComm V22 VP22,
    VPZ22 : @PlusLid V22 VP22 VZ22,
    VPN22 : @PlusLinv V22 VP22 VZ22 VN22,

    SM22 : ScalarMult U V22,
    SMO22 : @ScalarId U V22 UO SM22,
    SML22 : @ScalarLdist U V22 VP22 SM22,
    SMR22 : @ScalarRdist U V22 UP VP22 SM22,
    SMC22 : @ScalarComp U V22 UM SM22
}.

Local Infix "⊗1" := (tensor_mult U V1 V21) (at level 40, left associativity).
Local Infix "⊗2" := (tensor_mult U V1 V22) (at level 40, left associativity).

Let T1_plus := module_plus (tensor_product U V1 V21).
Let T1_scalar := module_scalar (tensor_product U V1 V21).
Let T2_plus := module_plus (tensor_product U V1 V22).
Let T2_scalar := module_scalar (tensor_product U V1 V22).

Existing Instances T1_plus T1_scalar T2_plus T2_scalar.

Theorem tensor_product_riso :
    ∀ (f : ModuleHomomorphism (vector_module U V21) (vector_module U V22)),
    isomorphism (C0 := MODULE (scalar_cring U)) f →
    ∃ g : ModuleHomomorphism (tensor_product U V1 V21) (tensor_product U V1 V22),
        isomorphism (C0 := MODULE (scalar_cring U)) g ∧
        ∀ u v, module_homo_f g (u ⊗1 v) = u ⊗2 module_homo_f f v.
    intros f f_iso.
    exact (tensor_product_lriso U V1 V1 V21 V22
        (cat_id (MODULE (scalar_cring U)) (vector_module U V1)) f
        (id_isomorphism (C0 := MODULE (scalar_cring U)) (vector_module U V1))
        f_iso).
Qed.

Definition tensor_product_riso_f f f_iso
    := module_homo_f (ex_val (tensor_product_riso f f_iso)).

Variables
    (f : ModuleHomomorphism (vector_module U V21) (vector_module U V22))
    (f_iso : isomorphism (C0 := MODULE (scalar_cring U)) f).

Let rf := tensor_product_riso_f f f_iso.

Theorem tensor_product_riso_eq : ∀ a b,
        rf (a ⊗1 b) = a ⊗2 module_homo_f f b.
    apply (ex_proof (tensor_product_riso f f_iso)).
Qed.

Theorem tensor_product_riso_plus : ∀ a b, rf (a + b) = rf a + rf b.
    apply (@module_homo_plus _ _ _ (ex_val (tensor_product_riso f f_iso))).
Qed.
Theorem tensor_product_riso_scalar : ∀ a v, rf (a · v) = a · rf v.
    apply (@module_homo_scalar _ _ _ (ex_val (tensor_product_riso f f_iso))).
Qed.

Theorem tensor_product_riso_bij : bijective rf.
    pose proof (land (ex_proof (tensor_product_riso f f_iso)))
        as [[g g_plus g_scalar] [fg gf]].
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

End TensorProductIsomorphism.
