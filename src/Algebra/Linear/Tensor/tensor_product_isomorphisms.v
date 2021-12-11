Require Import init.

Require Import linear_bilinear.
Require Import tensor_product_universal.

Require Import set.
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
Let f := tensor_product_comm_f.

Theorem tensor_product_comm_eq : ∀ a b, f (a ⊗12 b) = b ⊗21 a.
    apply (ex_proof tensor_product_comm).
Qed.

Theorem tensor_product_comm_plus : ∀ a b, f (a + b) = f a + f b.
    apply (@module_homo_plus _ _ _ (ex_val tensor_product_comm)).
Qed.
Theorem tensor_product_comm_scalar : ∀ a v, f (a · v) = a · f v.
    apply (@module_homo_scalar _ _ _ (ex_val tensor_product_comm)).
Qed.

Theorem tensor_product_comm_bij : bijective f.
    pose proof (land (ex_proof tensor_product_comm))
        as [[g g_plus g_scalar] [fg gf]].
    cbn in *.
    unfold module_homo_compose, module_homo_id in *; cbn in *.
    inversion fg as [fg']; clear fg.
    inversion gf as [gf']; clear gf.
    apply (inverse_ex_bijective f g).
    -   apply func_eq.
        exact fg'.
    -   apply func_eq.
        exact gf'.
Qed.

End TensorProductIsomorphisms.
