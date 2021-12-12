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

Context V3 `{
    VP3 : Plus V3,
    VZ3 : Zero V3,
    VN3 : Neg V3,
    VPA3 : @PlusAssoc V3 VP3,
    VPC3 : @PlusComm V3 VP3,
    VPZ3 : @PlusLid V3 VP3 VZ3,
    VPN3 : @PlusLinv V3 VP3 VZ3 VN3,

    SM3 : ScalarMult U V3,
    SMO3 : @ScalarId U V3 UO SM3,
    SML3 : @ScalarLdist U V3 VP3 SM3,
    SMR3 : @ScalarRdist U V3 UP VP3 SM3,
    SMC3 : @ScalarComp U V3 UM SM3
}.

Local Infix "⊗23" := (tensor_mult U V2 V3) (at level 40, left associativity).
Local Infix "⊗1_23" := (tensor_mult U V1 (module_V (tensor_product U V2 V3)))
    (at level 40, left associativity).
Local Infix "⊗12_3" := (tensor_mult U (module_V (tensor_product U V1 V2)) V3)
    (at level 40, left associativity).

Let T12_zero := module_zero (tensor_product U V1 V2).
Let T12_neg := module_neg (tensor_product U V1 V2).
Let T12_plus_comm := module_plus_comm (tensor_product U V1 V2).
Let T12_plus_assoc := module_plus_assoc (tensor_product U V1 V2).
Let T12_plus_lid := module_plus_lid (tensor_product U V1 V2).
Let T12_plus_linv := module_plus_linv (tensor_product U V1 V2).
Let T12_scalar_comp := module_scalar_comp (tensor_product U V1 V2).
Let T12_scalar_id := module_scalar_id (tensor_product U V1 V2).
Let T12_scalar_ldist := module_scalar_ldist (tensor_product U V1 V2).
Let T12_scalar_rdist := module_scalar_rdist (tensor_product U V1 V2).
Let T23_plus := module_plus (tensor_product U V2 V3).
Let T23_zero := module_zero (tensor_product U V2 V3).
Let T23_neg := module_neg (tensor_product U V2 V3).
Let T23_plus_comm := module_plus_comm (tensor_product U V2 V3).
Let T23_plus_assoc := module_plus_assoc (tensor_product U V2 V3).
Let T23_plus_lid := module_plus_lid (tensor_product U V2 V3).
Let T23_plus_linv := module_plus_linv (tensor_product U V2 V3).
Let T23_scalar := module_scalar (tensor_product U V2 V3).
Let T23_scalar_comp := module_scalar_comp (tensor_product U V2 V3).
Let T23_scalar_id := module_scalar_id (tensor_product U V2 V3).
Let T23_scalar_ldist := module_scalar_ldist (tensor_product U V2 V3).
Let T23_scalar_rdist := module_scalar_rdist (tensor_product U V2 V3).
Existing Instances T12_zero T12_neg T12_plus_comm T12_plus_assoc T12_plus_lid
    T12_plus_linv T12_scalar_comp T12_scalar_id T12_scalar_ldist
    T12_scalar_rdist T23_plus T23_zero T23_neg T23_plus_comm T23_plus_assoc
    T23_plus_lid T23_plus_linv T23_scalar T23_scalar_comp T23_scalar_id
    T23_scalar_ldist T23_scalar_rdist.
Let T1_23_plus := module_plus
    (tensor_product U V1 (module_V (tensor_product U V2 V3))).
Let T1_23_scalar := module_scalar
    (tensor_product U V1 (module_V (tensor_product U V2 V3))).
Let T12_3_plus := module_plus
    (tensor_product U (module_V (tensor_product U V1 V2)) V3).
Let T12_3_scalar := module_scalar
    (tensor_product U (module_V (tensor_product U V1 V2)) V3).
Existing Instances T1_23_plus T1_23_scalar T12_3_plus T12_3_scalar.

Theorem tensor_product_assoc :
    ∃ f : ModuleHomomorphism
            (tensor_product U V1 (module_V (tensor_product U V2 V3)))
            (tensor_product U (module_V (tensor_product U V1 V2)) V3),
        isomorphism (C0 := MODULE (scalar_cring U)) f ∧
        ∀ a b c, module_homo_f f (a ⊗1_23 (b ⊗23 c)) = (a ⊗12 b) ⊗12_3 c.
    pose (T1_23_zero := module_zero
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T1_23_neg := module_neg
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T1_23_plus_comm := module_plus_comm
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T1_23_plus_assoc := module_plus_assoc
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T1_23_plus_lid := module_plus_lid
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T1_23_plus_linv := module_plus_linv
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T1_23_scalar_comp := module_scalar_comp
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T1_23_scalar_id := module_scalar_id
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T1_23_scalar_ldist := module_scalar_ldist
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T1_23_scalar_rdist := module_scalar_rdist
        (tensor_product U V1 (module_V (tensor_product U V2 V3)))).
    pose (T12_3_zero := module_zero
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (T12_3_neg := module_neg
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (T12_3_plus_comm := module_plus_comm
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (T12_3_plus_assoc := module_plus_assoc
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (T12_3_plus_lid := module_plus_lid
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (T12_3_plus_linv := module_plus_linv
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (T12_3_scalar_comp := module_scalar_comp
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (T12_3_scalar_id := module_scalar_id
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (T12_3_scalar_ldist := module_scalar_ldist
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (T12_3_scalar_rdist := module_scalar_rdist
        (tensor_product U (module_V (tensor_product U V1 V2)) V3)).
    pose (f1 a b c := (a ⊗12 b) ⊗12_3 c).
    assert (∀ a, bilinear (f1 a)) as f1_bil.
    {
        intros v.
        unfold f1.
        repeat split; intros.
        -   rewrite tensor_rscalar.
            rewrite tensor_lscalar.
            reflexivity.
        -   rewrite tensor_rscalar.
            reflexivity.
        -   rewrite tensor_ldist.
            rewrite tensor_rdist.
            reflexivity.
        -   rewrite tensor_ldist.
            reflexivity.
    }
    pose (f2_base a := make_bilinear _ _ _ _ _ (f1_bil a)).
    pose (f2 a := card_one_ex (tensor_product_universal _ _ _ (f2_base a))).
    cbn in f2.
    pose (f3 a b := module_homo_f [f2 a|] b).
    assert (bilinear f3) as f3_bil.
    {
        repeat split; intros.
        -   unfold f3.
            unfold f2.
            destruct (card_one_ex _) as [fav fav_in].
            destruct (card_one_ex _) as [fv fv_in].
            cbn.
            unfold bilinear_from_set in fav_in, fv_in; cbn in *.
            pose proof (tensor_sum _ _ _ v2) as [l v2_eq]; subst v2.
            induction l.
            +   cbn.
                rewrite <- (scalar_lanni 0).
                rewrite (@module_homo_scalar _ _ _ fav).
                rewrite (@module_homo_scalar _ _ _ fv).
                do 2 rewrite scalar_lanni.
                rewrite scalar_ranni.
                reflexivity.
            +   cbn.
                rewrite (@module_homo_plus _ _ _ fav).
                rewrite (@module_homo_plus _ _ _ fv).
                rewrite scalar_ldist.
                rewrite <- IHl.
                apply rplus.
                destruct a0 as [a0 [u [v eq]]]; subst a0; cbn.
                unfold tensor_mult; cbn.
                rewrite fav_in, fv_in.
                unfold f1.
                rewrite tensor_lscalar.
                rewrite tensor_lscalar.
                reflexivity.
        -   unfold f3.
            apply (@module_homo_scalar _ _ _ [f2 v1|]).
        -   unfold f3.
            unfold f2.
            destruct (card_one_ex _) as [fv12 fv12_in].
            destruct (card_one_ex _) as [fv1 fv1_in].
            destruct (card_one_ex _) as [fv2 fv2_in].
            cbn.
            unfold bilinear_from_set in fv12_in, fv1_in, fv2_in; cbn in *.
            pose proof (tensor_sum _ _ _ v3) as [l v3_eq]; subst v3.
            induction l.
            +   cbn.
                rewrite <- (scalar_lanni 0).
                rewrite (@module_homo_scalar _ _ _ fv12).
                rewrite (@module_homo_scalar _ _ _ fv1).
                rewrite (@module_homo_scalar _ _ _ fv2).
                do 3 rewrite scalar_lanni.
                rewrite plus_lid.
                reflexivity.
            +   cbn.
                rewrite (@module_homo_plus _ _ _ fv12).
                rewrite (@module_homo_plus _ _ _ fv1).
                rewrite (@module_homo_plus _ _ _ fv2).
                rewrite IHl; clear IHl.
                do 2 rewrite plus_assoc.
                apply rplus.
                rewrite plus_comm.
                rewrite (plus_comm (module_homo_f fv1 [a|])).
                rewrite <- plus_assoc.
                apply lplus.
                destruct a as [a [u [v eq]]]; subst a; cbn.
                unfold tensor_mult; rewrite fv12_in, fv1_in, fv2_in.
                unfold f1.
                do 2 rewrite tensor_rdist.
                reflexivity.
        -   unfold f3.
            apply (@module_homo_plus _ _ _ [f2 v1|]).
    }
    pose (f_base := make_bilinear _ _ _ _ _ f3_bil).
    pose proof (tensor_product_universal _ _ _ f_base) as f_ex.
    apply card_one_ex in f_ex as [f f_in].
    cbn in *.
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
            -   rewrite tensor_lscalar.
                reflexivity.
            -   rewrite tensor_lscalar.
                rewrite tensor_rscalar.
                reflexivity.
            -   rewrite tensor_rdist.
                reflexivity.
            -   rewrite tensor_rdist.
                rewrite tensor_ldist.
                reflexivity.
        }
        pose (g2_base c := make_bilinear _ _ _ _ _ (g1_bil c)).
        pose (g2 c := card_one_ex (tensor_product_universal _ _ _ (g2_base c))).
        cbn in g2.
        pose (g3 b a := module_homo_f [g2 a|] b).
        assert (bilinear g3) as g3_bil.
        {
            repeat split; intros.
            -   unfold g3.
                apply (@module_homo_scalar _ _ _ [g2 v2|]).
            -   unfold g3.
                unfold g2.
                destruct (card_one_ex _) as [gav gav_in].
                destruct (card_one_ex _) as [gv gv_in].
                cbn.
                unfold bilinear_from_set in gav_in, gv_in; cbn in *.
                pose proof (tensor_sum _ _ _ v1) as [l v1_eq]; subst v1.
                induction l.
                +   cbn.
                    rewrite <- (scalar_lanni 0).
                    rewrite (@module_homo_scalar _ _ _ gav).
                    rewrite (@module_homo_scalar _ _ _ gv).
                    do 2 rewrite scalar_lanni.
                    rewrite scalar_ranni.
                    reflexivity.
                +   cbn.
                    rewrite (@module_homo_plus _ _ _ gav).
                    rewrite (@module_homo_plus _ _ _ gv).
                    rewrite scalar_ldist.
                    rewrite <- IHl.
                    apply rplus.
                    destruct a0 as [a0 [u [v eq]]]; subst a0; cbn.
                    unfold tensor_mult; cbn.
                    rewrite gav_in, gv_in.
                    unfold g1.
                    rewrite tensor_rscalar.
                    rewrite tensor_rscalar.
                    reflexivity.
            -   unfold g3.
                apply (@module_homo_plus _ _ _ [g2 v3|]).
            -   unfold g3.
                unfold g2.
                destruct (card_one_ex _) as [gv12 gv12_in].
                destruct (card_one_ex _) as [gv1 gv1_in].
                destruct (card_one_ex _) as [gv2 gv2_in].
                cbn.
                unfold bilinear_from_set in gv12_in, gv1_in, gv2_in; cbn in *.
                pose proof (tensor_sum _ _ _ v1) as [l v1_eq]; subst v1.
                induction l.
                +   cbn.
                    rewrite <- (scalar_lanni 0).
                    rewrite (@module_homo_scalar _ _ _ gv12).
                    rewrite (@module_homo_scalar _ _ _ gv1).
                    rewrite (@module_homo_scalar _ _ _ gv2).
                    do 3 rewrite scalar_lanni.
                    rewrite plus_lid.
                    reflexivity.
                +   cbn.
                    rewrite (@module_homo_plus _ _ _ gv12).
                    rewrite (@module_homo_plus _ _ _ gv1).
                    rewrite (@module_homo_plus _ _ _ gv2).
                    rewrite IHl; clear IHl.
                    do 2 rewrite plus_assoc.
                    apply rplus.
                    rewrite plus_comm.
                    rewrite (plus_comm (module_homo_f gv1 [a|])).
                    rewrite <- plus_assoc.
                    apply lplus.
                    destruct a as [a [u [v eq]]]; subst a; cbn.
                    unfold tensor_mult; rewrite gv12_in, gv1_in, gv2_in.
                    unfold g1.
                    do 2 rewrite tensor_ldist.
                    reflexivity.
        }
        pose (g_base := make_bilinear _ _ _ _ _ g3_bil).
        pose proof (tensor_product_universal _ _ _ g_base) as g_ex.
        apply card_one_ex in g_ex as [g g_in].
        cbn in *.
        unfold bilinear_from_set in g_in; cbn in g_in.
        clear g_base.
        exists g.
        cbn.
        unfold module_homo_compose, module_homo_id; cbn.
        split; apply module_homomorphism_eq; cbn.
        +   intros x.
            pose proof (tensor_sum _ _ _ x) as [l1 x_eq]; subst x.
            induction l1.
            *   cbn.
                rewrite <- (scalar_lanni 0) at 1.
                rewrite (@module_homo_scalar _ _ _ g).
                rewrite (@module_homo_scalar _ _ _ f).
                apply scalar_lanni.
            *   cbn.
                rewrite (@module_homo_plus _ _ _ g).
                rewrite (@module_homo_plus _ _ _ f).
                cbn in *.
                rewrite <- IHl1 at 2; clear IHl1.
                apply rplus.
                destruct a as [a [u [v a_eq]]]; subst a; cbn.
                unfold tensor_mult at 1; rewrite g_in.
                unfold g3.
                unfold g2.
                destruct (card_one_ex _) as [h h_in].
                cbn.
                unfold bilinear_from_set in h_in.
                pose proof (tensor_sum _ _ _ u) as [l2 u_eq]; subst u.
                induction l2.
                --  cbn.
                    rewrite tensor_product_lanni by exact T12_plus_lid.
                    rewrite <- (scalar_lanni 0) at 1.
                    rewrite (@module_homo_scalar _ _ _ h).
                    rewrite (@module_homo_scalar _ _ _ f).
                    apply scalar_lanni.
                --  cbn.
                    rewrite (@module_homo_plus _ _ _ h).
                    rewrite (@module_homo_plus _ _ _ f).
                    rewrite IHl2.
                    rewrite tensor_rdist.
                    apply rplus.
                    destruct a as [a [u' [v' eq]]]; subst a.
                    cbn.
                    unfold tensor_mult at 1; rewrite h_in.
                    unfold g2_base; cbn.
                    unfold g1.
                    unfold tensor_mult at 1 2; rewrite f_in.
                    unfold f3, f2.
                    destruct (card_one_ex _) as [h' h'_in].
                    unfold bilinear_from_set in h'_in; cbn in *.
                    rewrite h'_in.
                    unfold f1.
                    reflexivity.
        +   intros x.
            pose proof (tensor_sum _ _ _ x) as [l x_eq]; subst x.
            induction l.
            *   cbn.
                rewrite <- (scalar_lanni 0) at 1.
                rewrite (@module_homo_scalar _ _ _ f).
                rewrite (@module_homo_scalar _ _ _ g).
                apply scalar_lanni.
            *   cbn.
                rewrite (@module_homo_plus _ _ _ f).
                rewrite (@module_homo_plus _ _ _ g).
                cbn in *.
                rewrite <- IHl at 2; clear IHl.
                apply rplus.
                destruct a as [a [u [v a_eq]]]; subst a; cbn.
                unfold tensor_mult at 1; rewrite f_in.
                unfold f3, f2.
                destruct (card_one_ex _) as [h h_in].
                cbn.
                unfold bilinear_from_set in h_in.
                pose proof (tensor_sum _ _ _ v) as [l2 v_eq]; subst v.
                induction l2.
                --  cbn.
                    rewrite tensor_product_ranni by exact T23_plus_lid.
                    rewrite <- (scalar_lanni 0) at 1.
                    rewrite (@module_homo_scalar _ _ _ h).
                    rewrite (@module_homo_scalar _ _ _ g).
                    apply scalar_lanni.
                --  cbn.
                    rewrite (@module_homo_plus _ _ _ h).
                    rewrite (@module_homo_plus _ _ _ g).
                    rewrite IHl2; clear IHl2.
                    rewrite tensor_ldist.
                    apply rplus.
                    destruct a as [a [u' [v' eq]]]; subst a.
                    cbn.
                    unfold tensor_mult at 1; rewrite h_in.
                    unfold f2_base; cbn.
                    unfold f1.
                    unfold tensor_mult at 1 2; rewrite g_in.
                    unfold g3, g2.
                    destruct (card_one_ex _) as [h' h'_in].
                    unfold bilinear_from_set in h'_in; cbn in *.
                    rewrite h'_in.
                    unfold g1.
                    reflexivity.
    -   intros a b c.
        unfold tensor_mult at 1 2.
        rewrite f_in.
        unfold f3, f2.
        destruct (card_one_ex _) as [fa fa_in].
        cbn.
        unfold bilinear_from_set in fa_in.
        rewrite fa_in.
        reflexivity.
Qed.

Definition tensor_product_assoc_f := module_homo_f (ex_val tensor_product_assoc).
Let af := tensor_product_assoc_f.

Theorem tensor_product_assoc_eq :
        ∀ a b c, af (a ⊗1_23 (b ⊗23 c)) = (a ⊗12 b) ⊗12_3 c.
    apply (ex_proof tensor_product_assoc).
Qed.

Theorem tensor_product_assoc_plus : ∀ a b, af (a + b) = af a + af b.
    apply (@module_homo_plus _ _ _ (ex_val tensor_product_assoc)).
Qed.
Theorem tensor_product_assoc_scalar : ∀ a v, af (a · v) = a · af v.
    apply (@module_homo_scalar _ _ _ (ex_val tensor_product_assoc)).
Qed.

Theorem tensor_product_assoc_bij : bijective af.
    pose proof (land (ex_proof tensor_product_assoc))
        as [[g g_plus g_scalar] [fg gf]].
    cbn in *.
    unfold module_homo_compose, module_homo_id in *; cbn in *.
    inversion fg as [fg']; clear fg.
    inversion gf as [gf']; clear gf.
    apply (inverse_ex_bijective af g).
    -   apply func_eq.
        exact fg'.
    -   apply func_eq.
        exact gf'.
Qed.

End TensorProductIsomorphisms.
