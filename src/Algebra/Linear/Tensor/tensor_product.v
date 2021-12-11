Require Import init.

Require Export linear_base.
Require Import linear_free.
Require Import linear_subspace.
Require Import linear_span.
Require Import linear_bilinear.

Require Import set.
Require Import card.

Require Import list.
Require Import plus_sum.

Require Import category_base.
Require Import module_category.
Require Import category_slice.
Require Import category_initterm.

Section TensorProduct.

Context U V1 V2 `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @MultAssoc U UM,
    @MultComm U UM,
    @MultLid U UM UO,
    @Ldist U UP UM,

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

Let FR := free_linear U (V1 * V2).
Let to_FR a b := to_free U (V1 * V2) (a, b).

Let FR_plus := free_plus_class U (V1 * V2).
Let FR_zero := free_zero U (V1 * V2).
Let FR_neg := free_neg U (V1 * V2).
Let FR_plus_comm := free_plus_comm_class U (V1 * V2).
Let FR_plus_assoc := free_plus_assoc_class U (V1 * V2).
Let FR_plus_lid := free_plus_lid_class U (V1 * V2).
Let FR_plus_linv := free_plus_linv_class U (V1 * V2).
Let FR_scalar := free_scalar U (V1 * V2).
Let FR_scalar_id := free_scalar_id_class U (V1 * V2).
Let FR_scalar_ldist := free_scalar_ldist_class U (V1 * V2).
Let FR_scalar_rdist := free_scalar_rdist_class U (V1 * V2).
Let FR_scalar_comp := free_scalar_comp_class U (V1 * V2).
Existing Instances FR_plus FR_zero FR_neg FR_plus_comm FR_plus_assoc FR_plus_lid
    FR_plus_linv FR_scalar FR_scalar_id FR_scalar_ldist FR_scalar_rdist
    FR_scalar_comp.

Let sub1 v := ∃ a b c, v = to_FR (a + b) c - to_FR a c - to_FR b c.
Let sub2 v := ∃ a b c, v = to_FR a (b + c) - to_FR a b - to_FR a c.
Let sub3 v := ∃ a m n, v = a · to_FR m n - to_FR (a · m) n.
Let sub4 v := ∃ a m n, v = a · to_FR m n - to_FR m (a · n).
Definition tensor_product_ideal := sub1 ∪ sub2 ∪ sub3 ∪ sub4.

Definition tensor_space := linear_span_quotient U tensor_product_ideal.
Definition tensor_mult_base a b := to_quotient U tensor_product_ideal (to_free U (V1 * V2) (a, b)).
Local Infix "⊗" := tensor_mult_base.

Definition tensor_plus := quotient_space_plus (linear_span_subspace U tensor_product_ideal).
Definition tensor_zero := quotient_space_zero (linear_span_subspace U tensor_product_ideal).
Definition tensor_neg := quotient_space_neg (linear_span_subspace U tensor_product_ideal).
Definition tensor_plus_assoc := quotient_space_plus_assoc (linear_span_subspace U tensor_product_ideal).
Definition tensor_plus_comm := quotient_space_plus_comm (linear_span_subspace U tensor_product_ideal).
Definition tensor_plus_lid := quotient_space_plus_lid (linear_span_subspace U tensor_product_ideal).
Definition tensor_plus_linv := quotient_space_plus_linv (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_mult := quotient_space_scalar_mult (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_id := quotient_space_scalar_id (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_ldist := quotient_space_scalar_ldist (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_rdist := quotient_space_scalar_rdist (linear_span_subspace U tensor_product_ideal).
Definition tensor_scalar_comp := quotient_space_scalar_comp (linear_span_subspace U tensor_product_ideal).
Existing Instances tensor_plus tensor_zero tensor_neg tensor_plus_assoc
    tensor_plus_comm tensor_plus_lid tensor_plus_linv tensor_scalar_mult
    tensor_scalar_id tensor_scalar_ldist tensor_scalar_rdist tensor_scalar_comp.

Theorem tensor_ldist_base : ∀ a b c, a ⊗ (b + c) = a ⊗ b + a ⊗ c.
    intros a b c.
    unfold tensor_mult_base; cbn.
    unfold plus at 2; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    left; left; right.
    exists a, b, c.
    unfold to_FR.
    rewrite neg_plus.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem tensor_rdist_base : ∀ a b c, (a + b) ⊗ c = a ⊗ c + b ⊗ c.
    intros a b c.
    unfold tensor_mult_base, plus at 2; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    repeat left.
    exists a, b, c.
    unfold to_FR.
    rewrite neg_plus.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem tensor_lscalar_base : ∀ a u v, (a · u) ⊗ v = a · (u ⊗ v).
    intros a u v.
    symmetry.
    unfold tensor_mult_base, scalar_mult; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    left; right.
    exists a, u, v; cbn.
    unfold to_FR.
    reflexivity.
Qed.

Theorem tensor_rscalar_base : ∀ a u v, u ⊗ (a · v) = a · (u ⊗ v).
    intros a u v.
    symmetry.
    unfold tensor_mult_base, scalar_mult; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    right.
    exists a, u, v; cbn.
    unfold to_FR.
    reflexivity.
Qed.

Theorem tensor_mult_lneg_base : ∀ u v, (-u) ⊗ v = -(u ⊗ v).
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite tensor_lscalar_base.
    apply scalar_neg_one.
Qed.
Theorem tensor_mult_rneg_base : ∀ u v, u ⊗ (-v) = -(u ⊗ v).
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite tensor_rscalar_base.
    apply scalar_neg_one.
Qed.

Definition simple_tensor T := ∃ a b, T = a ⊗ b.

Local Open Scope card_scope.

Theorem tensor_sum : ∀ T, ∃ l : list (set_type simple_tensor),
        T = list_sum (list_image l (λ x, [x|])).
    intros T.
    equiv_get_value T.
    pose proof (free_fin T) as T_fin.
    apply fin_nat_ex in T_fin as [n n_eq].
    revert T n_eq.
    nat_induction n.
    {
        intros T eq.
        exists list_end.
        cbn.
        unfold zero; cbn.
        apply f_equal.
        apply free_eq.
        intros x.
        classic_contradiction contr.
        apply zero_is_empty in eq.
        assert (∅ x) as x_in.
        {
            rewrite <- eq.
            exact contr.
        }
        contradiction x_in.
    }
    intros T T_size.
    change (nat_suc n) with (1 + n) in T_size.
    rewrite <- nat_to_card_plus in T_size.
    unfold plus, nat_to_card in T_size; equiv_simpl in T_size.
    destruct T_size as [f [f_inj f_sur]].
    pose (x := f (inl [0|nat_0_lt_1])).
    pose (T' v := If v = [x|] then 0 else free_f T v).
    assert (nat_to_card n = |set_type (λ x, T' x ≠ 0)|) as T'n.
    {
        unfold nat_to_card; equiv_simpl.
        assert (∀ m : set_type (λ x, x < n), T' [f (inr m)|] ≠ 0) as T'_neq.
        {
            intros m.
            unfold T'.
            case_if.
            -   unfold x in e.
                apply set_type_eq in e.
                apply f_inj in e.
                inversion e.
            -   destruct (f (inr m)) as [fm fm_neq].
                exact fm_neq.
        }
        exists (λ m, [[f (inr m)|] | T'_neq m]).
        split.
        -   intros a b eq.
            apply eq_set_type in eq; cbn in eq.
            apply set_type_eq in eq; cbn in eq.
            apply f_inj in eq.
            inversion eq.
            reflexivity.
        -   intros [b b_neq].
            assert (free_f T b ≠ 0) as b_neq2.
            {
                unfold T' in b_neq.
                case_if.
                1: contradiction.
                exact b_neq.
            }
            specialize (f_sur [b|b_neq2]) as [a a_eq].
            apply eq_set_type in a_eq; cbn in a_eq.
            destruct a as [a|a].
            +   unfold T' in b_neq.
                exfalso.
                case_if.
                1: contradiction.
                rewrite <- a_eq in n0.
                apply n0.
                apply eq_set_type.
                unfold x.
                apply f_equal.
                apply f_equal.
                destruct a as [a a_lt].
                apply set_type_eq; cbn.
                clear - a_lt.
                apply nat_lt_1 in a_lt.
                symmetry; exact a_lt.
            +   exists a.
                subst b.
                apply set_type_eq; cbn.
                reflexivity.
    }
    assert (finite (|set_type (λ x, T' x ≠ 0)|)) as T'_fin.
    {
        rewrite <- T'n.
        apply nat_is_finite.
    }
    specialize (IHn (make_free T' T'_fin) T'n) as [l l_eq].
    pose (x' := free_f T [x|] · (fst [x|] ⊗ snd [x|])).
    assert (simple_tensor x') as x'_simple.
    {
        exists (free_f T [x|] · fst [x|]), (snd [x|]).
        unfold x'.
        rewrite tensor_lscalar_base.
        reflexivity.
    }
    exists ([x'|x'_simple] :: l).
    cbn.
    unfold x'.
    clear x' x'_simple.
    rewrite <- l_eq.
    assert (T = free_f T [x|] · to_FR (fst [x|]) (snd [x|]) + (make_free T' T'_fin)) as eq.
    {
        apply free_eq.
        intros v.
        unfold T'.
        unfold plus; cbn.
        unfold scalar_mult; cbn.
        replace (fst [x|], snd [x|]) with [x|].
        2: destruct [x|]; reflexivity.
        case_if.
        -   subst v.
            rewrite plus_rid.
            rewrite mult_rid.
            reflexivity.
        -   rewrite mult_ranni.
            rewrite plus_lid.
            reflexivity.
    }
    unfold scalar_mult, plus, tensor_mult_base, to_quotient; cbn.
    rewrite eq at 1.
    equiv_simpl.
    rewrite neg_plus.
    rewrite (plus_comm (_ · to_FR _ _)).
    rewrite plus_assoc.
    rewrite <- (plus_assoc _ (_ · to_FR _ _)).
    rewrite plus_rinv.
    rewrite plus_rid.
    rewrite plus_rinv.
    apply linear_span_zero.
Qed.

Definition tensor_list_to_free (l : list (set_type simple_tensor))
    := list_sum (list_image l (λ t, to_FR (ex_val [|t]) (ex_val (ex_proof [|t])))).
Definition tensor_to_free (T : tensor_space)
    := tensor_list_to_free (ex_val (tensor_sum T)).

End TensorProduct.

Section TensorProductCategory.

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

Definition tensor_product_base := make_module
    (scalar_cring U)
    (tensor_space U V1 V2)
    (tensor_plus U V1 V2)
    (tensor_zero U V1 V2)
    (tensor_neg U V1 V2)
    (tensor_plus_assoc U V1 V2)
    (tensor_plus_comm U V1 V2)
    (tensor_plus_lid U V1 V2)
    (tensor_plus_linv U V1 V2)
    (tensor_scalar_mult U V1 V2)
    (tensor_scalar_id U V1 V2)
    (tensor_scalar_ldist U V1 V2)
    (tensor_scalar_rdist U V1 V2)
    (tensor_scalar_comp U V1 V2).

Record bilinear_from := make_bilinear {
    bilinear_from_module : Module (scalar_cring U);
    bilinear_from_f : V1 → V2 → module_V bilinear_from_module;
    bilinear_from_bi : bilinear
        (H1 := module_plus bilinear_from_module)
        (H4 := module_scalar bilinear_from_module)
        bilinear_from_f;
}.

Definition bilinear_from_set (f g : bilinear_from)
    (h : cat_morphism (MODULE (scalar_cring U))
                      (bilinear_from_module f)
                      (bilinear_from_module g))
    := ∀ x y, module_homo_f h (bilinear_from_f f x y) = bilinear_from_f g x y.

Definition bilinear_from_compose {F G H : bilinear_from}
    (f : set_type (bilinear_from_set G H)) (g : set_type (bilinear_from_set F G))
    := [f|] ∘ [g|].

Lemma bilinear_from_set_compose_in
        {F G H : bilinear_from} : ∀ (f : set_type (bilinear_from_set G H)) g,
        bilinear_from_set F H (bilinear_from_compose f g).
    intros [f f_eq] [g g_eq].
    unfold bilinear_from_set in *.
    unfold bilinear_from_compose; cbn.
    intros x y.
    rewrite g_eq.
    apply f_eq.
Qed.

Lemma bilinear_from_set_id_in
        : ∀ f : bilinear_from, bilinear_from_set f f 𝟙.
    intros f.
    unfold bilinear_from_set.
    intros x y.
    cbn.
    reflexivity.
Qed.

Program Instance BILINEAR_FROM : Category := {
    cat_U := bilinear_from;
    cat_morphism f g := set_type (bilinear_from_set f g);
    cat_compose {F G H} f g := [_|bilinear_from_set_compose_in f g];
    cat_id f := [_|bilinear_from_set_id_in f];
}.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_assoc (MODULE (scalar_cring U))).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_lid (MODULE (scalar_cring U))).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_rid (MODULE (scalar_cring U))).
Qed.

Let FR_plus := free_plus_class U (V1 * V2).
Let FR_zero := free_zero U (V1 * V2).
Let FR_neg := free_neg U (V1 * V2).
Let FR_plus_comm := free_plus_comm_class U (V1 * V2).
Let FR_plus_assoc := free_plus_assoc_class U (V1 * V2).
Let FR_plus_lid := free_plus_lid_class U (V1 * V2).
Let FR_plus_linv := free_plus_linv_class U (V1 * V2).
Let FR_scalar := free_scalar U (V1 * V2).
Let FR_scalar_id := free_scalar_id_class U (V1 * V2).
Let FR_scalar_ldist := free_scalar_ldist_class U (V1 * V2).
Let FR_scalar_rdist := free_scalar_rdist_class U (V1 * V2).
Let FR_scalar_comp := free_scalar_comp_class U (V1 * V2).
Existing Instances FR_plus FR_zero FR_neg FR_plus_comm FR_plus_assoc FR_plus_lid
    FR_plus_linv FR_scalar FR_scalar_id FR_scalar_ldist FR_scalar_rdist
    FR_scalar_comp.

Theorem tensor_product_ex : ∃ T, @initial BILINEAR_FROM T.
    pose (V3P := module_plus tensor_product_base).
    pose (SM3 := module_scalar tensor_product_base).
    pose (f x y := tensor_mult_base U V1 V2 x y).
    assert (bilinear f) as f_bil.
    {
        repeat split.
        -   apply tensor_lscalar_base.
        -   apply tensor_rscalar_base.
        -   apply tensor_rdist_base.
        -   apply tensor_ldist_base.
    }
    exists (make_bilinear tensor_product_base f f_bil).
    unfold initial; cbn.
    intros g.
    pose (tp := module_plus (tensor_product_base)).
    pose (tz := module_zero (tensor_product_base)).
    pose (tn := module_neg (tensor_product_base)).
    pose (tpa := module_plus_assoc (tensor_product_base)).
    pose (tpc := module_plus_comm (tensor_product_base)).
    pose (tpz := module_plus_lid (tensor_product_base)).
    pose (tpn := module_plus_linv (tensor_product_base)).
    pose (tsm := module_scalar (tensor_product_base)).
    pose (tsc := module_scalar_comp (tensor_product_base)).
    pose (tso := module_scalar_id (tensor_product_base)).
    pose (tsl := module_scalar_ldist (tensor_product_base)).
    pose (tsr := module_scalar_rdist (tensor_product_base)).
    pose (gP := module_plus (bilinear_from_module g)).
    pose (gZ := module_zero (bilinear_from_module g)).
    pose (gN := module_neg (bilinear_from_module g)).
    pose (gPA := module_plus_assoc (bilinear_from_module g)).
    pose (gPC := module_plus_comm (bilinear_from_module g)).
    pose (gPZ := module_plus_lid (bilinear_from_module g)).
    pose (gPN := module_plus_linv (bilinear_from_module g)).
    pose (gSM := module_scalar (bilinear_from_module g)).
    pose (gSO := module_scalar_id (bilinear_from_module g)).
    pose (gSL := module_scalar_ldist (bilinear_from_module g)).
    pose (gSR := module_scalar_rdist (bilinear_from_module g)).
    apply card_unique_one.
    -   apply ex_set_type.
        pose (h1 x := bilinear_from_f g (fst x) (snd x)).
        pose (h2 := make_free_from U (V1 * V2) (bilinear_from_module g) h1).
        pose proof (free_module_universal U (V1 * V2) h2) as uni.
        cbn in uni.
        apply card_one_ex in uni as [h3 h3_free_from].
        unfold free_from_set in h3_free_from.
        cbn in h3_free_from.
        pose (h4 := module_homo_f h3).
        cbn in h4.
        pose (h3_plus := @module_homo_plus _ _ _ h3).
        pose (h3_scalar := @module_homo_scalar _ _ _ h3).
        assert (∀ x y, eq_equal (subspace_equiv (linear_span_subspace U
            (tensor_product_ideal U V1 V2))) x y → h4 x = h4 y) as wd.
        {
            intros x y eq.
            cbn in eq.
            unfold h4.
            apply plus_0_anb_a_b.
            rewrite <- scalar_neg_one.
            rewrite <- h3_scalar.
            rewrite scalar_neg_one.
            rewrite <- h3_plus.
            rewrite (span_linear_combination _ (tensor_product_ideal U V1 V2)) in eq.
            destruct eq as [l [l_eq l_in]].
            cbn in *.
            unfold FR_plus in l_eq.
            rewrite l_eq; clear l_eq.
            destruct l as [l l_comb]; cbn in *.
            unfold linear_list_in in l_in; cbn in l_in; clear l_comb.
            induction l.
            -   cbn.
                rewrite <- (scalar_lanni (V := free_linear U (V1 * V2)) 0).
                rewrite h3_scalar.
                rewrite scalar_lanni.
                reflexivity.
            -   assert (∀ v, (∃ α, in_list l (α, v)) →
                    tensor_product_ideal U V1 V2 v) as IHl'.
                {
                    intros v [α v_in].
                    apply l_in.
                    exists α.
                    right.
                    exact v_in.
                }
                specialize (IHl IHl'); clear IHl'.
                cbn.
                rewrite h3_plus.
                rewrite <- IHl; clear IHl.
                rewrite plus_rid.
                rewrite h3_scalar.
                assert (tensor_product_ideal U V1 V2 (snd a)) as a_in.
                {
                    apply l_in.
                    exists (fst a).
                    left; destruct a; reflexivity.
                }
                pose proof (bilinear_from_bi g) as
                    [g_lscalar [g_rscalar [g_rdist g_ldist]]].
                cbn in *.
                destruct a_in as [[[a_in|a_in]|a_in]|a_in].
                +   destruct a_in as [u [v [w eq]]].
                    rewrite eq; clear eq.
                    rewrite h3_plus.
                    rewrite h3_plus.
                    rewrite <- scalar_neg_one.
                    rewrite <- (scalar_neg_one (V := free_linear U (V1 * V2))).
                    do 2 rewrite h3_scalar.
                    do 2 rewrite scalar_neg_one.
                    do 3 rewrite h3_free_from.
                    unfold h1; cbn.
                    rewrite <- plus_assoc.
                    rewrite <- neg_plus.
                    rewrite <- g_rdist.
                    rewrite plus_rinv.
                    rewrite scalar_ranni.
                    reflexivity.
                +   destruct a_in as [u [v [w eq]]].
                    rewrite eq; clear eq.
                    rewrite h3_plus.
                    rewrite h3_plus.
                    rewrite <- scalar_neg_one.
                    rewrite <- (scalar_neg_one (V := free_linear U (V1 * V2))).
                    do 2 rewrite h3_scalar.
                    do 2 rewrite scalar_neg_one.
                    do 3 rewrite h3_free_from.
                    unfold h1; cbn.
                    rewrite <- plus_assoc.
                    rewrite <- neg_plus.
                    rewrite <- g_ldist.
                    rewrite plus_rinv.
                    rewrite scalar_ranni.
                    reflexivity.
                +   destruct a_in as [α [u [v eq]]].
                    rewrite eq; clear eq.
                    rewrite h3_plus.
                    rewrite <- scalar_neg_one.
                    do 2 rewrite h3_scalar.
                    rewrite scalar_neg_one.
                    do 2 rewrite h3_free_from.
                    unfold h1; cbn.
                    rewrite g_lscalar.
                    rewrite plus_rinv.
                    rewrite scalar_ranni.
                    reflexivity.
                +   destruct a_in as [α [u [v eq]]].
                    rewrite eq; clear eq.
                    rewrite h3_plus.
                    rewrite <- scalar_neg_one.
                    do 2 rewrite h3_scalar.
                    rewrite scalar_neg_one.
                    do 2 rewrite h3_free_from.
                    unfold h1; cbn.
                    rewrite g_rscalar.
                    rewrite plus_rinv.
                    rewrite scalar_ranni.
                    reflexivity.
        }
        pose (h := unary_op wd).
        cbn in *.
        change (equiv_type (subspace_equiv (linear_span_subspace U
            (tensor_product_ideal U V1 V2)))) with (tensor_space U V1 V2) in h.
        assert (∀ u v, h (u + v) = h u + h v) as h_plus.
        {
            intros u v.
            equiv_get_value u v.
            unfold h.
            unfold plus at 1; cbn.
            equiv_simpl.
            apply h3_plus.
        }
        assert (∀ a v, h (a · v) = a · h v) as h_scalar.
        {
            intros a v.
            equiv_get_value v.
            unfold h.
            unfold scalar_mult at 1; cbn.
            equiv_simpl.
            apply h3_scalar.
        }
        exists (make_module_homomorphism _ tensor_product_base _ h h_plus h_scalar).
        unfold bilinear_from_set; cbn.
        intros x y.
        unfold h, f.
        unfold tensor_mult_base, to_quotient.
        equiv_simpl.
        unfold h4.
        rewrite h3_free_from.
        unfold h1.
        cbn.
        reflexivity.
    -   intros [h1 h1_from] [h2 h2_from].
        unfold bilinear_from_set in h1_from, h2_from; cbn in *.
        pose (h1_plus := @module_homo_plus _ _ _ h1).
        pose (h2_plus := @module_homo_plus _ _ _ h2).
        pose (h1_scalar := @module_homo_scalar _ _ _ h1).
        pose (h2_scalar := @module_homo_scalar _ _ _ h2).
        apply set_type_eq; cbn.
        apply module_homomorphism_eq.
        intros x.
        cbn in x.
        pose proof (tensor_sum U V1 V2 x) as [l x_eq].
        rewrite x_eq; clear x_eq.
        induction l.
        +   cbn.
            rewrite <- (scalar_lanni 0).
            rewrite h1_scalar, h2_scalar.
            do 2 rewrite scalar_lanni.
            reflexivity.
        +   cbn.
            rewrite h1_plus, h2_plus.
            rewrite IHl; clear IHl.
            apply rplus.
            destruct a as [a [u [v a_eq]]]; cbn.
            subst a.
            rewrite h1_from, h2_from.
            reflexivity.
Qed.

Definition tensor_bilinear_from := ex_val tensor_product_ex.
Definition tensor_product := bilinear_from_module tensor_bilinear_from.
Definition tensor_mult := bilinear_from_f tensor_bilinear_from.
Definition tensor_bilinear := bilinear_from_bi tensor_bilinear_from.

Theorem tensor_product_universal : initial tensor_bilinear_from.
    exact (ex_proof tensor_product_ex).
Qed.

Infix "⊗" := tensor_mult : algebra_scope.

Let tensor_plus := module_plus tensor_product.
Let tensor_zero := module_zero tensor_product.
Let tensor_neg := module_neg tensor_product.
Let tensor_plus_comm := module_plus_comm tensor_product.
Let tensor_plus_assoc := module_plus_assoc tensor_product.
Let tensor_plus_lid := module_plus_lid tensor_product.
Let tensor_plus_linv := module_plus_linv tensor_product.
Let tensor_scalar := module_scalar tensor_product.
Let tensor_scalar_comp := module_scalar_comp tensor_product.
Let tensor_scalar_id := module_scalar_id tensor_product.
Let tensor_scalar_rdist := module_scalar_rdist tensor_product.
Existing Instances tensor_plus tensor_zero tensor_neg tensor_plus_comm
    tensor_plus_assoc tensor_plus_lid tensor_plus_linv tensor_scalar
    tensor_scalar_comp tensor_scalar_id tensor_scalar_rdist.

Theorem tensor_ldist : ∀ a b c, a ⊗ (b + c) = a ⊗ b + a ⊗ c.
    apply tensor_bilinear.
Qed.

Theorem tensor_rdist : ∀ a b c, (a + b) ⊗ c = a ⊗ c + b ⊗ c.
    apply tensor_bilinear.
Qed.

Theorem tensor_lscalar : ∀ a u v, (a · u) ⊗ v = a · (u ⊗ v).
    apply tensor_bilinear.
Qed.

Theorem tensor_rscalar : ∀ a u v, u ⊗ (a · v) = a · (u ⊗ v).
    apply tensor_bilinear.
Qed.

Theorem tensor_mult_lneg : ∀ u v, (-u) ⊗ v = -(u ⊗ v).
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite tensor_lscalar.
    apply scalar_neg_one.
Qed.
Theorem tensor_mult_rneg : ∀ u v, u ⊗ (-v) = -(u ⊗ v).
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite tensor_rscalar.
    apply scalar_neg_one.
Qed.

End TensorProductCategory.
