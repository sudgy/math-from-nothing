Require Import init.

Require Import linear_free.
Require Import linear_subspace.
Require Import linear_span.
Require Import linear_bilinear.
Require Import tensor_product_construction.

Require Import set.
Require Import card.

Require Import unordered_list.
Require Import plus_sum.

Require Import module_category.
Require Import category_initterm.

Section TensorProductCategory.

Context {F : CRing} (M N : Module F).

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

Definition tensor_product_base := make_module
    F
    (tensor_space M N)
    (tensor_plus M N)
    (tensor_zero M N)
    (tensor_neg M N)
    (tensor_plus_assoc M N)
    (tensor_plus_comm M N)
    (tensor_plus_lid M N)
    (tensor_plus_linv M N)
    (tensor_scalar_mult M N)
    (tensor_scalar_id M N)
    (tensor_scalar_ldist M N)
    (tensor_scalar_rdist M N)
    (tensor_scalar_comp M N).

Record bilinear_from := make_bilinear {
    bilinear_from_module : Module F;
    bilinear_from_f : V1 → V2 → module_V bilinear_from_module;
    bilinear_from_bi : bilinear
        (H1 := module_plus bilinear_from_module)
        (H4 := module_scalar bilinear_from_module)
        bilinear_from_f;
}.

Definition bilinear_from_set (f g : bilinear_from)
    (h : cat_morphism (MODULE F)
                      (bilinear_from_module f)
                      (bilinear_from_module g))
    := ∀ x y, module_homo_f h (bilinear_from_f f x y) = bilinear_from_f g x y.

Definition bilinear_from_compose {F G H : bilinear_from}
    (f : set_type (bilinear_from_set G H)) (g : set_type (bilinear_from_set F G))
    := [f|] ∘ [g|].

Lemma bilinear_from_set_compose_in
        {F' G H : bilinear_from} : ∀ (f : set_type (bilinear_from_set G H)) g,
        bilinear_from_set F' H (bilinear_from_compose f g).
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
    apply (@cat_assoc (MODULE F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_lid (MODULE F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_rid (MODULE F)).
Qed.

Let FR_plus := free_plus_class F (V1 * V2).
Let FR_zero := free_zero F (V1 * V2).
Let FR_neg := free_neg F (V1 * V2).
Let FR_plus_comm := free_plus_comm_class F (V1 * V2).
Let FR_plus_assoc := free_plus_assoc_class F (V1 * V2).
Let FR_plus_lid := free_plus_lid_class F (V1 * V2).
Let FR_plus_linv := free_plus_linv_class F (V1 * V2).
Let FR_scalar := free_scalar F (V1 * V2).
Let FR_scalar_id := free_scalar_id_class F (V1 * V2).
Let FR_scalar_ldist := free_scalar_ldist_class F (V1 * V2).
Let FR_scalar_rdist := free_scalar_rdist_class F (V1 * V2).
Let FR_scalar_comp := free_scalar_comp_class F (V1 * V2).
Let V3P := module_plus tensor_product_base.
Let SM3 := module_scalar tensor_product_base.
Existing Instances FR_plus FR_zero FR_neg FR_plus_comm FR_plus_assoc FR_plus_lid
    FR_plus_linv FR_scalar FR_scalar_id FR_scalar_ldist FR_scalar_rdist
    FR_scalar_comp V3P SM3.

Let f x y := tensor_mult_base M N x y.

Lemma tensor_product_bilinear_base : bilinear f.
    repeat split.
    -   apply tensor_lscalar_base.
    -   apply tensor_rscalar_base.
    -   apply tensor_rdist_base.
    -   apply tensor_ldist_base.
Qed.

Let f_bilinear_from :=
    make_bilinear tensor_product_base f tensor_product_bilinear_base.

Lemma tensor_product_ex_base : @initial BILINEAR_FROM f_bilinear_from.
    unfold f_bilinear_from, initial; cbn.
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
        pose (h2 := make_free_from F (V1 * V2) (bilinear_from_module g) h1).
        pose proof (free_module_universal F (V1 * V2) h2) as uni.
        cbn in uni.
        apply card_one_ex in uni as [h3 h3_free_from].
        unfold free_from_set in h3_free_from.
        cbn in h3_free_from.
        pose (h4 := module_homo_f h3).
        cbn in h4.
        pose (h3_plus := @module_homo_plus _ _ _ h3).
        pose (h3_scalar := @module_homo_scalar _ _ _ h3).
        assert (∀ x y, eq_equal (subspace_equiv (linear_span_subspace U
            (tensor_product_ideal M N))) x y → h4 x = h4 y) as wd.
        {
            intros x y eq.
            cbn in eq.
            unfold h4.
            apply plus_0_anb_a_b.
            rewrite <- scalar_neg_one.
            rewrite <- h3_scalar.
            rewrite scalar_neg_one.
            rewrite <- h3_plus.
            rewrite (span_linear_combination _ (tensor_product_ideal M N)) in eq.
            destruct eq as [l [l_eq l_in]].
            cbn in *.
            unfold FR_plus in l_eq.
            unfold U, V1, V2 in l_eq.
            unfold U, V1, V2.
            rewrite l_eq; clear l_eq.
            destruct l as [l l_comb]; cbn in *.
            unfold linear_combination; cbn.
            unfold linear_list_in in l_in; cbn in l_in; clear l_comb.
            induction l using ulist_induction.
            -   rewrite ulist_image_end, ulist_sum_end.
                rewrite <- (scalar_lanni (V := free_linear U (V1 * V2)) 0).
                rewrite h3_scalar.
                rewrite scalar_lanni.
                reflexivity.
            -   prove_parts IHl.
                1: {
                    apply ulist_prop_split.
                    intros [α v] l' l_eq; cbn.
                    subst l.
                    rewrite ulist_swap in l_in.
                    rewrite ulist_prop_add in l_in.
                    apply l_in.
                }
                rewrite ulist_image_add, ulist_sum_add.
                rewrite h3_plus.
                unfold U, V1, V2.
                rewrite <- IHl; clear IHl.
                rewrite plus_rid.
                rewrite h3_scalar.
                assert (tensor_product_ideal M N (snd a)) as a_in.
                {
                    rewrite ulist_prop_add in l_in.
                    apply l_in.
                }
                pose proof (bilinear_from_bi g) as
                    [g_lscalar [g_rscalar [g_rdist g_ldist]]].
                destruct a_in as [[[a_in|a_in]|a_in]|a_in].
                +   destruct a_in as [u [v [w eq]]].
                    unfold U, V1, V2 in eq.
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
                    unfold U, V1, V2 in eq.
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
                    unfold U, V1, V2 in eq.
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
                    unfold U, V1, V2 in eq.
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
            (tensor_product_ideal M N)))) with (tensor_space M N) in h.
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
        pose proof (tensor_sum_base M N x) as [l x_eq].
        rewrite x_eq; clear x_eq.
        induction l using ulist_induction.
        +   rewrite ulist_image_end, ulist_sum_end.
            rewrite <- (scalar_lanni 0).
            rewrite h1_scalar, h2_scalar.
            do 2 rewrite scalar_lanni.
            reflexivity.
        +   rewrite ulist_image_add, ulist_sum_add.
            rewrite h1_plus, h2_plus.
            rewrite IHl; clear IHl.
            apply rplus.
            destruct a as [a [u [v a_eq]]]; cbn.
            subst a.
            rewrite h1_from, h2_from.
            reflexivity.
Qed.

Theorem tensor_product_ex : ∃ T, @initial BILINEAR_FROM T.
    exists f_bilinear_from.
    exact tensor_product_ex_base.
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

Definition simple_tensor T := ∃ a b, T = a ⊗ b.

Theorem tensor_sum : ∀ T, ∃ l : ulist (set_type simple_tensor),
        T = ulist_sum (ulist_image l (λ x, [x|])).
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
    intros T.
    pose proof (initial_unique  _ _
        tensor_product_universal tensor_product_ex_base) as [g [h [gh hg]]].
    destruct g as [g g_in], h as [h h_in].
    cbn in *.
    apply eq_set_type in gh; cbn in gh.
    apply eq_set_type in hg; cbn in hg.
    unfold module_homo_compose, module_homo_id in gh, hg.
    inversion gh as [gh']; clear gh.
    inversion hg as [hg']; clear hg.
    pose proof (func_eq _ _ gh') as gh; cbn in gh.
    pose proof (func_eq _ _ hg') as hg; cbn in hg.
    clear gh' hg'.
    pose proof (tensor_sum_base M N (module_homo_f g T)) as [l l_eq].
    pose (f' (t : set_type (simple_tensor_base M N))
        := module_homo_f h [t|]).
    assert (∀ t, simple_tensor (f' t)) as f'_in.
    {
        intros [t [u [v t_eq]]].
        subst t.
        unfold f'; cbn.
        exists u, v.
        unfold bilinear_from_set in *; cbn in *.
        unfold f in h_in.
        rewrite h_in.
        reflexivity.
    }
    exists (ulist_image l (λ t, [_|f'_in t])).
    unfold f'; cbn.
    rewrite ulist_image_comp; cbn.
    clear f' f'_in.
    revert T l_eq.
    induction l using ulist_induction; intros.
    -   rewrite ulist_image_end, ulist_sum_end.
        rewrite ulist_image_end, ulist_sum_end in l_eq.
        apply (f_equal (module_homo_f h)) in l_eq.
        rewrite hg in l_eq.
        rewrite l_eq.
        rewrite <- (scalar_ranni 0).
        rewrite (@module_homo_scalar _ _ _ h).
        apply scalar_lanni.
    -   rewrite ulist_image_add, ulist_sum_add.
        rewrite ulist_image_add, ulist_sum_add in l_eq.
        apply plus_rlmove in l_eq.
        rewrite <- (gh (-[a|])) in l_eq.
        rewrite <- (@module_homo_plus _ _ _ g) in l_eq.
        specialize (IHl _ l_eq).
        rewrite <- IHl.
        clear IHl l_eq.
        rewrite <- scalar_neg_one.
        rewrite (@module_homo_scalar _ _ _ h).
        rewrite scalar_neg_one.
        rewrite plus_lrinv.
        reflexivity.
Qed.

Theorem tensor_product_lanni : ∀ v, 0 ⊗ v = 0.
    intros v.
    apply (plus_rcancel (0 ⊗ v)).
    rewrite <- tensor_rdist.
    do 2 rewrite plus_lid.
    reflexivity.
Qed.
Theorem tensor_product_ranni : ∀ v, v ⊗ 0 = 0.
    intros v.
    apply (plus_rcancel (v ⊗ 0)).
    rewrite <- tensor_ldist.
    do 2 rewrite plus_lid.
    reflexivity.
Qed.
Theorem tensor_product_zero : 0 ⊗ 0 = 0.
    apply tensor_product_lanni.
Qed.

End TensorProductCategory.
