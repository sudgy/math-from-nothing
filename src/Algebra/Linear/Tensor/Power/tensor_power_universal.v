Require Import init.

Require Export tensor_power_base.
Require Import tensor_product_universal.
Require Import linear_bilinear.
Require Import module_category.
Require Import category_initterm.

Require Import list.
Require Import unordered_list.
Require Import set.
Require Import nat.

(* begin hide *)
Section TensorPowerCategory.

(* end hide *)
Context {F : CRingObj} (V : ModuleObj F).
Variable n : nat.

(* begin hide *)
Let VP := module_plus V.
Let VSM := module_scalar V.
Let VnP := module_plus (tensor_power V n).
Let VnSM := module_scalar (tensor_power V n).

Existing Instances VP VSM VnP VnSM.

(* end hide *)
Record multilinear_from := make_multilinear {
    multilinear_from_module : Module F;
    multilinear_from_f : ∀ l : list (module_V V), list_size l = n →
        module_V multilinear_from_module;
    multilinear_from_plus : ∀ l1 a b l2 eq1 eq2 eq3,
        multilinear_from_f (l1 + (a + b) ꞉ l2) eq1 =
        @plus _ (module_plus multilinear_from_module)
            (multilinear_from_f (l1 + a ꞉ l2) eq2)
            (multilinear_from_f (l1 + b ꞉ l2) eq3);
    multilinear_from_scalar : ∀ l1 a v l2 eq1 eq2,
        multilinear_from_f (l1 + (a · v) ꞉ l2) eq1 =
        @scalar_mult _ _ (module_scalar multilinear_from_module)
            a (multilinear_from_f (l1 + v ꞉ l2) eq2)
}.

Definition multilinear_from_set (f g : multilinear_from)
    (h : cat_morphism (multilinear_from_module f)
                      (multilinear_from_module g))
    := ∀ x (eq : list_size x = n),
        h (multilinear_from_f f x eq) = multilinear_from_f g x eq.

Definition multilinear_from_compose {F G H : multilinear_from}
    (f : set_type (multilinear_from_set G H))
    (g : set_type (multilinear_from_set F G))
    := [f|] ∘ [g|].

Lemma multilinear_from_set_compose_in {F' G H : multilinear_from} :
    ∀ (f : set_type (multilinear_from_set G H)) g,
    multilinear_from_set F' H (multilinear_from_compose f g).
Proof.
    intros [f f_eq] [g g_eq].
    unfold multilinear_from_set in *.
    unfold multilinear_from_compose; cbn.
    intros x eq.
    rewrite g_eq.
    apply f_eq.
Qed.

Lemma multilinear_from_set_id_in : ∀ f : multilinear_from,
    multilinear_from_set f f 𝟙.
Proof.
    intros f.
    unfold multilinear_from_set.
    intros x eq.
    cbn.
    reflexivity.
Qed.

Program Instance MULTILINEAR_FROM : Category := {
    cat_U := multilinear_from;
    cat_morphism f g := set_type (multilinear_from_set f g);
    cat_compose {F G H} f g := [_|multilinear_from_set_compose_in f g];
    cat_id f := [_|multilinear_from_set_id_in f];
}.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_assoc (Module F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_lid (Module F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_rid (Module F)).
Qed.

Definition vectors_to_power_eq {m} (l : list (module_V V)) (eq : list_size l = m)
    := tensor_power_nat_eq V eq (vectors_to_power V l).

Lemma vectors_to_power_eq_generic {m} :
    ∀ (l : list (module_V V)) (eq : list_size l = m),
    to_generic_tensor V (vectors_to_power_eq l eq) =
    to_generic_tensor V (vectors_to_power V l).
Proof.
    intros l eq.
    unfold vectors_to_power_eq.
    rewrite generic_tensor_eq_generic.
    reflexivity.
Qed.

Lemma vectors_to_power_add :
    ∀ a l (eq1 : list_size (a ꞉ l) = nat_suc n) eq2,
    vectors_to_power_eq (a ꞉ l) eq1 =
    tensor_mult V (tensor_power V _) a (vectors_to_power_eq l eq2).
Proof.
    intros a l eq1 eq2.
    apply tensor_power_eq.
    rewrite vectors_to_power_eq_generic.
    destruct eq2; cbn.
    reflexivity.
Qed.

Lemma tensor_multilinear_from_plus : ∀ l1 a b l2 eq1 eq2 eq3,
    vectors_to_power_eq (l1 + (a + b) ꞉ l2) eq1 =
    vectors_to_power_eq (l1 + a ꞉ l2) eq2 +
    vectors_to_power_eq (l1 + b ꞉ l2) eq3.
Proof.
    intros l1 a b l2 eq1 eq2 eq3.
    apply tensor_power_eq.
    rewrite vectors_to_power_eq_generic.
    clear eq1.
    unfold vectors_to_power_eq.
    destruct eq3.
    induction l1.
    -   cbn in *.
        rewrite list_conc_lid.
        unfold list_conc; cbn.
        rewrite (tensor_rdist V).
        apply (@to_generic_tensor_plus F V).
        +   reflexivity.
        +   rewrite (generic_tensor_eq_generic V _ _ eq2).
            reflexivity.
    -   cbn in *.
        inversion eq2 as [eq3].
        specialize (IHl1 eq3).
        rewrite (generic_tensor_mult_eq V (Logic.eq_refl a0) IHl1).
        rewrite tensor_ldist.
        apply (@to_generic_tensor_plus F V).
        +   reflexivity.
        +   rewrite (generic_tensor_eq_generic V _ _ eq2).
            apply generic_tensor_mult_eq; [>reflexivity|].
            rewrite generic_tensor_eq_generic.
            reflexivity.
Qed.

Lemma tensor_multilinear_from_scalar : ∀ l1 a v l2 eq1 eq2,
    vectors_to_power_eq (l1 + (a · v) ꞉ l2) eq1 =
    a · vectors_to_power_eq (l1 + v ꞉ l2) eq2.
Proof.
    intros l1 a v l2 eq1 eq2.
    apply tensor_power_eq.
    rewrite vectors_to_power_eq_generic.
    unfold vectors_to_power_eq.
    destruct eq2; cbn.
    clear eq1.
    induction l1.
    -   unfold plus; cbn.
        unfold list_conc; cbn.
        rewrite (tensor_lscalar V).
        reflexivity.
    -   cbn in *.
        rewrite list_conc_add.
        cbn.
        unfold plus at 6; cbn.
        unfold list_conc; fold (list_conc (U := module_V V)).
        cbn.
        rewrite <- (tensor_rscalar V
            (tensor_power V (list_size (list_conc l1 (v ꞉ l2))))).
        apply generic_tensor_mult_eq; [>reflexivity|].
        exact IHl1.
Qed.

Definition tensor_multilinear_from := make_multilinear
    (tensor_power V n)
    vectors_to_power_eq
    tensor_multilinear_from_plus
    tensor_multilinear_from_scalar.

(* begin hide *)
End TensorPowerCategory.

Section TensorPowerCategory.

Context {F : CRingObj} (V : ModuleObj F).
Variable n : nat.

Let UM := cring_mult F.
Let UMC := cring_mult_comm F.

Existing Instances UM UMC.

(* end hide *)
Theorem tensor_power_universal :
    @initial (MULTILINEAR_FROM V n) (tensor_multilinear_from V n).
Proof.
    unfold tensor_multilinear_from, initial; cbn.
    intros g.
    unfold multilinear_from_set; cbn.
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        nat_induction n.
        +   destruct g as [M g g_plus g_scalar]; cbn.
            pose (USM := module_scalar (cring_module F)).
            pose (UP := cring_plus F).
            pose (MP := module_plus M).
            pose (MSM := module_scalar M).
            pose (MSMO := module_scalar_id M).
            pose (MSMR := module_scalar_rdist M).
            pose (MSMC := module_scalar_comp M).
            unfold zero at 2; cbn.
            pose (x := g list_end (Logic.eq_refl 0)).
            pose (f α := α · x).
            assert (∀ u v, f (u + v) = f u + f v) as f_plus.
            {
                intros u v.
                unfold f.
                apply scalar_rdist.
            }
            assert (∀ a v, f (a · v) = a · f v) as f_scalar.
            {
                intros a v.
                unfold f.
                symmetry; apply scalar_comp.
            }
            exists (make_module_homomorphism F (cring_module F) M
                f f_plus f_scalar); cbn.
            intros l l_eq.
            destruct l; [>|inversion l_eq].
            rewrite (proof_irrelevance _ (Logic.eq_refl 0)); clear l_eq.
            fold x.
            unfold vectors_to_power_eq.
            unfold f.
            unfold vectors_to_power.
            destruct (@Logic.eq_refl nat nat_zero); cbn.
            apply scalar_id.
        +   cbn.
            clear n.
            rename n0 into n.
            pose (VP := module_plus V).
            pose (VSM := module_scalar V).
            pose (VnP := module_plus (tensor_power V n)).
            pose (VnSM := module_scalar (tensor_power V n)).
            pose (gM := multilinear_from_module V (nat_suc n) g).
            pose (gMP := module_plus gM).
            pose (gMN := module_neg gM).
            pose (gMPC := module_plus_comm gM).
            pose (gMPA := module_plus_assoc gM).
            pose (gMPZ := module_plus_lid gM).
            pose (gMPN := module_plus_linv gM).
            pose (gMSM := module_scalar gM).
            pose (gMSML := module_scalar_ldist gM).
            pose (gMSMC := module_scalar_comp gM).
            assert (∀ (a : module_V V) l,
                list_size l = n → list_size (a ꞉ l) = nat_suc n) as l_eq.
            {
                intros a l eq.
                rewrite list_size_add.
                apply f_equal.
                exact eq.
            }
            pose (f1 v l eq := multilinear_from_f V (nat_suc n) g (v ꞉ l) (l_eq _ _ eq)).
            assert (∀ v, ∀ l1 a b l2 eq1 eq2 eq3,
                f1 v (l1 + (a + b) ꞉ l2) eq1 =
                f1 v (l1 + a ꞉ l2) eq2 + f1 v (l1 + b ꞉ l2) eq3)
                as f1_plus.
            {
                intros v l1 a b l2 eq1 eq2 eq3.
                unfold f1.
                change (v ꞉ (l1 + (a + b) ꞉ l2)) with ((v ꞉ l1) + (a + b) ꞉ l2).
                change (v ꞉ (l1 + a ꞉ l2)) with ((v ꞉ l1) + a ꞉ l2).
                change (v ꞉ (l1 + b ꞉ l2)) with ((v ꞉ l1) + b ꞉ l2).
                apply multilinear_from_plus.
            }
            assert (∀ v, ∀ l1 a u l2 eq1 eq2,
                f1 v (l1 + (a · u) ꞉ l2) eq1 =
                a · f1 v (l1 + u ꞉ l2) eq2) as f1_scalar.
            {
                intros v l1 a u l2 eq1 eq2.
                unfold f1.
                change (v ꞉ (l1 + a · u ꞉ l2)) with ((v ꞉ l1) + a · u ꞉ l2).
                change (v ꞉ (l1 + u ꞉ l2)) with ((v ꞉ l1) + u ꞉ l2).
                apply multilinear_from_scalar.
            }
            pose (f2 v := make_multilinear V n
                (multilinear_from_module V (nat_suc n) g)
                (f1 v) (f1_plus v) (f1_scalar v)).
            pose (f3 v := ex_val (IHn0 (f2 v))).
            cbn in f3.
            assert (bilinear f3) as f_bil.
            {
                repeat split.
                -   intros a v1 v2.
                    unfold f3.
                    unfold ex_val.
                    destruct (ex_to_type _) as [ah ah_eq]; cbn.
                    destruct (ex_to_type _) as [h h_eq]; cbn.
                    pose proof (tensor_power_sum V v2) as [l v2_eq]; subst v2.
                    induction l as [|v l] using ulist_induction.
                    +   rewrite ulist_image_end, ulist_sum_end.
                        do 2 rewrite module_homo_zero.
                        rewrite scalar_ranni.
                        reflexivity.
                    +   rewrite ulist_image_add, ulist_sum_add.
                        do 2 rewrite module_homo_plus.
                        rewrite scalar_ldist.
                        rewrite IHl; clear IHl.
                        apply rplus; clear l.
                        destruct v as [v [α [l v_eq]]]; subst v; cbn.
                        destruct l as [l ln]; cbn.
                        do 2 rewrite module_homo_scalar.
                        unfold vectors_to_power_eq in ah_eq, h_eq.
                        rewrite ah_eq, h_eq.
                        rewrite scalar_comp.
                        rewrite mult_comm.
                        rewrite <- scalar_comp.
                        apply f_equal.
                        unfold f1.
                        apply (multilinear_from_scalar _ _ g list_end).
                -   intros a v1 v2.
                    unfold f3.
                    apply module_homo_scalar.
                -   intros v1 v2 v3.
                    unfold f3.
                    unfold ex_val.
                    destruct (ex_to_type _) as [h12 h12_eq]; cbn.
                    destruct (ex_to_type _) as [h1 h1_eq]; cbn.
                    destruct (ex_to_type _) as [h2 h2_eq]; cbn.
                    pose proof (tensor_power_sum V v3) as [l v3_eq]; subst v3.
                    induction l as [|v l] using ulist_induction.
                    +   rewrite ulist_image_end, ulist_sum_end.
                        do 3 rewrite module_homo_zero.
                        rewrite plus_lid.
                        reflexivity.
                    +   rewrite ulist_image_add, ulist_sum_add.
                        do 3 rewrite module_homo_plus.
                        rewrite IHl; clear IHl.
                        do 2 rewrite plus_assoc.
                        apply rplus.
                        rewrite <- plus_assoc.
                        rewrite (plus_comm _ (h2 [v|])).
                        rewrite plus_assoc.
                        apply rplus; clear l.
                        destruct v as [v [α  [l v_eq]]]; subst v; cbn.
                        destruct l as [l ln]; cbn.
                        do 3 rewrite module_homo_scalar.
                        unfold vectors_to_power_eq in h12_eq, h1_eq, h2_eq.
                        rewrite h12_eq, h1_eq, h2_eq.
                        rewrite <- scalar_ldist.
                        apply f_equal.
                        unfold f1.
                        apply (multilinear_from_plus _ _ g list_end).
                -   intros v1 v2 v3.
                    unfold f3.
                    apply module_homo_plus.
            }
            pose (f_base := make_bilinear V (tensor_power V n) _ f3 f_bil).
            pose proof (tensor_product_universal _ _ f_base) as f_ex.
            apply ex_singleton in f_ex as [f f_in].
            cbn in f, f_in.
            exists f.
            unfold bilinear_from_set in f_in; cbn in f_in.
            change (bilinear_from_f V _ (tensor_bilinear_from V _)) with
                (tensor_mult V (tensor_power V n)) in f_in.
            intros l eq.
            destruct l; [>inversion eq|].
            cbn.
            inversion eq as [eq2].
            rewrite (vectors_to_power_add _ _ _ _ _ eq2).
            rewrite f_in.
            unfold f3.
            unfold ex_val.
            destruct (ex_to_type _) as [h h_eq]; cbn.
            rewrite h_eq.
            unfold f1.
            rewrite (proof_irrelevance _ eq).
            reflexivity.
    -   intros [f1 f1_eq] [f2 f2_eq].
        apply set_type_eq; cbn.
        apply module_homomorphism_eq.
        intros v.
        pose proof (tensor_power_sum V v) as [l v_eq]; subst v.
        induction l as [|v l] using ulist_induction.
        +   rewrite ulist_image_end, ulist_sum_end.
            do 2 rewrite module_homo_zero.
            reflexivity.
        +   rewrite ulist_image_add, ulist_sum_add.
            do 2 rewrite module_homo_plus.
            rewrite IHl; clear IHl.
            apply rplus; clear l.
            destruct v as [v [α [l v_eq]]]; subst v; cbn.
            do 2 rewrite module_homo_scalar.
            apply f_equal.
            unfold vectors_to_power_eq in f1_eq, f2_eq.
            rewrite f1_eq, f2_eq.
            reflexivity.
Qed.
(* begin hide *)

End TensorPowerCategory.
(* end hide *)
