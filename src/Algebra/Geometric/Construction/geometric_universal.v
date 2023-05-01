Require Import init.

Require Export algebra_category.
Require Import geometric_construct.
Require Export linear_bilinear_form.
Require Import linear_free.
Require Import linear_grade.

Require Import ring_ideal.

Require Import category_initterm.
Require Export unordered_list.
Require Export set.
Require Import equivalence.

Section GeometricCategory.

Context {U : CRingObj} {V : ModuleObj U}.
Context (B : set_type (bilinear_form (V := V))).

Record to_geo := make_to_geo {
    to_geo_algebra : Algebra U;
    to_geo_homo : ModuleObjHomomorphism V (algebra_module to_geo_algebra);
    to_geo_contract : ∀ v,
        @mult _ (algebra_mult to_geo_algebra) (to_geo_homo v) (to_geo_homo v) =
        @scalar_mult _ _ (algebra_scalar to_geo_algebra)
            ([B|] v v) (@one _ (algebra_one to_geo_algebra))
}.

Definition to_geo_set (f g : to_geo)
    (h : cat_morphism (to_geo_algebra f)
                      (to_geo_algebra g))
    := ∀ x, h ((to_geo_homo f) x) = (to_geo_homo g) x.

Definition to_geo_compose {F G H : to_geo}
    (f : set_type (to_geo_set G H)) (g : set_type (to_geo_set F G))
    := [f|] ∘ [g|].

Lemma to_geo_set_compose_in {F' G H : to_geo} :
    ∀ (f : set_type (to_geo_set G H)) g,
    to_geo_set F' H (to_geo_compose f g).
Proof.
    intros [f f_eq] [g g_eq].
    unfold to_geo_set in *.
    unfold to_geo_compose; cbn.
    intros x.
    rewrite g_eq.
    apply f_eq.
Qed.

Lemma to_geo_set_id_in : ∀ f : to_geo, to_geo_set f f 𝟙.
Proof.
    intros f.
    unfold to_geo_set.
    intros x.
    cbn.
    reflexivity.
Qed.

Program Instance TO_GEO : Category := {
    cat_U := to_geo;
    cat_morphism f g := set_type (to_geo_set f g);
    cat_compose {F G H} f g := [_|to_geo_set_compose_in f g];
    cat_id f := [_|to_geo_set_id_in f];
}.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_assoc (Algebra U)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_lid (Algebra U)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_rid (Algebra U)).
Qed.

Definition vector_to_geo_homo := make_module_homomorphism
    U
    V
    (algebra_module (geometric_algebra_object B))
    (vector_to_geo B)
    (vector_to_geo_plus B)
    (vector_to_geo_scalar B).

Definition geo_to_geo := make_to_geo
    (geometric_algebra_object B)
    vector_to_geo_homo
    (geo_contract B).

Theorem geometric_algebra_ex : ∃ G, @initial TO_GEO G.
Proof.
    pose (FRM := FR_mult (V := V)).
    pose (FRA := FR_mult_assoc (V := V)).
    pose (FRL := FR_ldist (V := V)).
    pose (FRR := FR_rdist (V := V)).
    pose (FRLS := FR_lscalar (V := V)).
    pose (FRRS := FR_rscalar (V := V)).
    pose (FRO := FR_one (V := V)).
    pose (FRLO := FR_mult_lid (V := V)).
    pose (FRRO := FR_mult_rid (V := V)).
    pose (FRG := free_grade U (list V)).
    exists geo_to_geo.
    unfold geo_to_geo, initial; cbn.
    intros [A g g_contr].
    unfold to_geo_set; cbn.
    assert (∀ α v, to_qring (ga_ideal B) (α · v) =
        α · (to_qring (ga_ideal B) v : geometric_algebra_object B))
        as to_qring_scalar.
    {
        intros α v.
        unfold scalar_mult at 2; cbn.
        unfold to_qring; equiv_simpl.
        apply (ideal_eq_reflexive (ga_ideal B)).
    }
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        pose (h1 := free_extend U (list (module_V V))
            (λ l, list_prod (list_image g l))).
        assert (∀ v, h1 (to_free U (list (module_V V)) [v]) = g v)
            as h1_vec.
        {
            intros v.
            unfold h1.
            rewrite (free_extend_free _ _).
            rewrite list_image_single.
            cbn.
            apply mult_rid.
        }
        assert (HomomorphismMult h1) as h1_mult.
        {
            split.
            intros a b.
            induction a as [|a u] using grade_induction.
            {
                rewrite mult_lanni.
                rewrite module_homo_zero.
                rewrite mult_lanni.
                reflexivity.
            }
            rewrite rdist.
            do 2 rewrite module_homo_plus.
            rewrite rdist.
            rewrite IHu.
            apply rplus.
            clear u IHu.
            induction b as [|b v] using grade_induction.
            {
                rewrite mult_ranni.
                rewrite module_homo_zero.
                rewrite mult_ranni.
                reflexivity.
            }
            rewrite ldist.
            do 2 rewrite module_homo_plus.
            rewrite ldist.
            rewrite IHv.
            apply rplus.
            clear v IHv.
            destruct a as [a a_homo], b as [b b_homo]; cbn.
            destruct a_homo as [u au], b_homo as [v bv].
            apply to_free_ex in au as [α a_eq]; subst a.
            apply to_free_ex in bv as [β b_eq]; subst b.
            rewrite scalar_lmult, scalar_rmult.
            do 4 rewrite module_homo_scalar.
            rewrite scalar_lmult, scalar_rmult.
            do 2 apply f_equal.
            unfold mult at 1; cbn.
            change (sum_module_type _ _)
                with (module_V (free_linear U (list V))).
            rewrite (free_bilinear_free _ _).
            unfold h1.
            do 3 rewrite (free_extend_free _ _).
            rewrite list_image_conc.
            apply list_prod_conc.
        }
        assert (∀ x y, eq_equal (ideal_equiv (ga_ideal B)) x y →
            h1 x = h1 y) as wd.
        {
            intros x y eq.
            cbn in eq.
            rewrite <- plus_0_anb_a_b.
            rewrite <- module_homo_neg.
            rewrite <- module_homo_plus.
            remember (x - y) as v.
            rewrite <- Heqv in eq.
            clear x y Heqv.
            destruct eq as [l v_eq]; subst v.
            induction l as [|a l] using ulist_induction.
            {
                rewrite ulist_image_end, ulist_sum_end.
                rewrite module_homo_zero.
                reflexivity.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite module_homo_plus.
            rewrite <- IHl; clear l IHl.
            rewrite plus_rid.
            destruct a as [[a b] v]; cbn.
            do 2 setoid_rewrite homo_mult.
            assert (h1 [v|] = 0) as eq.
            {
                clear a b.
                destruct v as [v [v_in|[v_in|v_in]]]; cbn.
                -   destruct v_in as [a [b v_eq]]; subst v.
                    do 2 rewrite module_homo_plus.
                    do 2 rewrite module_homo_neg.
                    do 3 rewrite h1_vec.
                    rewrite <- plus_assoc.
                    rewrite module_homo_plus.
                    rewrite <- neg_plus.
                    apply plus_rinv.
                -   destruct v_in as [α [u v_eq]]; subst v.
                    rewrite module_homo_plus.
                    rewrite module_homo_neg.
                    rewrite module_homo_scalar.
                    do 2 rewrite h1_vec.
                    rewrite module_homo_scalar.
                    apply plus_rinv.
                -   destruct v_in as [u v_eq]; subst v.
                    rewrite module_homo_plus, module_homo_neg.
                    rewrite module_homo_scalar.
                    unfold h1.
                    do 2 rewrite (free_extend_free _ _).
                    rewrite list_image_end, list_prod_end.
                    rewrite list_image_add, list_image_single.
                    rewrite list_prod_add, list_prod_single.
                    rewrite g_contr.
                    apply plus_rinv.
            }
            rewrite eq.
            rewrite mult_ranni, mult_lanni.
            reflexivity.
        }
        pose (h := unary_op wd : geometric_algebra_object B → A).
        assert (∀ u v, h (u + v) = h u + h v) as h_plus.
        {
            intros u v.
            equiv_get_value u v.
            unfold plus at 1; cbn.
            unfold h; equiv_simpl.
            apply module_homo_plus.
        }
        assert (∀ a v, h (a · v) = a · h v) as h_scalar.
        {
            intros a v.
            equiv_get_value v.
            unfold scalar_mult at 1; cbn.
            unfold h; equiv_simpl.
            apply module_homo_scalar.
        }
        assert (∀ u v, h (u * v) = h u * h v) as h_mult.
        {
            intros u v.
            equiv_get_value u v.
            unfold mult at 1; cbn.
            unfold h; equiv_simpl.
            apply homo_mult.
        }
        assert (h 1 = 1) as h_one.
        {
            unfold h.
            unfold one at 1; equiv_simpl.
            unfold h1.
            unfold one at 1; cbn.
            rewrite (free_extend_free _ _).
            rewrite list_image_end.
            reflexivity.
        }
        exists (make_algebra_homomorphism U (geometric_algebra_object B) _
            h h_plus h_scalar h_mult h_one).
        intros x; cbn.
        unfold h, vector_to_geo.
        unfold to_qring.
        equiv_simpl.
        apply h1_vec.
    -   intros [f1 f1_eq] [f2 f2_eq].
        apply set_type_eq; cbn.
        apply algebra_homomorphism_eq.
        intros v.
        equiv_get_value v.
        change (to_equiv (ideal_equiv (ga_ideal B)) v) with
            (to_qring (ga_ideal B) v).
        induction v as [|a v] using grade_induction.
        {
            rewrite to_qring_zero.
            do 2 rewrite algebra_homo_zero.
            reflexivity.
        }
        rewrite to_qring_plus.
        do 2 rewrite algebra_homo_plus.
        rewrite IHv.
        apply rplus.
        clear v IHv.
        destruct a as [v [l vl]]; cbn.
        apply to_free_ex in vl as [α v_eq]; subst v.
        rewrite to_qring_scalar.
        do 2 rewrite algebra_homo_scalar.
        apply f_equal.
        clear α.
        induction l.
        {
            do 2 rewrite algebra_homo_one.
            reflexivity.
        }
        rewrite <- list_conc_single.
        rewrite <- (free_bilinear_free U (list V)
            (λ a b, to_free U (list V) (a + b) : free_linear _ _) [a] l).
        change (free_bilinear _ _ _ _ _) with (to_free U _ [a] * to_free U _ l).
        rewrite to_qring_mult.
        do 2 rewrite algebra_homo_mult.
        rewrite IHl.
        apply rmult.
        clear l IHl.
        rewrite f1_eq, f2_eq.
        reflexivity.
Qed.

Definition to_geometric_algebra := ex_val geometric_algebra_ex.
Definition geometric_algebra := to_geo_algebra to_geometric_algebra.
Definition vector_to_geo := to_geo_homo to_geometric_algebra.
Definition geo_contract := to_geo_contract to_geometric_algebra
    : ∀ v, vector_to_geo v * vector_to_geo v = [B|] v v · 1.
Definition geometric_universal := ex_proof geometric_algebra_ex
    : @initial TO_GEO to_geometric_algebra.

Definition scalar_to_geo a : geometric_algebra := a · 1.
Local Notation "'σ'" := scalar_to_geo.

Theorem scalar_to_geo_plus : ∀ a b, σ (a + b) = σ a + σ b.
Proof.
    intros a b.
    unfold scalar_to_geo.
    apply scalar_rdist.
Qed.

Theorem scalar_to_geo_zero : σ 0 = 0.
Proof.
    unfold scalar_to_geo.
    apply scalar_lanni.
Qed.

Theorem scalar_to_geo_mult : ∀ a b, σ (a * b) = σ a * σ b.
Proof.
    intros a b.
    unfold scalar_to_geo.
    rewrite scalar_lmult, scalar_rmult.
    rewrite mult_lid.
    rewrite scalar_comp.
    reflexivity.
Qed.

Theorem scalar_to_geo_scalar : ∀ a A, σ a * A = a · A.
Proof.
    intros a A.
    unfold scalar_to_geo.
    rewrite scalar_lmult.
    rewrite mult_lid.
    reflexivity.
Qed.

Theorem scalar_to_geo_neg : ∀ a, σ (-a) = -σ a.
Proof.
    intros a.
    unfold scalar_to_geo.
    apply scalar_lneg.
Qed.

Theorem scalar_to_geo_one : σ 1 = 1.
Proof.
    unfold scalar_to_geo.
    apply scalar_id.
Qed.

Theorem scalar_to_geo_comm : ∀ a A, σ a * A = A * σ a.
Proof.
    intros a A.
    unfold scalar_to_geo.
    rewrite scalar_lmult, scalar_rmult.
    rewrite mult_lid, mult_rid.
    reflexivity.
Qed.

End GeometricCategory.

Declare Scope geo_scope.
Delimit Scope geo_scope with geo.
