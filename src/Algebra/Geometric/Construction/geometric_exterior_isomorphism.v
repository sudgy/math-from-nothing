Require Import init.

Require Import set.
Require Import unordered_list.

Require Import module_category.
Require Import algebra_category.
Require Import linear_bilinear_form.

Require Import geometric_universal.
Require Import geometric_sum.
Require Import exterior_base.
Require Export exterior_to_geometric.
Require Export geometric_to_exterior.

Section GeometricExteriorIso.

Context {F : CRingObj} {V : ModuleObj F}.
Context (B : set_type (bilinear_form (V := V))).

Lemma ext_inner_inner : ∀ a b (x : exterior_algebra V),
    ext_inner B a (ext_inner B b x) + ext_inner B b (ext_inner B a x) = 0.
Proof.
    intros a b x.
    symmetry; apply plus_0_ab_a_nb.
    pose proof (ext_sum V x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite ext_inner_rzero.
        symmetry; apply neg_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 4 rewrite ext_inner_rplus.
    rewrite IHl; clear IHl.
    rewrite neg_plus.
    apply rplus; clear l.
    do 4 rewrite ext_inner_rscalar.
    rewrite <- scalar_rneg.
    apply f_equal.
    induction x as [|u l].
    {
        rewrite list_image_end; cbn.
        rewrite list_prod_end.
        rewrite <- scalar_to_ext_one.
        do 2 rewrite ext_inner_scalar.
        do 2 rewrite ext_inner_rzero.
        symmetry; apply neg_zero.
    }
    rewrite list_image_add; cbn.
    do 2 rewrite ext_inner_add.
    do 2 rewrite ext_inner_rplus.
    rewrite neg_plus.
    do 2 rewrite ext_inner_rneg.
    rewrite neg_neg.
    do 2 rewrite ext_inner_add.
    rewrite IHl; clear IHl.
    rewrite mult_rneg.
    rewrite neg_neg.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    do 2 rewrite ext_inner_rscalar.
    apply plus_comm.
Qed.

Lemma geo_mult_inner_inner : ∀ a b (x : geometric_algebra B),
    geo_mult_inner B a (geo_mult_inner B b x) +
    geo_mult_inner B b (geo_mult_inner B a x) = 0.
Proof.
    intros a b x.
    symmetry; apply plus_0_ab_a_nb.
    pose proof (geo_sum B x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 4 rewrite geo_mult_inner_rzero.
        symmetry; apply neg_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 4 rewrite geo_mult_inner_rplus.
    rewrite IHl; clear IHl.
    rewrite neg_plus.
    apply rplus; clear l.
    do 4 rewrite geo_mult_inner_rscalar.
    rewrite <- scalar_rneg.
    apply f_equal.
    induction x as [|u l].
    {
        rewrite list_image_end; cbn.
        rewrite list_prod_end.
        rewrite <- scalar_to_geo_one.
        do 2 rewrite geo_mult_inner_scalar.
        do 2 rewrite geo_mult_inner_rzero.
        symmetry; apply neg_zero.
    }
    rewrite list_image_add; cbn.
    do 2 rewrite geo_mult_inner_add.
    do 2 rewrite geo_mult_inner_rplus.
    rewrite neg_plus.
    do 2 rewrite geo_mult_inner_rneg.
    rewrite neg_neg.
    do 2 rewrite geo_mult_inner_add.
    rewrite IHl; clear IHl.
    rewrite mult_rneg.
    rewrite neg_neg.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    do 2 rewrite geo_mult_inner_rscalar.
    apply plus_comm.
Qed.

Lemma geo_to_ext_inner : ∀ a (x : geometric_algebra B),
    geo_to_ext B (geo_mult_inner B a x) = ext_inner B a (geo_to_ext B x).
Proof.
    intros a x.
    pose proof (geo_sum B x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite geo_mult_inner_rzero.
        do 2 rewrite geo_to_ext_zero.
        symmetry; apply ext_inner_rzero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite geo_mult_inner_rplus.
    do 2 rewrite geo_to_ext_plus.
    rewrite ext_inner_rplus.
    rewrite IHl; clear IHl.
    apply rplus.
    rewrite geo_mult_inner_rscalar.
    do 2 rewrite geo_to_ext_scalar.
    rewrite ext_inner_rscalar.
    apply f_equal.
    clear α l.
    induction x as [|b l].
    {
        rewrite list_image_end; cbn.
        rewrite list_prod_end.
        rewrite <- scalar_to_geo_one.
        rewrite geo_to_ext_of_scalar.
        rewrite geo_mult_inner_scalar.
        rewrite ext_inner_scalar.
        apply geo_to_ext_zero.
    }
    rewrite list_image_add; cbn.
    rewrite geo_mult_inner_add.
    rewrite geo_to_ext_add.
    rewrite geo_to_ext_plus, geo_to_ext_neg.
    rewrite ext_inner_rplus.
    rewrite geo_to_ext_add.
    rewrite IHl; clear IHl.
    rewrite ext_inner_add.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite geo_to_ext_scalar.
    rewrite plus_comm.
    apply rplus.
    apply plus_0_ab_na_b.
    symmetry; apply ext_inner_inner.
Qed.

Lemma ext_to_geo_inner : ∀ a (x : exterior_algebra V),
    ext_to_geo B (ext_inner B a x) = geo_mult_inner B a (ext_to_geo B x).
Proof.
    intros a x.
    pose proof (ext_sum V x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ext_inner_rzero.
        rewrite ext_to_geo_zero.
        symmetry; apply geo_mult_inner_rzero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_inner_rplus.
    do 2 rewrite ext_to_geo_plus.
    rewrite geo_mult_inner_rplus.
    rewrite IHl; clear IHl.
    apply rplus.
    rewrite ext_inner_rscalar.
    do 2 rewrite ext_to_geo_scalar.
    rewrite geo_mult_inner_rscalar.
    apply f_equal.
    clear α l.
    induction x as [|b l].
    {
        rewrite list_image_end; cbn.
        rewrite list_prod_end.
        rewrite <- scalar_to_ext_one.
        rewrite ext_to_geo_of_scalar.
        rewrite ext_inner_scalar.
        rewrite geo_mult_inner_scalar.
        apply ext_to_geo_zero.
    }
    rewrite list_image_add; cbn.
    rewrite ext_inner_add.
    rewrite ext_to_geo_add.
    rewrite ext_to_geo_plus, ext_to_geo_neg.
    rewrite geo_mult_inner_rplus.
    rewrite ext_to_geo_add.
    rewrite IHl; clear IHl.
    rewrite geo_mult_inner_add.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite ext_to_geo_scalar.
    rewrite plus_comm.
    apply rplus.
    rewrite neg_neg.
    rewrite geo_mult_inner_rneg.
    apply plus_0_ab_a_nb.
    symmetry; apply geo_mult_inner_inner.
Qed.

Theorem geo_to_ext_to_geo : ∀ x, geo_to_ext B (ext_to_geo B x) = x.
Proof.
    intros x.
    pose proof (ext_sum V x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ext_to_geo_zero.
        apply geo_to_ext_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite (ext_to_geo_plus B).
    rewrite (geo_to_ext_plus B).
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite (ext_to_geo_scalar B).
    rewrite (geo_to_ext_scalar B).
    apply f_equal.
    induction x as [|a l].
    {
        rewrite list_image_end; cbn.
        rewrite list_prod_end.
        rewrite ext_to_geo_one.
        apply geo_to_ext_one.
    }
    rewrite list_image_add; cbn.
    rewrite ext_to_geo_add.
    rewrite (geo_to_ext_plus B).
    rewrite geo_to_ext_add.
    rewrite IHl.
    rewrite (geo_to_ext_neg B).
    rewrite plus_assoc.
    apply plus_0_a_ab_b.
    rewrite plus_0_nab_a_b.
    rewrite geo_to_ext_inner.
    rewrite IHl.
    reflexivity.
Qed.

Theorem ext_to_geo_to_ext : ∀ x, ext_to_geo B (geo_to_ext B x) = x.
Proof.
    intros x.
    pose proof (geo_sum B x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite geo_to_ext_zero.
        apply ext_to_geo_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite geo_to_ext_plus.
    rewrite ext_to_geo_plus.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite geo_to_ext_scalar.
    rewrite ext_to_geo_scalar.
    apply f_equal.
    induction x as [|a l].
    {
        rewrite list_image_end; cbn.
        rewrite list_prod_end.
        rewrite geo_to_ext_one.
        apply ext_to_geo_one.
    }
    rewrite list_image_add; cbn.
    rewrite geo_to_ext_add.
    rewrite (ext_to_geo_plus B).
    rewrite ext_to_geo_add.
    rewrite IHl.
    rewrite plus_assoc.
    apply plus_0_a_ab_b.
    rewrite ext_to_geo_inner.
    rewrite IHl.
    rewrite plus_rinv.
    reflexivity.
Qed.

Definition ext_to_geo_homo := make_module_homomorphism
    F
    (algebra_module (exterior_algebra V))
    (algebra_module (geometric_algebra B))
    (ext_to_geo B)
    (ext_to_geo_plus B)
    (ext_to_geo_scalar B) : morphism (algebra_module (exterior_algebra V)) _.

Definition geo_to_ext_homo := make_module_homomorphism
    F
    (algebra_module (geometric_algebra B))
    (algebra_module (exterior_algebra V))
    (geo_to_ext B)
    (geo_to_ext_plus B)
    (geo_to_ext_scalar B) : morphism (algebra_module (geometric_algebra B)) _.

Theorem ext_to_geo_to_ext_homo : ext_to_geo_homo ∘ geo_to_ext_homo = 𝟙.
Proof.
    apply module_homomorphism_eq.
    intros x.
    cbn.
    apply ext_to_geo_to_ext.
Qed.
Theorem geo_to_ext_to_geo_homo : geo_to_ext_homo ∘ ext_to_geo_homo = 𝟙.
Proof.
    apply module_homomorphism_eq.
    intros x.
    cbn.
    apply geo_to_ext_to_geo.
Qed.

Theorem ext_to_geo_iso : isomorphism ext_to_geo_homo.
Proof.
    exists geo_to_ext_homo.
    split.
    -   exact ext_to_geo_to_ext_homo.
    -   exact geo_to_ext_to_geo_homo.
Qed.
Theorem geo_to_ext_iso : isomorphism geo_to_ext_homo.
Proof.
    exists ext_to_geo_homo.
    split.
    -   exact geo_to_ext_to_geo_homo.
    -   exact ext_to_geo_to_ext_homo.
Qed.

Theorem geo_ext_iso : isomorphic
    (algebra_module (geometric_algebra B))
    (algebra_module (exterior_algebra V)).
Proof.
    exists geo_to_ext_homo.
    exact geo_to_ext_iso.
Qed.

Theorem scalar_to_geo_eq : ∀ a b, scalar_to_geo B a = scalar_to_geo B b → a = b.
Proof.
    intros a b eq.
    apply (f_equal (geo_to_ext B)) in eq.
    do 2 rewrite geo_to_ext_of_scalar in eq.
    apply scalar_to_ext_eq in eq.
    exact eq.
Qed.

Theorem vector_to_geo_eq : ∀ a b, vector_to_geo B a = vector_to_geo B b → a = b.
Proof.
    intros a b eq.
    apply (f_equal (geo_to_ext B)) in eq.
    do 2 rewrite geo_to_ext_vector in eq.
    apply vector_to_ext_eq in eq.
    exact eq.
Qed.
(* begin hide *)

End GeometricExteriorIso.
(* end hide *)
