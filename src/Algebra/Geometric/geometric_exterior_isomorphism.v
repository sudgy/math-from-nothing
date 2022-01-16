Require Import init.

Require Import set.
Require Import unordered_list.
Require Import mult_product.

Require Import module_category.
Require Import algebra_category.
Require Import linear_bilinear_form.

Require Export geometric_construct.
Require Export exterior_construct.
Require Import exterior_to_geometric.
Require Import geometric_to_exterior.

Section GeometricExteriorIso.

Context {F : CRing} {V : Module F}.

Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMC := cring_mult_comm F.

Existing Instances UP UZ UN UPC UPZ UPN UM UO UMC.

Let VP := module_plus V.
Let VS := module_scalar V.

Existing Instances VP VS.

Context (B : set_type bilinear_form).

Let EP := ext_plus V.
Let EZ := ext_zero V.
Let EN := ext_neg V.
Let EPA := ext_plus_assoc V.
Let EPC := ext_plus_comm V.
Let EPZ := ext_plus_lid V.
Let EPN := ext_plus_linv V.
Let EM := ext_mult V.
Let EL := ext_ldist V.
Let ER := ext_rdist V.
Let EO := ext_one V.
Let EMA := ext_mult_assoc V.
Let ES := ext_scalar V.
Let ESL := ext_scalar_ldist V.
Let ESR := ext_scalar_rdist V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EL ER EO EMA ES ESL ESR.

Let GP := ga_plus B.
Let GZ := ga_zero B.
Let GN := ga_neg B.
Let GPA := ga_plus_assoc B.
Let GPC := ga_plus_comm B.
Let GPZ := ga_plus_lid B.
Let GPN := ga_plus_linv B.
Let GM := ga_mult B.
Let GL := ga_ldist B.
Let GR := ga_rdist B.
Let GS := ga_scalar B.
Let GSL := ga_scalar_ldist B.
Let GSC := ga_scalar_comp B.
Let GSMR := ga_scalar_rmult B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GL GR GS GSL GSC GSMR.

Lemma ext_inner_inner : ∀ a b (x : ext V),
        ext_inner B a (ext_inner B b x) + ext_inner B b (ext_inner B a x) = 0.
    intros a b x.
    symmetry; apply plus_0_ab_a_nb.
    pose proof (ext_sum V x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 4 rewrite ext_inner_rzero.
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
        cbn.
        rewrite <- scalar_to_ext_one.
        do 2 rewrite ext_inner_scalar.
        do 2 rewrite ext_inner_rzero.
        symmetry; apply neg_zero.
    }
    cbn.
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

Lemma ga_mult_inner_inner : ∀ a b (x : ga B),
        ga_mult_inner B a (ga_mult_inner B b x) +
        ga_mult_inner B b (ga_mult_inner B a x) = 0.
    intros a b x.
    symmetry; apply plus_0_ab_a_nb.
    pose proof (ga_sum B x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 4 rewrite ga_mult_inner_rzero.
        symmetry; apply neg_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 4 rewrite ga_mult_inner_rplus.
    rewrite IHl; clear IHl.
    rewrite neg_plus.
    apply rplus; clear l.
    do 4 rewrite ga_mult_inner_rscalar.
    rewrite <- scalar_rneg.
    apply f_equal.
    induction x as [|u l].
    {
        cbn.
        rewrite <- scalar_to_ga_one.
        do 2 rewrite ga_mult_inner_scalar.
        do 2 rewrite ga_mult_inner_rzero.
        symmetry; apply neg_zero.
    }
    cbn.
    do 2 rewrite ga_mult_inner_add.
    do 2 rewrite ga_mult_inner_rplus.
    rewrite neg_plus.
    do 2 rewrite ga_mult_inner_rneg.
    rewrite neg_neg.
    do 2 rewrite ga_mult_inner_add.
    rewrite IHl; clear IHl.
    rewrite mult_rneg.
    rewrite neg_neg.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    do 2 rewrite ga_mult_inner_rscalar.
    apply plus_comm.
Qed.

Lemma geo_to_ext_inner : ∀ a (x : ga B),
        geo_to_ext B (ga_mult_inner B a x) = ext_inner B a (geo_to_ext B x).
    intros a x.
    pose proof (ga_sum B x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ga_mult_inner_rzero.
        do 2 rewrite geo_to_ext_zero.
        symmetry; apply ext_inner_rzero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ga_mult_inner_rplus.
    do 2 rewrite geo_to_ext_plus.
    rewrite ext_inner_rplus.
    rewrite IHl; clear IHl.
    apply rplus.
    rewrite ga_mult_inner_rscalar.
    do 2 rewrite geo_to_ext_scalar.
    rewrite ext_inner_rscalar.
    apply f_equal.
    clear α l.
    induction x as [|b l].
    {
        cbn.
        rewrite <- scalar_to_ga_one.
        rewrite geo_to_ext_of_scalar.
        rewrite ga_mult_inner_scalar.
        rewrite ext_inner_scalar.
        apply geo_to_ext_zero.
    }
    cbn.
    rewrite ga_mult_inner_add.
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

Lemma ext_to_geo_inner : ∀ a (x : ext V),
        ext_to_geo B (ext_inner B a x) = ga_mult_inner B a (ext_to_geo B x).
    intros a x.
    pose proof (ext_sum V x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ext_inner_rzero.
        do 2 rewrite ext_to_geo_zero.
        symmetry; apply ga_mult_inner_rzero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_inner_rplus.
    do 2 rewrite ext_to_geo_plus.
    rewrite ga_mult_inner_rplus.
    rewrite IHl; clear IHl.
    apply rplus.
    rewrite ext_inner_rscalar.
    do 2 rewrite ext_to_geo_scalar.
    rewrite ga_mult_inner_rscalar.
    apply f_equal.
    clear α l.
    induction x as [|b l].
    {
        cbn.
        rewrite <- scalar_to_ext_one.
        rewrite ext_to_geo_of_scalar.
        rewrite ext_inner_scalar.
        rewrite ga_mult_inner_scalar.
        apply ext_to_geo_zero.
    }
    cbn.
    rewrite ext_inner_add.
    rewrite ext_to_geo_add.
    rewrite ext_to_geo_plus, ext_to_geo_neg.
    rewrite ga_mult_inner_rplus.
    rewrite ext_to_geo_add.
    rewrite IHl; clear IHl.
    rewrite ga_mult_inner_add.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite ext_to_geo_scalar.
    rewrite plus_comm.
    apply rplus.
    rewrite neg_neg.
    rewrite ga_mult_inner_rneg.
    apply plus_0_ab_a_nb.
    symmetry; apply ga_mult_inner_inner.
Qed.

Theorem geo_to_ext_to_geo : ∀ x, geo_to_ext B (ext_to_geo B x) = x.
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
        cbn.
        replace (ext_to_geo B 1) with (@one _ (ga_one B))
            by (symmetry; apply (ext_to_geo_one B)).
        apply geo_to_ext_one.
    }
    cbn.
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
    intros x.
    pose proof (ga_sum B x) as [l l_eq]; subst x.
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
        cbn.
        rewrite geo_to_ext_one.
        apply ext_to_geo_one.
    }
    cbn.
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
    (ext_to_geo_scalar B) : cat_morphism (MODULE F) _ _.

Definition geo_to_ext_homo := make_module_homomorphism
    F
    (algebra_module (geometric_algebra B))
    (algebra_module (exterior_algebra V))
    (geo_to_ext B)
    (geo_to_ext_plus B)
    (geo_to_ext_scalar B) : cat_morphism (MODULE F) _ _.

Theorem ext_to_geo_to_ext_homo : ext_to_geo_homo ∘ geo_to_ext_homo = 𝟙.
    apply module_homomorphism_eq.
    intros x.
    cbn.
    apply ext_to_geo_to_ext.
Qed.
Theorem geo_to_ext_to_geo_homo : geo_to_ext_homo ∘ ext_to_geo_homo = 𝟙.
    apply module_homomorphism_eq.
    intros x.
    cbn.
    apply geo_to_ext_to_geo.
Qed.

Theorem ext_to_geo_iso : isomorphism ext_to_geo_homo.
    exists geo_to_ext_homo.
    split.
    -   exact ext_to_geo_to_ext_homo.
    -   exact geo_to_ext_to_geo_homo.
Qed.
Theorem geo_to_ext_iso : isomorphism geo_to_ext_homo.
    exists ext_to_geo_homo.
    split.
    -   exact geo_to_ext_to_geo_homo.
    -   exact ext_to_geo_to_ext_homo.
Qed.

Theorem geo_ext_iso : isomorphic (C0 := MODULE F)
        (algebra_module (geometric_algebra B))
        (algebra_module (exterior_algebra V)).
    exists geo_to_ext_homo.
    exact geo_to_ext_iso.
Qed.

Theorem scalar_to_ga_eq : ∀ a b, scalar_to_ga B a = scalar_to_ga B b → a = b.
    intros a b eq.
    apply (f_equal (geo_to_ext B)) in eq.
    do 2 rewrite geo_to_ext_of_scalar in eq.
    apply scalar_to_ext_eq in eq.
    exact eq.
Qed.

Theorem vector_to_ga_eq : ∀ a b, vector_to_ga B a = vector_to_ga B b → a = b.
    intros a b eq.
    apply (f_equal (geo_to_ext B)) in eq.
    do 2 rewrite geo_to_ext_vector in eq.
    apply vector_to_ext_eq in eq.
    exact eq.
Qed.

End GeometricExteriorIso.
