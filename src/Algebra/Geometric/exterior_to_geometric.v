Require Import init.

Require Import set.
Require Import card.
Require Import unordered_list.

Require Import module_category.
Require Import algebra_category.
Require Import linear_bilinear_form.
Require Import linear_sum.
Require Import linear_transformation_space.

Require Export geometric_construct.
Require Export geometric_universal.
Require Export exterior_construct.
Require Import exterior_universal.

Section ExteriorToGeometric.

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

Let GP := ga_plus B.
Let GZ := ga_zero B.
Let GN := ga_neg B.
Let GPA := ga_plus_assoc B.
Let GPC := ga_plus_comm B.
Let GPZ := ga_plus_lid B.
Let GPN := ga_plus_linv B.
Let GM := ga_mult B.
Let GO := ga_one B.
Let GMA := ga_mult_assoc B.
Let GML := ga_mult_lid B.
Let GMR := ga_mult_rid B.
Let GS := ga_scalar B.
Let GSO := ga_scalar_id B.
Let GSL := ga_scalar_ldist B.
Let GSR := ga_scalar_rdist B.
Let GSC := ga_scalar_comp B.
Let GL := ga_ldist B.
Let GR := ga_rdist B.
Let GSML := ga_scalar_lmult B.
Let GSMR := ga_scalar_rmult B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GMA GML GMR GS GSO GSL GSR GSC
    GL GR GSML GSMR.

Let G12 := direct_sum (algebra_module (geometric_algebra B))
                       (algebra_module (geometric_algebra B)).
Let G12P := module_plus G12.
Let G12S := module_scalar G12.

Existing Instances G12P G12S.

Definition ga_mult_inner_base1 (a : module_V V) (v : module_V V) (p : module_V G12)
    := (
        vector_to_ga B v * fst p,
        -vector_to_ga B v * snd p + [B|] a v · (fst p)
    ) : module_V G12.

Lemma ga_mult_inner_base_plus : ∀ a v p1 p2, ga_mult_inner_base1 a v (p1 + p2) =
        ga_mult_inner_base1 a v p1 + ga_mult_inner_base1 a v p2.
    intros a v [p11 p12] [p21 p22]; cbn.
    unfold ga_mult_inner_base1; cbn.
    unfold plus at 1 3 4 5; cbn.
    apply f_equal2.
    -   apply ldist.
    -   rewrite ldist.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        rewrite scalar_ldist.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.

Lemma ga_mult_inner_base_scalar : ∀ a v b p, ga_mult_inner_base1 a v (b · p) =
        b · ga_mult_inner_base1 a v p.
    intros a v b [p1 p2].
    unfold ga_mult_inner_base1; cbn.
    unfold scalar_mult at 1 2 4 5; cbn.
    apply f_equal2.
    -   apply scalar_rmult.
    -   rewrite scalar_rmult.
        rewrite scalar_comp.
        rewrite (mult_comm _ b).
        rewrite <- scalar_comp.
        rewrite scalar_ldist.
        reflexivity.
Qed.

Definition ga_mult_inner_base2 (a : module_V V) (v : module_V V) :=
    make_module_homomorphism F G12 G12
    (ga_mult_inner_base1 a v)
    (ga_mult_inner_base_plus a v)
    (ga_mult_inner_base_scalar a v).

Let G3 := linear_trans_algebra G12.
Let G3P := algebra_plus G3.
Let G3S := algebra_scalar G3.
Let G3M := algebra_mult G3.
Let G3O := algebra_one G3.

Existing Instances G3P G3S G3M G3O.

Lemma ga_mult_inner_base2_plus : ∀ a v1 v2, ga_mult_inner_base2 a (v1 + v2) =
        ga_mult_inner_base2 a v1 + ga_mult_inner_base2 a v2.
    intros a v1 v2.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold plus at 2; cbn.
    unfold ga_mult_inner_base2, linear_trans_plus_base; cbn.
    unfold ga_mult_inner_base1; cbn.
    unfold plus at 5; cbn.
    apply f_equal2.
    -   rewrite (vector_to_ga_plus B).
        apply rdist.
    -   rewrite (vector_to_ga_plus B).
        rewrite neg_plus.
        rewrite rdist.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        rewrite bilinear_form_rplus.
        rewrite scalar_rdist.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.

Lemma ga_mult_inner_base2_scalar : ∀ a b v,
        ga_mult_inner_base2 a (b · v) = b · ga_mult_inner_base2 a v.
    intros a b v.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold scalar_mult at 2; cbn.
    unfold linear_trans_scalar_base; cbn.
    unfold ga_mult_inner_base1; cbn.
    unfold scalar_mult at 5; cbn.
    apply f_equal2.
    -   rewrite (vector_to_ga_scalar B).
        apply scalar_lmult.
    -   rewrite (vector_to_ga_scalar B).
        rewrite bilinear_form_rscalar.
        rewrite <- scalar_comp.
        rewrite scalar_ldist.
        do 2 rewrite mult_lneg.
        rewrite scalar_rneg.
        rewrite scalar_lmult.
        reflexivity.
Qed.

Lemma ga_mult_inner_base_contract : ∀ a v,
        ga_mult_inner_base2 a v * ga_mult_inner_base2 a v = [B|] v v · 1.
    intros a v.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold mult, scalar_mult, one; cbn.
    unfold linear_trans_scalar_base, ga_mult_inner_base1; cbn.
    unfold scalar_mult at 3; cbn.
    apply f_equal2.
    -   rewrite mult_assoc.
        rewrite (ga_contract B).
        rewrite scalar_lmult.
        rewrite mult_lid.
        reflexivity.
    -   rewrite ldist.
        rewrite mult_assoc.
        rewrite mult_lneg, mult_rneg.
        rewrite (ga_contract B).
        rewrite neg_neg.
        rewrite <- scalar_rmult.
        rewrite mult_lneg.
        rewrite plus_rlinv.
        rewrite scalar_lmult.
        rewrite mult_lid.
        reflexivity.
Qed.

Definition ga_mult_inner_base3 a := make_module_homomorphism
    F
    V
    (algebra_module G3)
    (ga_mult_inner_base2 a)
    (ga_mult_inner_base2_plus a)
    (ga_mult_inner_base2_scalar a).

Definition ga_mult_inner_base4 a := make_to_ga
    B
    G3
    (ga_mult_inner_base3 a)
    (ga_mult_inner_base_contract a).

Definition ga_mult_inner_base a
    := card_one_ex (geometric_universal B (ga_mult_inner_base4 a)).

Definition ga_mult_inner_f_homo a := [ga_mult_inner_base a|].
Definition ga_mult_inner_f a := algebra_homo_f (ga_mult_inner_f_homo a).

Theorem ga_mult_inner_f_eq : ∀ a v,
        ga_mult_inner_f a (vector_to_ga B v) = ga_mult_inner_base2 a v.
    intros a.
    apply [|ga_mult_inner_base a].
Qed.

Theorem ga_mult_inner_f_mult : ∀ a u v,
        ga_mult_inner_f a (u * v) = ga_mult_inner_f a u * ga_mult_inner_f a v.
    intros a u v.
    apply algebra_homo_mult.
Qed.

Definition ga_mult_inner a v := snd (module_homo_f (ga_mult_inner_f a v) (1, 0)).

Theorem ga_mult_inner_rplus : ∀ a u v,
        ga_mult_inner a (u + v) = ga_mult_inner a u + ga_mult_inner a v.
    intros a u v.
    unfold ga_mult_inner.
    unfold ga_mult_inner_f.
    rewrite algebra_homo_plus.
    unfold plus at 1; cbn.
    unfold linear_trans_plus_base.
    unfold plus at 1; cbn.
    reflexivity.
Qed.

Theorem ga_mult_inner_rscalar : ∀ a α v,
        ga_mult_inner a (α · v) = α · ga_mult_inner a v.
    intros a α v.
    unfold ga_mult_inner.
    unfold ga_mult_inner_f.
    rewrite algebra_homo_scalar.
    unfold scalar_mult at 1; cbn.
    unfold linear_trans_scalar_base.
    unfold scalar_mult at 1; cbn.
    reflexivity.
Qed.

Theorem ga_mult_inner_rzero : ∀ a, ga_mult_inner a 0 = 0.
    intros a.
    rewrite <- (scalar_lanni 0).
    rewrite ga_mult_inner_rscalar.
    apply scalar_lanni.
Qed.

Theorem ga_mult_inner_rneg : ∀ a v, ga_mult_inner a (-v) = -ga_mult_inner a v.
    intros a v.
    rewrite <- scalar_neg_one.
    rewrite ga_mult_inner_rscalar.
    apply scalar_neg_one.
Qed.

Theorem ga_mult_inner_add : ∀ a v x,
        ga_mult_inner a (vector_to_ga B v * x) =
        [B|] a v · x - vector_to_ga B v * ga_mult_inner a x.
    intros a v x.
    pose proof (ga_sum B x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_ranni.
        rewrite ga_mult_inner_rzero.
        rewrite mult_ranni.
        rewrite scalar_ranni.
        rewrite neg_zero, plus_rid.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ldist.
    rewrite scalar_rmult.
    rewrite ga_mult_inner_rplus.
    rewrite IHl; clear IHl.
    rewrite ga_mult_inner_rplus.
    rewrite ldist.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite scalar_ldist.
    rewrite <- plus_assoc.
    rewrite (plus_comm _ (-(vector_to_ga B v * _))).
    rewrite plus_assoc.
    apply rplus.
    clear l.
    do 2 rewrite ga_mult_inner_rscalar.
    rewrite scalar_rmult.
    rewrite scalar_comp.
    rewrite (mult_comm _ α).
    rewrite <- scalar_comp.
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    apply f_equal.
    unfold ga_mult_inner.
    rewrite ga_mult_inner_f_mult.
    rewrite ga_mult_inner_f_eq.
    unfold mult at 1; cbn.
    rewrite plus_comm.
    rewrite mult_lneg.
    apply rplus.
    induction x as [|x l].
    {
        cbn.
        unfold ga_mult_inner_f.
        rewrite algebra_homo_one.
        unfold one at 1; cbn.
        reflexivity.
    }
    cbn.
    rewrite ga_mult_inner_f_mult.
    unfold mult at 1; cbn.
    unfold linear_trans_mult_base.
    rewrite ga_mult_inner_f_eq.
    cbn.
    rewrite <- scalar_rmult.
    rewrite IHl; clear IHl.
    rewrite scalar_rmult.
    reflexivity.
Qed.

Theorem ga_mult_inner_scalar : ∀ a α, ga_mult_inner a (scalar_to_ga B α) = 0.
    intros a α.
    unfold ga_mult_inner.
    unfold ga_mult_inner_f.
    rewrite scalar_to_ga_one_scalar.
    rewrite algebra_homo_scalar.
    rewrite algebra_homo_one.
    unfold scalar_mult; cbn.
    unfold linear_trans_scalar_base.
    unfold one at 1; cbn.
    unfold scalar_mult; cbn.
    rewrite scalar_ranni.
    reflexivity.
Qed.

Theorem ga_mult_inner_vector : ∀ a v,
        ga_mult_inner a (vector_to_ga B v) = [B|] a v · 1.
    intros a v.
    rewrite <- (mult_rid (vector_to_ga B v)).
    rewrite ga_mult_inner_add.
    unfold GO.
    rewrite <- scalar_to_ga_one at 2.
    rewrite ga_mult_inner_scalar.
    rewrite mult_ranni.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem ga_mult_inner_bivector : ∀ a u v,
        ga_mult_inner a (vector_to_ga B u * vector_to_ga B v) =
        [B|] a u · vector_to_ga B v -
        [B|] a v · vector_to_ga B u.
    intros a u v.
    rewrite ga_mult_inner_add.
    rewrite ga_mult_inner_vector.
    rewrite scalar_rmult.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem ga_mult_inner_lplus : ∀ a b v,
        ga_mult_inner (a + b) v = ga_mult_inner a v + ga_mult_inner b v.
    intros a b v.
    pose proof (ga_sum B v) as [l l_eq]; subst v.
    induction l as [|[α v] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite ga_mult_inner_rzero.
        rewrite plus_rid.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 3 rewrite ga_mult_inner_rplus.
    rewrite IHl; clear IHl.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite <- plus_assoc.
    rewrite (plus_comm (ga_mult_inner a (ulist_sum _))).
    rewrite plus_assoc.
    apply rplus; clear l.
    do 3 rewrite ga_mult_inner_rscalar.
    rewrite <- scalar_ldist.
    apply f_equal.
    induction v as [|v l].
    {
        cbn.
        rewrite <- scalar_to_ga_one.
        do 3 rewrite ga_mult_inner_scalar.
        rewrite plus_rid.
        reflexivity.
    }
    cbn.
    do 3 rewrite ga_mult_inner_add.
    rewrite IHl; clear IHl.
    rewrite ldist.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite bilinear_form_lplus.
    rewrite scalar_rdist.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    apply plus_comm.
Qed.

Theorem ga_mult_inner_lscalar : ∀ α a v,
        ga_mult_inner (α · a) v = α · ga_mult_inner a v.
    intros α a v.
    pose proof (ga_sum B v) as [l l_eq]; subst v.
    induction l as [|[β v] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite ga_mult_inner_rzero.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite ga_mult_inner_rplus.
    rewrite IHl; clear IHl.
    rewrite scalar_ldist.
    apply rplus; clear l.
    do 2 rewrite ga_mult_inner_rscalar.
    rewrite scalar_comp.
    rewrite mult_comm.
    rewrite <- scalar_comp.
    apply f_equal; clear β.
    induction v as [|v l].
    {
        cbn.
        rewrite <- scalar_to_ga_one.
        do 2 rewrite ga_mult_inner_scalar.
        rewrite scalar_ranni.
        reflexivity.
    }
    cbn.
    do 2 rewrite ga_mult_inner_add.
    rewrite IHl; clear IHl.
    rewrite bilinear_form_lscalar.
    rewrite scalar_ldist.
    rewrite scalar_comp.
    rewrite scalar_rneg.
    rewrite scalar_rmult.
    reflexivity.
Qed.

Definition ga_mult_inner_homo a := make_module_homomorphism
    F
    (algebra_module (geometric_algebra B))
    (algebra_module (geometric_algebra B))
    (ga_mult_inner a)
    (ga_mult_inner_rplus a)
    (ga_mult_inner_rscalar a).

Definition ga_mult_homo a := make_module_homomorphism
    F
    (algebra_module (geometric_algebra B))
    (algebra_module (geometric_algebra B))
    (mult (vector_to_ga B a))
    (ldist (vector_to_ga B a))
    (λ α v, scalar_rmult α (vector_to_ga B a) v).

Let GG := linear_trans_algebra (algebra_module (geometric_algebra B)).
Let GGP := algebra_plus GG.
Let GGZ := algebra_zero GG.
Let GGN := algebra_neg GG.
Let GGPA := algebra_plus_assoc GG.
Let GGPC := algebra_plus_comm GG.
Let GGPZ := algebra_plus_lid GG.
Let GGPN := algebra_plus_linv GG.
Let GGM := algebra_mult GG.
Let GGO := algebra_one GG.
Let GGL := algebra_ldist GG.
Let GGR := algebra_rdist GG.
Let GGS := algebra_scalar GG.
Let GGSL := algebra_scalar_ldist GG.

Existing Instances GGP GGZ GGN GGPA GGPC GGPZ GGPN GGM GGO GGL GGR GGS GGSL.

Theorem ga_mult_inner_alternating : ∀ a,
        ga_mult_inner_homo a * ga_mult_inner_homo a = 0.
    intros a.
    apply module_homomorphism_eq.
    intros x.
    unfold mult at 1; cbn.
    unfold zero at 1; cbn.
    unfold linear_trans_zero_base.
    pose proof (ga_sum B x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite ga_mult_inner_rzero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite ga_mult_inner_rplus.
    rewrite IHl; clear IHl l.
    rewrite plus_rid.
    do 2 rewrite ga_mult_inner_rscalar.
    rewrite <- (scalar_ranni α).
    apply f_equal.
    induction x as [|v l].
    {
        cbn.
        rewrite <- scalar_to_ga_one.
        rewrite ga_mult_inner_scalar.
        apply ga_mult_inner_rzero.
    }
    cbn.
    rewrite ga_mult_inner_add.
    rewrite ga_mult_inner_rplus.
    rewrite ga_mult_inner_rneg.
    rewrite ga_mult_inner_add.
    rewrite IHl.
    rewrite mult_ranni.
    rewrite neg_zero, plus_rid.
    rewrite ga_mult_inner_rscalar.
    rewrite plus_rinv.
    reflexivity.
Qed.

Theorem ga_mult_contract : ∀ a, ga_mult_homo a * ga_mult_homo a = [B|] a a · 1.
    intros a.
    apply module_homomorphism_eq.
    intros x.
    unfold mult at 1; cbn.
    unfold scalar_mult at 1, one at 1; cbn.
    unfold linear_trans_scalar_base; cbn.
    rewrite mult_assoc.
    rewrite (ga_contract B).
    rewrite scalar_lmult.
    rewrite mult_lid.
    reflexivity.
Qed.

Definition ext_to_geo_base1 a := -ga_mult_inner_homo a + ga_mult_homo a.

Lemma ext_to_geo_base1_plus : ∀ u v,
        ext_to_geo_base1 (u + v) = ext_to_geo_base1 u + ext_to_geo_base1 v.
    intros u v.
    unfold ext_to_geo_base1.
    apply module_homomorphism_eq.
    intros x.
    unfold plus at 1 4 5 6; cbn.
    unfold linear_trans_plus_base; cbn.
    unfold neg at 1 2 3; cbn.
    unfold linear_trans_neg_base; cbn.
    rewrite ga_mult_inner_lplus.
    rewrite (vector_to_ga_plus B).
    rewrite rdist.
    rewrite neg_plus.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply plus_comm.
Qed.

Lemma ext_to_geo_base1_scalar : ∀ a v,
        ext_to_geo_base1 (a · v) = a · ext_to_geo_base1 v.
    intros a v.
    unfold ext_to_geo_base1.
    apply module_homomorphism_eq.
    intros x.
    rewrite scalar_ldist.
    unfold scalar_mult at 3 4, plus at 1 2; cbn.
    unfold linear_trans_plus_base, linear_trans_scalar_base; cbn.
    unfold neg at 1 2; cbn.
    unfold linear_trans_neg_base; cbn.
    rewrite ga_mult_inner_lscalar.
    rewrite (vector_to_ga_scalar B).
    rewrite scalar_lmult.
    rewrite scalar_rneg.
    reflexivity.
Qed.

Lemma ext_to_geo_base_alternating : ∀ v,
        0 = ext_to_geo_base1 v * ext_to_geo_base1 v.
    intros v.
    unfold ext_to_geo_base1.
    rewrite ldist.
    do 2 rewrite rdist.
    rewrite mult_lneg.
    rewrite mult_rneg.
    rewrite neg_neg.
    rewrite mult_lneg, mult_rneg.
    rewrite ga_mult_inner_alternating, ga_mult_contract.
    rewrite plus_lid.
    apply module_homomorphism_eq.
    intros x.
    unfold neg at 1 2; cbn.
    unfold linear_trans_neg_base; cbn.
    unfold mult at 1 2, plus at 1 2; cbn.
    unfold linear_trans_plus_base; cbn.
    unfold scalar_mult at 1; cbn.
    unfold linear_trans_scalar_base.
    unfold one at 1; cbn.
    unfold mult at 2; cbn.
    unfold zero at 1; cbn.
    unfold linear_trans_zero_base.
    rewrite ga_mult_inner_add.
    rewrite neg_plus.
    rewrite neg_neg.
    rewrite (plus_comm (-([B|] v v · x))).
    rewrite plus_rlinv.
    rewrite plus_linv.
    reflexivity.
Qed.

Definition ext_to_geo_base2 := make_module_homomorphism
    F
    V
    (algebra_module GG)
    ext_to_geo_base1
    ext_to_geo_base1_plus
    ext_to_geo_base1_scalar.

Definition ext_to_geo_base3 := make_to_ext
    V GG ext_to_geo_base2 ext_to_geo_base_alternating.

Definition ext_to_geo_base :=
    card_one_ex (exterior_universal V ext_to_geo_base3).
Definition ext_to_geo_f_homo := [ext_to_geo_base|].
Definition ext_to_geo_f := algebra_homo_f ext_to_geo_f_homo.

Let EP := ext_plus V.
Let EZ := ext_zero V.
Let EN := ext_neg V.
Let EPA := ext_plus_assoc V.
Let EPC := ext_plus_comm V.
Let EPZ := ext_plus_lid V.
Let EPN := ext_plus_linv V.
Let EM := ext_mult V.
Let EO := ext_one V.
Let EMR := ext_mult_rid V.
Let ES := ext_scalar V.
Let ESO := ext_scalar_id V.
Let ESR := ext_scalar_rdist V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO EMR ES ESO ESR.

Theorem ext_to_geo_f_eq :
        ∀ v, ext_to_geo_f (vector_to_ext V v) = ext_to_geo_base1 v.
    apply [|ext_to_geo_base].
Qed.

Theorem ext_to_geo_f_mult :
        ∀ u v, ext_to_geo_f (u * v) = ext_to_geo_f u * ext_to_geo_f v.
    apply algebra_homo_mult.
Qed.

Definition ext_to_geo (v : ext V) := module_homo_f (ext_to_geo_f v) 1 : ga B.

Theorem ext_to_geo_plus : ∀ u v,
        ext_to_geo (u + v) = ext_to_geo u + ext_to_geo v.
    intros u v.
    unfold ext_to_geo.
    unfold ext_to_geo_f.
    rewrite algebra_homo_plus.
    unfold plus at 1; cbn.
    unfold linear_trans_plus_base.
    reflexivity.
Qed.

Theorem ext_to_geo_scalar : ∀ a v, ext_to_geo (a · v) = a · ext_to_geo v.
    intros a v.
    unfold ext_to_geo.
    unfold ext_to_geo_f.
    rewrite algebra_homo_scalar.
    unfold scalar_mult at 1; cbn.
    unfold linear_trans_scalar_base.
    reflexivity.
Qed.

Theorem ext_to_geo_add : ∀ v x, ext_to_geo (vector_to_ext V v * x) =
        -ga_mult_inner v (ext_to_geo x) + vector_to_ga B v * ext_to_geo x.
    intros v x.
    unfold ext_to_geo.
    rewrite ext_to_geo_f_mult.
    rewrite ext_to_geo_f_eq.
    unfold mult at 1; cbn.
    unfold linear_trans_mult_base; cbn.
    unfold ext_to_geo_base1; cbn.
    unfold plus at 1; cbn.
    unfold linear_trans_plus_base; cbn.
    reflexivity.
Qed.

Theorem ext_to_geo_neg : ∀ x, ext_to_geo (-x) = -ext_to_geo x.
    intros x.
    rewrite <- scalar_neg_one.
    rewrite ext_to_geo_scalar.
    apply scalar_neg_one.
Qed.

Theorem ext_to_geo_zero : ext_to_geo 0 = 0.
    rewrite <- (scalar_lanni 0).
    rewrite ext_to_geo_scalar.
    apply scalar_lanni.
Qed.

Theorem ext_to_geo_one : ext_to_geo 1 = 1.
    unfold ext_to_geo.
    unfold ext_to_geo_f.
    rewrite algebra_homo_one.
    unfold one at 1; cbn.
    reflexivity.
Qed.

Theorem ext_to_geo_of_scalar : ∀ α,
        ext_to_geo (scalar_to_ext V α) = scalar_to_ga B α.
    intros α.
    rewrite scalar_to_ext_one_scalar.
    rewrite ext_to_geo_scalar.
    change 1 with (one (U := ext V)).
    rewrite ext_to_geo_one.
    symmetry; apply scalar_to_ga_one_scalar.
Qed.

Theorem ext_to_geo_vector : ∀ v,
        ext_to_geo (vector_to_ext V v) = vector_to_ga B v.
    intros v.
    rewrite <- (mult_rid (vector_to_ext V v)).
    rewrite ext_to_geo_add.
    change 1 with (one (U := ext V)).
    rewrite ext_to_geo_one.
    rewrite mult_rid.
    replace 1 with (scalar_to_ga B 1) by apply scalar_to_ga_one.
    rewrite ga_mult_inner_scalar.
    rewrite neg_zero.
    apply plus_lid.
Qed.

Theorem ext_to_geo_vector2 : ∀ u v,
        ext_to_geo (vector_to_ext V u * vector_to_ext V v) =
        -[B|] u v · 1 + vector_to_ga B u * vector_to_ga B v.
    intros u v.
    rewrite ext_to_geo_add.
    rewrite ext_to_geo_vector.
    rewrite ga_mult_inner_vector.
    rewrite scalar_lneg.
    reflexivity.
Qed.

End ExteriorToGeometric.
