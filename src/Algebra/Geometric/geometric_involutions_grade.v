Require Import init.

Require Import mult_product.
Require Import mult_pow.

Require Export geometric_construct.
Require Import geometric_exterior_isomorphism.
Require Import geometric_grade.
Require Import exterior_grade.
Require Import geometric_involutions.
Require Import exterior_involutions.

Section GeometricInvolutions.

Context {F : CRing} {V : Module F}.

Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UL := cring_ldist F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.

Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UL UMA UMC UMO.

Let VP := module_plus V.
Let VS := module_scalar V.

Existing Instances VP VS.

Context (B : set_type bilinear_form).

Let GP := geo_plus B.
Let GZ := geo_zero B.
Let GN := geo_neg B.
Let GPA := geo_plus_assoc B.
Let GPC := geo_plus_comm B.
Let GPZ := geo_plus_lid B.
Let GPN := geo_plus_linv B.
Let GM := geo_mult B.
Let GO := geo_one B.
Let GL := geo_ldist B.
Let GR := geo_rdist B.
Let GMA := geo_mult_assoc B.
Let GS := geo_scalar B.
Let GSO := geo_scalar_id B.
Let GSL := geo_scalar_ldist B.
Let GSR := geo_scalar_rdist B.
Let GSC := geo_scalar_comp B.
Let GSML := geo_scalar_lmult B.
Let GSMR := geo_scalar_rmult B.
Let GG := geo_grade B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GL GR GMA GS GSO GSL GSR GSC
    GSML GSMR GG.

Local Notation "'φ'" := (vector_to_geo B).
Local Notation "'σ'" := (scalar_to_geo B).
Local Notation "'E'" := (geo_to_ext B).
Local Notation "'G'" := (ext_to_geo B).

Let EP := ext_plus V.
Let EZ := ext_zero V.
Let EN := ext_neg V.
Let EPA := ext_plus_assoc V.
Let EPC := ext_plus_comm V.
Let EPZ := ext_plus_lid V.
Let EPN := ext_plus_linv V.
Let EM := ext_mult V.
Let EO := ext_one V.
Let EL := ext_ldist V.
Let ER := ext_rdist V.
Let EML := ext_mult_lid V.
Let EMR := ext_mult_rid V.
Let EMA := ext_mult_assoc V.
Let ES := ext_scalar V.
Let ESO := ext_scalar_id V.
Let ESL := ext_scalar_ldist V.
Let ESR := ext_scalar_rdist V.
Let ESC := ext_scalar_comp V.
Let ESML := ext_scalar_lmult V.
Let ESMR := ext_scalar_rmult V.
Let EG := exterior_grade V.
Let EGA := exterior_grade_mult V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO EL ER EML EMR EMA ES ESO ESL
    ESR ESC ESML ESMR EG EGA.

Local Open Scope geo_scope.
Local Open Scope nat_scope.

Theorem geo_mult_inner_involute : ∀ a (X : geo B),
        (geo_mult_inner B a X)∗ = -geo_mult_inner B a (X∗).
    intros a X.
    pose proof (geo_sum B X) as [l l_eq]; subst X.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite geo_involute_zero.
        do 2 rewrite geo_mult_inner_rzero.
        rewrite neg_zero, geo_involute_zero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite geo_involute_plus.
    do 2 rewrite geo_mult_inner_rplus.
    rewrite geo_involute_plus.
    rewrite IHl; clear IHl.
    rewrite neg_plus.
    apply rplus; clear l.
    rewrite geo_involute_scalar.
    do 2 rewrite geo_mult_inner_rscalar.
    rewrite geo_involute_scalar.
    rewrite <- scalar_rneg.
    apply lscalar; clear α.
    induction x as [|v l].
    {
        cbn.
        rewrite geo_involute_one.
        do 2 rewrite <- scalar_to_geo_one.
        rewrite geo_mult_inner_scalar.
        rewrite neg_zero, geo_involute_zero.
        reflexivity.
    }
    cbn.
    rewrite geo_involute_mult.
    rewrite geo_involute_vector.
    rewrite mult_lneg.
    rewrite geo_mult_inner_rneg.
    rewrite neg_neg.
    do 2 rewrite geo_mult_inner_add.
    rewrite geo_involute_plus.
    rewrite geo_involute_neg.
    rewrite geo_involute_mult.
    rewrite IHl; clear IHl.
    rewrite geo_involute_vector.
    rewrite mult_lneg, mult_rneg.
    rewrite neg_neg.
    rewrite geo_involute_scalar.
    reflexivity.
Qed.

Theorem ext_to_geo_involute : ∀ X, (G X)∗ = G (ext_involute X).
    intros X.
    pose proof (ext_sum V X) as [l l_eq]; subst X.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ext_involute_zero.
        do 2 rewrite ext_to_geo_zero.
        apply geo_involute_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_involute_plus.
    do 2 rewrite ext_to_geo_plus.
    rewrite geo_involute_plus.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite ext_involute_scalar.
    do 2 rewrite ext_to_geo_scalar.
    rewrite geo_involute_scalar.
    apply lscalar; clear α.
    induction x as [|v l].
    {
        cbn.
        rewrite ext_involute_one.
        do 2 rewrite ext_to_geo_one.
        apply geo_involute_one.
    }
    cbn.
    rewrite ext_involute_mult.
    rewrite ext_involute_vector.
    rewrite mult_lneg.
    rewrite ext_to_geo_neg.
    do 2 rewrite ext_to_geo_add.
    rewrite geo_involute_plus.
    rewrite geo_involute_neg.
    rewrite geo_mult_inner_involute.
    rewrite neg_neg.
    rewrite geo_involute_mult.
    rewrite IHl; clear IHl.
    rewrite geo_involute_vector.
    rewrite neg_plus.
    rewrite neg_neg.
    rewrite mult_lneg.
    reflexivity.
Qed.

Theorem geo_to_ext_involute : ∀ X : geo B, ext_involute (E X) = E (X∗).
    intros X.
    rewrite <- (geo_to_ext_to_geo B (ext_involute (E X))).
    rewrite <- ext_to_geo_involute.
    rewrite ext_to_geo_to_ext.
    reflexivity.
Qed.

End GeometricInvolutions.
