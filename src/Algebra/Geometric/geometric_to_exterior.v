Require Import init.

Require Import set.
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

(* begin hide *)
Section GeometricToExterior.

(* end hide *)
Context {F : CRingObj} {V : ModuleObj F}.
(* begin hide *)

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

(* end hide *)
Context (B : set_type bilinear_form).

(* begin hide *)
Let EP := ext_plus V.
Let EZ := ext_zero V.
Let EN := ext_neg V.
Let EPA := ext_plus_assoc V.
Let EPC := ext_plus_comm V.
Let EPZ := ext_plus_lid V.
Let EPN := ext_plus_linv V.
Let EM := ext_mult V.
Let EO := ext_one V.
Let EMA := ext_mult_assoc V.
Let EML := ext_mult_lid V.
Let EMR := ext_mult_rid V.
Let ES := ext_scalar V.
Let ESO := ext_scalar_id V.
Let ESL := ext_scalar_ldist V.
Let ESR := ext_scalar_rdist V.
Let ESC := ext_scalar_comp V.
Let EL := ext_ldist V.
Let ER := ext_rdist V.
Let ESML := ext_scalar_lmult V.
Let ESMR := ext_scalar_rmult V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO EMA EML EMR ES ESO ESL ESR ESC
    EL ER ESML ESMR.

Let E12 := direct_sum (algebra_module (exterior_algebra V))
                       (algebra_module (exterior_algebra V)).
Let E12P := module_plus E12.
Let E12S := module_scalar E12.

Existing Instances E12P E12S.

Definition ext_inner_base1 (a : module_V V) (v : module_V V) (p : module_V E12)
    := (
        vector_to_ext V v * fst p,
        -vector_to_ext V v * snd p + [B|] a v · (fst p)
    ) : module_V E12.

Lemma ext_inner_base_plus : ∀ a v p1 p2, ext_inner_base1 a v (p1 + p2) =
    ext_inner_base1 a v p1 + ext_inner_base1 a v p2.
Proof.
    intros a v [p11 p12] [p21 p22]; cbn.
    unfold ext_inner_base1; cbn.
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

Lemma ext_inner_base_scalar : ∀ a v b p, ext_inner_base1 a v (b · p) =
    b · ext_inner_base1 a v p.
Proof.
    intros a v b [p1 p2].
    unfold ext_inner_base1; cbn.
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

Definition ext_inner_base2 (a : module_V V) (v : module_V V) :=
    make_module_homomorphism F E12 E12
    (ext_inner_base1 a v)
    (ext_inner_base_plus a v)
    (ext_inner_base_scalar a v).

Let E3 := linear_trans_algebra E12.
Let E3P := algebra_plus E3.
Let E3Z := algebra_zero E3.
Let E3S := algebra_scalar E3.
Let E3M := algebra_mult E3.

Existing Instances E3P E3Z E3S E3M.

Lemma ext_inner_base2_plus : ∀ a v1 v2, ext_inner_base2 a (v1 + v2) =
    ext_inner_base2 a v1 + ext_inner_base2 a v2.
Proof.
    intros a v1 v2.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold plus at 2; cbn.
    unfold ext_inner_base2, linear_trans_plus_base; cbn.
    unfold ext_inner_base1; cbn.
    unfold plus at 5; cbn.
    apply f_equal2.
    -   rewrite (vector_to_ext_plus V).
        apply rdist.
    -   rewrite (vector_to_ext_plus V).
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

Lemma ext_inner_base2_scalar : ∀ a b v,
    ext_inner_base2 a (b · v) = b · ext_inner_base2 a v.
Proof.
    intros a b v.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold scalar_mult at 2; cbn.
    unfold linear_trans_scalar_base; cbn.
    unfold ext_inner_base1; cbn.
    unfold scalar_mult at 5; cbn.
    apply f_equal2.
    -   rewrite (vector_to_ext_scalar V).
        apply scalar_lmult.
    -   rewrite (vector_to_ext_scalar V).
        rewrite bilinear_form_rscalar.
        rewrite <- scalar_comp.
        rewrite scalar_ldist.
        do 2 rewrite mult_lneg.
        rewrite scalar_rneg.
        rewrite scalar_lmult.
        reflexivity.
Qed.

Lemma ext_inner_base_alternating : ∀ a v,
    0 = ext_inner_base2 a v * ext_inner_base2 a v.
Proof.
    intros a v.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold mult, zero; cbn.
    unfold linear_trans_zero_base, ext_inner_base1; cbn.
    unfold zero; cbn.
    apply f_equal2.
    -   rewrite mult_assoc.
        rewrite <- (ext_alternating V).
        rewrite mult_lanni.
        reflexivity.
    -   rewrite ldist.
        rewrite mult_assoc.
        rewrite mult_lneg, mult_rneg.
        rewrite <- (ext_alternating V).
        rewrite neg_neg, mult_lanni, plus_lid.
        rewrite <- scalar_rmult.
        rewrite <- rdist.
        rewrite plus_linv.
        rewrite mult_lanni.
        reflexivity.
Qed.

Definition ext_inner_base3 a := make_module_homomorphism
    F
    V
    (algebra_module E3)
    (ext_inner_base2 a)
    (ext_inner_base2_plus a)
    (ext_inner_base2_scalar a).

Definition ext_inner_base4 a := make_to_ext
    V
    E3
    (ext_inner_base3 a)
    (ext_inner_base_alternating a).

Definition ext_inner_base a
    := ex_singleton (exterior_universal V (ext_inner_base4 a)).

Definition ext_inner_f_homo a := [ext_inner_base a|].
Definition ext_inner_f a := algebra_homo_f (ext_inner_f_homo a).

Theorem ext_inner_f_eq : ∀ a v,
    ext_inner_f a (vector_to_ext V v) = ext_inner_base2 a v.
Proof.
    intros a.
    apply [|ext_inner_base a].
Qed.

Theorem ext_inner_f_mult : ∀ a u v,
    ext_inner_f a (u * v) = ext_inner_f a u * ext_inner_f a v.
Proof.
    intros a u v.
    apply algebra_homo_mult.
Qed.

Definition ext_inner a v := snd (module_homo_f (ext_inner_f a v) (1, 0)).

(* end hide *)
Theorem ext_inner_rplus :
    ∀ a u v, ext_inner a (u + v) = ext_inner a u + ext_inner a v.
Proof.
    intros a u v.
    unfold ext_inner.
    unfold ext_inner_f.
    rewrite algebra_homo_plus.
    unfold plus at 1; cbn.
    unfold linear_trans_plus_base.
    unfold plus at 1; cbn.
    reflexivity.
Qed.

Theorem ext_inner_rscalar : ∀ a α v, ext_inner a (α · v) = α · ext_inner a v.
Proof.
    intros a α v.
    unfold ext_inner.
    unfold ext_inner_f.
    rewrite algebra_homo_scalar.
    unfold scalar_mult at 1; cbn.
    unfold linear_trans_scalar_base.
    unfold scalar_mult at 1; cbn.
    reflexivity.
Qed.

Theorem ext_inner_rzero : ∀ a, ext_inner a 0 = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0).
    rewrite ext_inner_rscalar.
    apply scalar_lanni.
Qed.

Theorem ext_inner_rneg : ∀ a v, ext_inner a (-v) = -ext_inner a v.
Proof.
    intros a v.
    rewrite <- scalar_neg_one.
    rewrite ext_inner_rscalar.
    apply scalar_neg_one.
Qed.

Theorem ext_inner_add : ∀ a v x,
    ext_inner a (vector_to_ext V v * x) =
    [B|] a v · x - vector_to_ext V v * ext_inner a x.
Proof.
    intros a v x.
    pose proof (ext_sum V x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_ranni.
        rewrite ext_inner_rzero.
        rewrite mult_ranni.
        rewrite scalar_ranni.
        rewrite neg_zero, plus_rid.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ldist.
    rewrite scalar_rmult.
    rewrite ext_inner_rplus.
    rewrite IHl; clear IHl.
    rewrite ext_inner_rplus.
    rewrite ldist.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite scalar_ldist.
    rewrite <- plus_assoc.
    rewrite (plus_comm _ (-(vector_to_ext V v * _))).
    rewrite plus_assoc.
    apply rplus.
    clear l.
    do 2 rewrite ext_inner_rscalar.
    rewrite scalar_rmult.
    rewrite scalar_comp.
    rewrite (mult_comm _ α).
    rewrite <- scalar_comp.
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    apply f_equal.
    unfold ext_inner.
    rewrite ext_inner_f_mult.
    rewrite ext_inner_f_eq.
    unfold mult at 1; cbn.
    rewrite plus_comm.
    rewrite mult_lneg.
    apply rplus.
    induction x as [|x l].
    {
        cbn.
        unfold ext_inner_f.
        rewrite algebra_homo_one.
        unfold one at 1; cbn.
        reflexivity.
    }
    cbn.
    rewrite ext_inner_f_mult.
    unfold mult at 1; cbn.
    unfold linear_trans_mult_base.
    rewrite ext_inner_f_eq.
    cbn.
    rewrite <- scalar_rmult.
    rewrite IHl; clear IHl.
    rewrite scalar_rmult.
    reflexivity.
Qed.

Theorem ext_inner_scalar : ∀ a α, ext_inner a (scalar_to_ext V α) = 0.
Proof.
    intros a α.
    unfold ext_inner.
    unfold ext_inner_f.
    rewrite scalar_to_ext_one_scalar.
    rewrite algebra_homo_scalar.
    rewrite algebra_homo_one.
    unfold scalar_mult; cbn.
    unfold linear_trans_scalar_base.
    unfold one at 1; cbn.
    unfold scalar_mult; cbn.
    rewrite scalar_ranni.
    reflexivity.
Qed.

Theorem ext_inner_vector : ∀ a v,
    ext_inner a (vector_to_ext V v) = [B|] a v · 1.
Proof.
    intros a v.
    rewrite <- (mult_rid (vector_to_ext V v)).
    rewrite ext_inner_add.
    unfold EO.
    rewrite <- scalar_to_ext_one at 2.
    rewrite ext_inner_scalar.
    rewrite mult_ranni.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem ext_inner_bivector : ∀ a u v,
    ext_inner a (vector_to_ext V u * vector_to_ext V v) =
    [B|] a u · vector_to_ext V v -
    [B|] a v · vector_to_ext V u.
Proof.
    intros a u v.
    rewrite ext_inner_add.
    rewrite ext_inner_vector.
    rewrite scalar_rmult.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem ext_inner_lplus :
    ∀ a b v, ext_inner (a + b) v = ext_inner a v + ext_inner b v.
Proof.
    intros a b v.
    pose proof (ext_sum V v) as [l l_eq]; subst v.
    induction l as [|[α v] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite ext_inner_rzero.
        rewrite plus_rid.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 3 rewrite ext_inner_rplus.
    rewrite IHl; clear IHl.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite <- plus_assoc.
    rewrite (plus_comm (ext_inner a (ulist_sum _))).
    rewrite plus_assoc.
    apply rplus; clear l.
    do 3 rewrite ext_inner_rscalar.
    rewrite <- scalar_ldist.
    apply f_equal.
    induction v as [|v l].
    {
        rewrite list_image_end; cbn.
        rewrite <- scalar_to_ext_one.
        do 3 rewrite ext_inner_scalar.
        rewrite plus_rid.
        reflexivity.
    }
    rewrite list_image_add; cbn.
    do 3 rewrite ext_inner_add.
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

Theorem ext_inner_lscalar : ∀ α a v, ext_inner (α · a) v = α · ext_inner a v.
Proof.
    intros α a v.
    pose proof (ext_sum V v) as [l l_eq]; subst v.
    induction l as [|[β v] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite ext_inner_rzero.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite ext_inner_rplus.
    rewrite IHl; clear IHl.
    rewrite scalar_ldist.
    apply rplus; clear l.
    do 2 rewrite ext_inner_rscalar.
    rewrite scalar_comp.
    rewrite mult_comm.
    rewrite <- scalar_comp.
    apply f_equal; clear β.
    induction v as [|v l].
    {
        rewrite list_image_end; cbn.
        rewrite <- scalar_to_ext_one.
        do 2 rewrite ext_inner_scalar.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite list_image_add; cbn.
    do 2 rewrite ext_inner_add.
    rewrite IHl; clear IHl.
    rewrite bilinear_form_lscalar.
    rewrite scalar_ldist.
    rewrite scalar_comp.
    rewrite scalar_rneg.
    rewrite scalar_rmult.
    reflexivity.
Qed.

(* begin hide *)
Definition ext_inner_homo a := make_module_homomorphism
    F
    (algebra_module (exterior_algebra V))
    (algebra_module (exterior_algebra V))
    (ext_inner a)
    (ext_inner_rplus a)
    (ext_inner_rscalar a).

Definition ext_outer_homo a := make_module_homomorphism
    F
    (algebra_module (exterior_algebra V))
    (algebra_module (exterior_algebra V))
    (mult (vector_to_ext V a))
    (ldist (vector_to_ext V a))
    (λ α v, scalar_rmult α (vector_to_ext V a) v).

Let EE := linear_trans_algebra (algebra_module (exterior_algebra V)).
Let EEP := algebra_plus EE.
Let EEZ := algebra_zero EE.
Let EEPC := algebra_plus_comm EE.
Let EEPZ := algebra_plus_lid EE.
Let EEM := algebra_mult EE.
Let EEO := algebra_one EE.
Let EEL := algebra_ldist EE.
Let EER := algebra_rdist EE.
Let EES := algebra_scalar EE.
Let EESL := algebra_scalar_ldist EE.

Existing Instances EEP EEZ EEPC EEPZ EEM EEO EEL EER EES EESL.

Theorem ext_inner_alternating : ∀ a, ext_inner_homo a * ext_inner_homo a = 0.
Proof.
    intros a.
    apply module_homomorphism_eq.
    intros x.
    unfold mult at 1; cbn.
    unfold zero at 1; cbn.
    unfold linear_trans_zero_base.
    pose proof (ext_sum V x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite ext_inner_rzero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite ext_inner_rplus.
    rewrite IHl; clear IHl l.
    rewrite plus_rid.
    do 2 rewrite ext_inner_rscalar.
    rewrite <- (scalar_ranni α).
    apply f_equal.
    induction x as [|v l].
    {
        rewrite list_image_end; cbn.
        rewrite <- scalar_to_ext_one.
        rewrite ext_inner_scalar.
        apply ext_inner_rzero.
    }
    rewrite list_image_add; cbn.
    rewrite ext_inner_add.
    rewrite ext_inner_rplus.
    rewrite ext_inner_rneg.
    rewrite ext_inner_add.
    rewrite IHl.
    rewrite mult_ranni.
    rewrite neg_zero, plus_rid.
    rewrite ext_inner_rscalar.
    rewrite plus_rinv.
    reflexivity.
Qed.

Theorem ext_outer_alternating : ∀ a, ext_outer_homo a * ext_outer_homo a = 0.
Proof.
    intros a.
    apply module_homomorphism_eq.
    intros x.
    unfold mult at 1; cbn.
    unfold zero at 1; cbn.
    unfold linear_trans_zero_base.
    rewrite mult_assoc.
    rewrite <- (ext_alternating V).
    apply mult_lanni.
Qed.

Definition geo_to_ext_base1 a := ext_inner_homo a + ext_outer_homo a.

Lemma geo_to_ext_base1_plus : ∀ u v,
    geo_to_ext_base1 (u + v) = geo_to_ext_base1 u + geo_to_ext_base1 v.
Proof.
    intros u v.
    unfold geo_to_ext_base1.
    apply module_homomorphism_eq.
    intros x.
    unfold plus at 1 4 5 6; cbn.
    unfold linear_trans_plus_base; cbn.
    rewrite ext_inner_lplus.
    rewrite (vector_to_ext_plus V).
    rewrite rdist.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply plus_comm.
Qed.

Lemma geo_to_ext_base1_scalar : ∀ a v,
    geo_to_ext_base1 (a · v) = a · geo_to_ext_base1 v.
Proof.
    intros a v.
    unfold geo_to_ext_base1.
    apply module_homomorphism_eq.
    intros x.
    rewrite scalar_ldist.
    unfold scalar_mult at 3 4, plus at 1 2; cbn.
    unfold linear_trans_plus_base, linear_trans_scalar_base; cbn.
    rewrite ext_inner_lscalar.
    rewrite (vector_to_ext_scalar V).
    rewrite scalar_lmult.
    reflexivity.
Qed.

Lemma geo_to_ext_base_contract : ∀ v,
    geo_to_ext_base1 v * geo_to_ext_base1 v = [B|] v v · 1.
Proof.
    intros v.
    unfold geo_to_ext_base1.
    rewrite ldist.
    do 2 rewrite rdist.
    rewrite ext_inner_alternating, ext_outer_alternating.
    rewrite plus_lid, plus_rid.
    apply module_homomorphism_eq.
    intros x.
    unfold mult at 1 2, plus at 1; cbn.
    unfold linear_trans_plus_base; cbn.
    unfold scalar_mult at 1; cbn.
    unfold linear_trans_scalar_base.
    unfold one at 1; cbn.
    rewrite ext_inner_add.
    rewrite plus_comm.
    apply plus_rlinv.
Qed.

Definition geo_to_ext_base2 := make_module_homomorphism
    F
    V
    (algebra_module EE)
    geo_to_ext_base1
    geo_to_ext_base1_plus
    geo_to_ext_base1_scalar.

Definition geo_to_ext_base3 := make_to_geo
    B EE geo_to_ext_base2 geo_to_ext_base_contract.

Definition geo_to_ext_base :=
    ex_singleton (geometric_universal B geo_to_ext_base3).
Definition geo_to_ext_f_homo := [geo_to_ext_base|].
Definition geo_to_ext_f := algebra_homo_f geo_to_ext_f_homo.

Let GP := geo_plus B.
Let GZ := geo_zero B.
Let GN := geo_neg B.
Let GPA := geo_plus_assoc B.
Let GPC := geo_plus_comm B.
Let GPZ := geo_plus_lid B.
Let GPN := geo_plus_linv B.
Let GM := geo_mult B.
Let GO := geo_one B.
Let GMR := geo_mult_rid B.
Let GS := geo_scalar B.
Let GSO := geo_scalar_id B.
Let GSR := geo_scalar_rdist B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GMR GS GSO GSR.

Theorem geo_to_ext_f_eq :
    ∀ v, geo_to_ext_f (vector_to_geo B v) = geo_to_ext_base1 v.
Proof.
    apply [|geo_to_ext_base].
Qed.

Theorem geo_to_ext_f_mult :
    ∀ u v, geo_to_ext_f (u * v) = geo_to_ext_f u * geo_to_ext_f v.
Proof.
    apply algebra_homo_mult.
Qed.

Definition geo_to_ext (v : geo B) := module_homo_f (geo_to_ext_f v) 1 : ext V.

(* end hide *)
Theorem geo_to_ext_plus : ∀ u v,
    geo_to_ext (u + v) = geo_to_ext u + geo_to_ext v.
Proof.
    intros u v.
    unfold geo_to_ext.
    unfold geo_to_ext_f.
    rewrite algebra_homo_plus.
    unfold plus at 1; cbn.
    unfold linear_trans_plus_base.
    reflexivity.
Qed.

Theorem geo_to_ext_scalar : ∀ a v, geo_to_ext (a · v) = a · geo_to_ext v.
Proof.
    intros a v.
    unfold geo_to_ext.
    unfold geo_to_ext_f.
    rewrite algebra_homo_scalar.
    unfold scalar_mult at 1; cbn.
    unfold linear_trans_scalar_base.
    reflexivity.
Qed.

Theorem geo_to_ext_add : ∀ v x, geo_to_ext (vector_to_geo B v * x) =
    ext_inner v (geo_to_ext x) + vector_to_ext V v * geo_to_ext x.
Proof.
    intros v x.
    unfold geo_to_ext.
    rewrite geo_to_ext_f_mult.
    rewrite geo_to_ext_f_eq.
    unfold mult at 1; cbn.
    unfold linear_trans_mult_base; cbn.
    unfold geo_to_ext_base1; cbn.
    unfold plus at 1; cbn.
    unfold linear_trans_plus_base; cbn.
    reflexivity.
Qed.

Theorem geo_to_ext_neg : ∀ x, geo_to_ext (-x) = -geo_to_ext x.
Proof.
    intros x.
    rewrite <- scalar_neg_one.
    rewrite geo_to_ext_scalar.
    apply scalar_neg_one.
Qed.

Theorem geo_to_ext_zero : geo_to_ext 0 = 0.
Proof.
    rewrite <- (scalar_lanni 0).
    rewrite geo_to_ext_scalar.
    apply scalar_lanni.
Qed.

Theorem geo_to_ext_one : geo_to_ext 1 = 1.
Proof.
    unfold geo_to_ext.
    unfold geo_to_ext_f.
    rewrite algebra_homo_one.
    unfold one at 1; cbn.
    reflexivity.
Qed.

Theorem geo_to_ext_of_scalar : ∀ α,
    geo_to_ext (scalar_to_geo B α) = scalar_to_ext V α.
Proof.
    intros α.
    rewrite scalar_to_geo_one_scalar.
    rewrite geo_to_ext_scalar.
    change 1 with (one (U := geo B)).
    rewrite geo_to_ext_one.
    symmetry; apply scalar_to_ext_one_scalar.
Qed.

Theorem geo_to_ext_vector : ∀ v,
    geo_to_ext (vector_to_geo B v) = vector_to_ext V v.
Proof.
    intros v.
    rewrite <- (mult_rid (vector_to_geo B v)).
    rewrite geo_to_ext_add.
    change 1 with (one (U := geo B)).
    rewrite geo_to_ext_one.
    rewrite mult_rid.
    replace 1 with (scalar_to_ext V 1) by apply scalar_to_ext_one.
    rewrite ext_inner_scalar.
    apply plus_lid.
Qed.

Theorem geo_to_ext_vector2 : ∀ u v,
    geo_to_ext (vector_to_geo B u * vector_to_geo B v) =
    [B|] u v · 1 + vector_to_ext V u * vector_to_ext V v.
Proof.
    intros u v.
    rewrite geo_to_ext_add.
    rewrite geo_to_ext_vector.
    rewrite ext_inner_vector.
    reflexivity.
Qed.
(* begin hide *)

End GeometricToExterior.
(* end hide *)
