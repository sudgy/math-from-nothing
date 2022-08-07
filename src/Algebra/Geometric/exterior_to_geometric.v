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

(* begin hide *)
Section ExteriorToGeometric.

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
Let GP := geo_plus B.
Let GZ := geo_zero B.
Let GN := geo_neg B.
Let GPA := geo_plus_assoc B.
Let GPC := geo_plus_comm B.
Let GPZ := geo_plus_lid B.
Let GPN := geo_plus_linv B.
Let GM := geo_mult B.
Let GO := geo_one B.
Let GMA := geo_mult_assoc B.
Let GML := geo_mult_lid B.
Let GMR := geo_mult_rid B.
Let GS := geo_scalar B.
Let GSO := geo_scalar_id B.
Let GSL := geo_scalar_ldist B.
Let GSR := geo_scalar_rdist B.
Let GSC := geo_scalar_comp B.
Let GL := geo_ldist B.
Let GR := geo_rdist B.
Let GSML := geo_scalar_lmult B.
Let GSMR := geo_scalar_rmult B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GMA GML GMR GS GSO GSL GSR GSC
    GL GR GSML GSMR.

Let G12 := direct_sum (algebra_module (geometric_algebra B))
                       (algebra_module (geometric_algebra B)).
Let G12P := module_plus G12.
Let G12S := module_scalar G12.

Existing Instances G12P G12S.

Definition geo_mult_inner_base1 (a : module_V V) (v : module_V V) (p : module_V G12)
    := (
        vector_to_geo B v * fst p,
        -vector_to_geo B v * snd p + [B|] a v · (fst p)
    ) : module_V G12.

Lemma geo_mult_inner_base_plus : ∀ a v p1 p2, geo_mult_inner_base1 a v (p1 + p2) =
    geo_mult_inner_base1 a v p1 + geo_mult_inner_base1 a v p2.
Proof.
    intros a v [p11 p12] [p21 p22]; cbn.
    unfold geo_mult_inner_base1; cbn.
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

Lemma geo_mult_inner_base_scalar : ∀ a v b p, geo_mult_inner_base1 a v (b · p) =
    b · geo_mult_inner_base1 a v p.
Proof.
    intros a v b [p1 p2].
    unfold geo_mult_inner_base1; cbn.
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

Definition geo_mult_inner_base2 (a : module_V V) (v : module_V V) :=
    make_module_homomorphism F G12 G12
    (geo_mult_inner_base1 a v)
    (geo_mult_inner_base_plus a v)
    (geo_mult_inner_base_scalar a v).

Let G3 := linear_trans_algebra G12.
Let G3P := algebra_plus G3.
Let G3S := algebra_scalar G3.
Let G3M := algebra_mult G3.
Let G3O := algebra_one G3.

Existing Instances G3P G3S G3M G3O.

Lemma geo_mult_inner_base2_plus : ∀ a v1 v2, geo_mult_inner_base2 a (v1 + v2) =
    geo_mult_inner_base2 a v1 + geo_mult_inner_base2 a v2.
Proof.
    intros a v1 v2.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold plus at 2; cbn.
    unfold geo_mult_inner_base2, linear_trans_plus_base; cbn.
    unfold geo_mult_inner_base1; cbn.
    unfold plus at 5; cbn.
    apply f_equal2.
    -   rewrite (vector_to_geo_plus B).
        apply rdist.
    -   rewrite (vector_to_geo_plus B).
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

Lemma geo_mult_inner_base2_scalar : ∀ a b v,
    geo_mult_inner_base2 a (b · v) = b · geo_mult_inner_base2 a v.
Proof.
    intros a b v.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold scalar_mult at 2; cbn.
    unfold linear_trans_scalar_base; cbn.
    unfold geo_mult_inner_base1; cbn.
    unfold scalar_mult at 5; cbn.
    apply f_equal2.
    -   rewrite (vector_to_geo_scalar B).
        apply scalar_lmult.
    -   rewrite (vector_to_geo_scalar B).
        rewrite bilinear_form_rscalar.
        rewrite <- scalar_comp.
        rewrite scalar_ldist.
        do 2 rewrite mult_lneg.
        rewrite scalar_rneg.
        rewrite scalar_lmult.
        reflexivity.
Qed.

Lemma geo_mult_inner_base_contract : ∀ a v,
    geo_mult_inner_base2 a v * geo_mult_inner_base2 a v = [B|] v v · 1.
Proof.
    intros a v.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold mult, scalar_mult, one; cbn.
    unfold linear_trans_scalar_base, geo_mult_inner_base1; cbn.
    unfold scalar_mult at 3; cbn.
    apply f_equal2.
    -   rewrite mult_assoc.
        rewrite (geo_contract B).
        rewrite scalar_lmult.
        rewrite mult_lid.
        reflexivity.
    -   rewrite ldist.
        rewrite mult_assoc.
        rewrite mult_lneg, mult_rneg.
        rewrite (geo_contract B).
        rewrite neg_neg.
        rewrite <- scalar_rmult.
        rewrite mult_lneg.
        rewrite plus_rlinv.
        rewrite scalar_lmult.
        rewrite mult_lid.
        reflexivity.
Qed.

Definition geo_mult_inner_base3 a := make_module_homomorphism
    F
    V
    (algebra_module G3)
    (geo_mult_inner_base2 a)
    (geo_mult_inner_base2_plus a)
    (geo_mult_inner_base2_scalar a).

Definition geo_mult_inner_base4 a := make_to_geo
    B
    G3
    (geo_mult_inner_base3 a)
    (geo_mult_inner_base_contract a).

Definition geo_mult_inner_base a
    := card_one_ex (geometric_universal B (geo_mult_inner_base4 a)).

Definition geo_mult_inner_f_homo a := [geo_mult_inner_base a|].
Definition geo_mult_inner_f a := algebra_homo_f (geo_mult_inner_f_homo a).

Theorem geo_mult_inner_f_eq : ∀ a v,
    geo_mult_inner_f a (vector_to_geo B v) = geo_mult_inner_base2 a v.
Proof.
    intros a.
    apply [|geo_mult_inner_base a].
Qed.

Theorem geo_mult_inner_f_mult : ∀ a u v,
    geo_mult_inner_f a (u * v) = geo_mult_inner_f a u * geo_mult_inner_f a v.
Proof.
    intros a u v.
    apply algebra_homo_mult.
Qed.

Definition geo_mult_inner a v := snd (module_homo_f (geo_mult_inner_f a v) (1, 0)).

(* end hide *)
Theorem geo_mult_inner_rplus : ∀ a u v,
    geo_mult_inner a (u + v) = geo_mult_inner a u + geo_mult_inner a v.
Proof.
    intros a u v.
    unfold geo_mult_inner.
    unfold geo_mult_inner_f.
    rewrite algebra_homo_plus.
    unfold plus at 1; cbn.
    unfold linear_trans_plus_base.
    unfold plus at 1; cbn.
    reflexivity.
Qed.

Theorem geo_mult_inner_rscalar : ∀ a α v,
    geo_mult_inner a (α · v) = α · geo_mult_inner a v.
Proof.
    intros a α v.
    unfold geo_mult_inner.
    unfold geo_mult_inner_f.
    rewrite algebra_homo_scalar.
    unfold scalar_mult at 1; cbn.
    unfold linear_trans_scalar_base.
    unfold scalar_mult at 1; cbn.
    reflexivity.
Qed.

Theorem geo_mult_inner_rzero : ∀ a, geo_mult_inner a 0 = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0).
    rewrite geo_mult_inner_rscalar.
    apply scalar_lanni.
Qed.

Theorem geo_mult_inner_rneg : ∀ a v, geo_mult_inner a (-v) = -geo_mult_inner a v.
Proof.
    intros a v.
    rewrite <- scalar_neg_one.
    rewrite geo_mult_inner_rscalar.
    apply scalar_neg_one.
Qed.

Theorem geo_mult_inner_add : ∀ a v x,
    geo_mult_inner a (vector_to_geo B v * x) =
    [B|] a v · x - vector_to_geo B v * geo_mult_inner a x.
Proof.
    intros a v x.
    pose proof (geo_sum B x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_ranni.
        rewrite geo_mult_inner_rzero.
        rewrite mult_ranni.
        rewrite scalar_ranni.
        rewrite neg_zero, plus_rid.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ldist.
    rewrite scalar_rmult.
    rewrite geo_mult_inner_rplus.
    rewrite IHl; clear IHl.
    rewrite geo_mult_inner_rplus.
    rewrite ldist.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite scalar_ldist.
    rewrite <- plus_assoc.
    rewrite (plus_comm _ (-(vector_to_geo B v * _))).
    rewrite plus_assoc.
    apply rplus.
    clear l.
    do 2 rewrite geo_mult_inner_rscalar.
    rewrite scalar_rmult.
    rewrite scalar_comp.
    rewrite (mult_comm _ α).
    rewrite <- scalar_comp.
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    apply f_equal.
    unfold geo_mult_inner.
    rewrite geo_mult_inner_f_mult.
    rewrite geo_mult_inner_f_eq.
    unfold mult at 1; cbn.
    rewrite plus_comm.
    rewrite mult_lneg.
    apply rplus.
    induction x as [|x l].
    {
        cbn.
        unfold geo_mult_inner_f.
        rewrite algebra_homo_one.
        unfold one at 1; cbn.
        reflexivity.
    }
    cbn.
    rewrite geo_mult_inner_f_mult.
    unfold mult at 1; cbn.
    unfold linear_trans_mult_base.
    rewrite geo_mult_inner_f_eq.
    cbn.
    rewrite <- scalar_rmult.
    rewrite IHl; clear IHl.
    rewrite scalar_rmult.
    reflexivity.
Qed.

Theorem geo_mult_inner_scalar : ∀ a α, geo_mult_inner a (scalar_to_geo B α) = 0.
Proof.
    intros a α.
    unfold geo_mult_inner.
    unfold geo_mult_inner_f.
    rewrite scalar_to_geo_one_scalar.
    rewrite algebra_homo_scalar.
    rewrite algebra_homo_one.
    unfold scalar_mult; cbn.
    unfold linear_trans_scalar_base.
    unfold one at 1; cbn.
    unfold scalar_mult; cbn.
    rewrite scalar_ranni.
    reflexivity.
Qed.

Theorem geo_mult_inner_vector : ∀ a v,
    geo_mult_inner a (vector_to_geo B v) = [B|] a v · 1.
Proof.
    intros a v.
    rewrite <- (mult_rid (vector_to_geo B v)).
    rewrite geo_mult_inner_add.
    unfold GO.
    rewrite <- scalar_to_geo_one at 2.
    rewrite geo_mult_inner_scalar.
    rewrite mult_ranni.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem geo_mult_inner_bivector : ∀ a u v,
    geo_mult_inner a (vector_to_geo B u * vector_to_geo B v) =
    [B|] a u · vector_to_geo B v -
    [B|] a v · vector_to_geo B u.
Proof.
    intros a u v.
    rewrite geo_mult_inner_add.
    rewrite geo_mult_inner_vector.
    rewrite scalar_rmult.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem geo_mult_inner_lplus : ∀ a b v,
    geo_mult_inner (a + b) v = geo_mult_inner a v + geo_mult_inner b v.
Proof.
    intros a b v.
    pose proof (geo_sum B v) as [l l_eq]; subst v.
    induction l as [|[α v] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite geo_mult_inner_rzero.
        rewrite plus_rid.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 3 rewrite geo_mult_inner_rplus.
    rewrite IHl; clear IHl.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite <- plus_assoc.
    rewrite (plus_comm (geo_mult_inner a (ulist_sum _))).
    rewrite plus_assoc.
    apply rplus; clear l.
    do 3 rewrite geo_mult_inner_rscalar.
    rewrite <- scalar_ldist.
    apply f_equal.
    induction v as [|v l].
    {
        cbn.
        rewrite <- scalar_to_geo_one.
        do 3 rewrite geo_mult_inner_scalar.
        rewrite plus_rid.
        reflexivity.
    }
    cbn.
    do 3 rewrite geo_mult_inner_add.
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

Theorem geo_mult_inner_lscalar : ∀ α a v,
    geo_mult_inner (α · a) v = α · geo_mult_inner a v.
Proof.
    intros α a v.
    pose proof (geo_sum B v) as [l l_eq]; subst v.
    induction l as [|[β v] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite geo_mult_inner_rzero.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite geo_mult_inner_rplus.
    rewrite IHl; clear IHl.
    rewrite scalar_ldist.
    apply rplus; clear l.
    do 2 rewrite geo_mult_inner_rscalar.
    rewrite scalar_comp.
    rewrite mult_comm.
    rewrite <- scalar_comp.
    apply f_equal; clear β.
    induction v as [|v l].
    {
        cbn.
        rewrite <- scalar_to_geo_one.
        do 2 rewrite geo_mult_inner_scalar.
        rewrite scalar_ranni.
        reflexivity.
    }
    cbn.
    do 2 rewrite geo_mult_inner_add.
    rewrite IHl; clear IHl.
    rewrite bilinear_form_lscalar.
    rewrite scalar_ldist.
    rewrite scalar_comp.
    rewrite scalar_rneg.
    rewrite scalar_rmult.
    reflexivity.
Qed.

(* begin hide *)
Definition geo_mult_inner_homo a := make_module_homomorphism
    F
    (algebra_module (geometric_algebra B))
    (algebra_module (geometric_algebra B))
    (geo_mult_inner a)
    (geo_mult_inner_rplus a)
    (geo_mult_inner_rscalar a).

Definition geo_mult_homo a := make_module_homomorphism
    F
    (algebra_module (geometric_algebra B))
    (algebra_module (geometric_algebra B))
    (mult (vector_to_geo B a))
    (ldist (vector_to_geo B a))
    (λ α v, scalar_rmult α (vector_to_geo B a) v).

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

Theorem geo_mult_inner_alternating : ∀ a,
    geo_mult_inner_homo a * geo_mult_inner_homo a = 0.
Proof.
    intros a.
    apply module_homomorphism_eq.
    intros x.
    unfold mult at 1; cbn.
    unfold zero at 1; cbn.
    unfold linear_trans_zero_base.
    pose proof (geo_sum B x) as [l l_eq]; subst x.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite geo_mult_inner_rzero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite geo_mult_inner_rplus.
    rewrite IHl; clear IHl l.
    rewrite plus_rid.
    do 2 rewrite geo_mult_inner_rscalar.
    rewrite <- (scalar_ranni α).
    apply f_equal.
    induction x as [|v l].
    {
        cbn.
        rewrite <- scalar_to_geo_one.
        rewrite geo_mult_inner_scalar.
        apply geo_mult_inner_rzero.
    }
    cbn.
    rewrite geo_mult_inner_add.
    rewrite geo_mult_inner_rplus.
    rewrite geo_mult_inner_rneg.
    rewrite geo_mult_inner_add.
    rewrite IHl.
    rewrite mult_ranni.
    rewrite neg_zero, plus_rid.
    rewrite geo_mult_inner_rscalar.
    rewrite plus_rinv.
    reflexivity.
Qed.

Theorem geo_mult_contract : ∀ a, geo_mult_homo a * geo_mult_homo a = [B|] a a · 1.
Proof.
    intros a.
    apply module_homomorphism_eq.
    intros x.
    unfold mult at 1; cbn.
    unfold scalar_mult at 1, one at 1; cbn.
    unfold linear_trans_scalar_base; cbn.
    rewrite mult_assoc.
    rewrite (geo_contract B).
    rewrite scalar_lmult.
    rewrite mult_lid.
    reflexivity.
Qed.

Definition ext_to_geo_base1 a := -geo_mult_inner_homo a + geo_mult_homo a.

Lemma ext_to_geo_base1_plus : ∀ u v,
    ext_to_geo_base1 (u + v) = ext_to_geo_base1 u + ext_to_geo_base1 v.
Proof.
    intros u v.
    unfold ext_to_geo_base1.
    apply module_homomorphism_eq.
    intros x.
    unfold plus at 1 4 5 6; cbn.
    unfold linear_trans_plus_base; cbn.
    unfold neg at 1 2 3; cbn.
    unfold linear_trans_neg_base; cbn.
    rewrite geo_mult_inner_lplus.
    rewrite (vector_to_geo_plus B).
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
Proof.
    intros a v.
    unfold ext_to_geo_base1.
    apply module_homomorphism_eq.
    intros x.
    rewrite scalar_ldist.
    unfold scalar_mult at 3 4, plus at 1 2; cbn.
    unfold linear_trans_plus_base, linear_trans_scalar_base; cbn.
    unfold neg at 1 2; cbn.
    unfold linear_trans_neg_base; cbn.
    rewrite geo_mult_inner_lscalar.
    rewrite (vector_to_geo_scalar B).
    rewrite scalar_lmult.
    rewrite scalar_rneg.
    reflexivity.
Qed.

Lemma ext_to_geo_base_alternating : ∀ v,
    0 = ext_to_geo_base1 v * ext_to_geo_base1 v.
Proof.
    intros v.
    unfold ext_to_geo_base1.
    rewrite ldist.
    do 2 rewrite rdist.
    rewrite mult_lneg.
    rewrite mult_rneg.
    rewrite neg_neg.
    rewrite mult_lneg, mult_rneg.
    rewrite geo_mult_inner_alternating, geo_mult_contract.
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
    rewrite geo_mult_inner_add.
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
Proof.
    apply [|ext_to_geo_base].
Qed.

Theorem ext_to_geo_f_mult :
    ∀ u v, ext_to_geo_f (u * v) = ext_to_geo_f u * ext_to_geo_f v.
Proof.
    apply algebra_homo_mult.
Qed.

Definition ext_to_geo (v : ext V) := module_homo_f (ext_to_geo_f v) 1 : geo B.

(* end hide *)
Theorem ext_to_geo_plus : ∀ u v,
    ext_to_geo (u + v) = ext_to_geo u + ext_to_geo v.
Proof.
    intros u v.
    unfold ext_to_geo.
    unfold ext_to_geo_f.
    rewrite algebra_homo_plus.
    unfold plus at 1; cbn.
    unfold linear_trans_plus_base.
    reflexivity.
Qed.

Theorem ext_to_geo_scalar : ∀ a v, ext_to_geo (a · v) = a · ext_to_geo v.
Proof.
    intros a v.
    unfold ext_to_geo.
    unfold ext_to_geo_f.
    rewrite algebra_homo_scalar.
    unfold scalar_mult at 1; cbn.
    unfold linear_trans_scalar_base.
    reflexivity.
Qed.

Theorem ext_to_geo_add : ∀ v x, ext_to_geo (vector_to_ext V v * x) =
    -geo_mult_inner v (ext_to_geo x) + vector_to_geo B v * ext_to_geo x.
Proof.
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
Proof.
    intros x.
    rewrite <- scalar_neg_one.
    rewrite ext_to_geo_scalar.
    apply scalar_neg_one.
Qed.

Theorem ext_to_geo_zero : ext_to_geo 0 = 0.
Proof.
    rewrite <- (scalar_lanni 0).
    rewrite ext_to_geo_scalar.
    apply scalar_lanni.
Qed.

Theorem ext_to_geo_one : ext_to_geo 1 = 1.
Proof.
    unfold ext_to_geo.
    unfold ext_to_geo_f.
    rewrite algebra_homo_one.
    unfold one at 1; cbn.
    reflexivity.
Qed.

Theorem ext_to_geo_of_scalar : ∀ α,
    ext_to_geo (scalar_to_ext V α) = scalar_to_geo B α.
Proof.
    intros α.
    rewrite scalar_to_ext_one_scalar.
    rewrite ext_to_geo_scalar.
    change 1 with (one (U := ext V)).
    rewrite ext_to_geo_one.
    symmetry; apply scalar_to_geo_one_scalar.
Qed.

Theorem ext_to_geo_vector : ∀ v,
    ext_to_geo (vector_to_ext V v) = vector_to_geo B v.
Proof.
    intros v.
    rewrite <- (mult_rid (vector_to_ext V v)).
    rewrite ext_to_geo_add.
    change 1 with (one (U := ext V)).
    rewrite ext_to_geo_one.
    rewrite mult_rid.
    replace 1 with (scalar_to_geo B 1) by apply scalar_to_geo_one.
    rewrite geo_mult_inner_scalar.
    rewrite neg_zero.
    apply plus_lid.
Qed.

Theorem ext_to_geo_vector2 : ∀ u v,
    ext_to_geo (vector_to_ext V u * vector_to_ext V v) =
    -[B|] u v · 1 + vector_to_geo B u * vector_to_geo B v.
Proof.
    intros u v.
    rewrite ext_to_geo_add.
    rewrite ext_to_geo_vector.
    rewrite geo_mult_inner_vector.
    rewrite scalar_lneg.
    reflexivity.
Qed.
(* begin hide *)

End ExteriorToGeometric.
(* end hide *)
