Require Import init.

Require Import order_minmax.

Require Import linear_transformation_space.

Require Export old_geometric_construct.
Require Export old_geometric_inner.
Require Export old_geometric_outer.
Require Import old_geometric_grade.
Require Import old_geometric_exterior_isomorphism.
Require Import old_geometric_involutions_grade.
Require Import old_geometric_decomposition.
Require Import old_exterior_grade.

(* begin hide *)
Section GeometricFormulae.

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
Let GL := geo_ldist B.
Let GR := geo_rdist B.
Let GMA := geo_mult_assoc B.
Let GML := geo_mult_lid B.
Let GMR := geo_mult_rid B.
Let GS := geo_scalar B.
Let GSO := geo_scalar_id B.
Let GSL := geo_scalar_ldist B.
Let GSR := geo_scalar_rdist B.
Let GSC := geo_scalar_comp B.
Let GSML := geo_scalar_lmult B.
Let GSMR := geo_scalar_rmult B.
Let GG := geo_grade B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GL GR GMA GML GMR GS GSO GSL
    GSR GSC GSML GSMR GG.

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
Let EMR := ext_mult_rid V.
Let EMA := ext_mult_assoc V.
Let ES := ext_scalar V.
Let ESO := ext_scalar_id V.
Let ESL := ext_scalar_ldist V.
Let ESR := ext_scalar_rdist V.
Let EG := exterior_grade V.
Let EGA := exterior_grade_mult V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO EL ER EMR EMA ES ESO ESL ESR.

Local Open Scope geo_scope.
Local Open Scope nat_scope.

(* end hide *)
Theorem lcontr_mult_inner : ∀ v X, φ v ⌋ X = geo_mult_inner B v X.
Proof.
    intros v X.
    induction X as [|X X' n Xn X'n IHX] using grade_induction.
    {
        rewrite geo_mult_inner_rzero.
        apply lcontr_ranni.
    }
    rewrite lcontr_ldist.
    rewrite geo_mult_inner_rplus.
    rewrite IHX.
    apply rplus; clear X' X'n IHX.
    pose proof (vector_to_geo_grade B v) as v1.
    rewrite (lcontr_homo _ _ _ _ _ v1 Xn).
    unfold geo_lcontr_base.
    nat_destruct n.
    {
        unfold zero at 1, one; cbn.
        apply geo_grade_zero_scalar in Xn as [a eq]; subst X.
        rewrite geo_mult_inner_scalar.
        reflexivity.
    }
    unfold one; cbn.
    rewrite nat_minus_zero.
    rewrite <- (ext_to_geo_to_ext B (φ v * X)).
    rewrite geo_to_ext_add.
    rewrite ext_to_geo_plus.
    rewrite grade_project_plus.
    rewrite ext_to_geo_inner.
    rewrite ext_to_geo_to_ext.
    rewrite ext_to_geo_project.
    assert (of_grade (H9 := EG)
        (nat_suc (nat_suc n)) (vector_to_ext V v * E X)) as Xn'.
    {
        change (nat_suc (nat_suc n)) with (1 + nat_suc n).
        apply (of_grade_mult (H13 := EGA)).
        -   apply vector_to_ext_grade.
        -   destruct Xn as [X' [X'n X'_eq]]; subst X.
            cbn.
            rewrite geo_to_ext_to_geo.
            exact X'n.
    }
    assert (nat_suc (nat_suc n) ≠ n) as neq.
    {
        clear.
        nat_induction n.
        -   intros contr; inversion contr.
        -   intros contr; inversion contr.
            contradiction.
    }
    rewrite (grade_project_of_grade_neq _ _ _ Xn' neq).
    rewrite ext_to_geo_zero.
    rewrite plus_rid.
    pose proof (geo_mult_inner_grade B v X n Xn) as Xn''.
    apply (grade_project_of_grade _ _ Xn'').
Qed.

Theorem lcontr_bilinear : ∀ a b, φ a ⌋ φ b = [B|] a b · 1.
Proof.
    intros a b.
    rewrite lcontr_mult_inner.
    apply geo_mult_inner_vector.
Qed.

Theorem inner_bilinear : ∀ a b, φ a • φ b = [B|] a b · 1.
Proof.
    intros a b.
    rewrite <- (lcontr_inner _ _ _ _ _ (refl 1)
        (vector_to_geo_grade B a) (vector_to_geo_grade B b)).
    apply lcontr_bilinear.
Qed.

Theorem rcontr_bilinear : ∀ a b, φ a ⌊ φ b = [B|] a b · 1.
Proof.
    intros a b.
    rewrite (rcontr_inner _ _ _ _ _ (refl 1)
        (vector_to_geo_grade B a) (vector_to_geo_grade B b)).
    apply inner_bilinear.
Qed.

Theorem lcontr_geo_add : ∀ a v X,
    φ a ⌋ (φ v * X) = φ a ⌋ φ v * X - φ v * (φ a ⌋ X).
Proof.
    intros a v X.
    rewrite lcontr_bilinear.
    do 2 rewrite lcontr_mult_inner.
    rewrite scalar_lmult.
    rewrite mult_lid.
    apply geo_mult_inner_add.
Qed.

Theorem lcontr_outer_add : ∀ a v X,
    φ a ⌋ (φ v ⋀ X) = φ a ⌋ φ v * X - φ v ⋀ (φ a ⌋ X).
Proof.
    intros a v X.
    rewrite lcontr_bilinear.
    rewrite scalar_lmult.
    rewrite mult_lid.
    do 2 rewrite outer_exterior.
    do 2 rewrite lcontr_mult_inner.
    rewrite <- ext_to_geo_inner.
    rewrite geo_to_ext_inner.
    rewrite geo_to_ext_vector.
    rewrite ext_inner_add.
    rewrite ext_to_geo_plus.
    rewrite ext_to_geo_scalar.
    rewrite ext_to_geo_to_ext.
    rewrite ext_to_geo_neg.
    reflexivity.
Qed.

Theorem lcontr_vector_scalar : ∀ v a, φ v ⌋ σ a = 0.
Proof.
    intros v a.
    rewrite lcontr_mult_inner.
    apply geo_mult_inner_scalar.
Qed.

Theorem rcontr_scalar_vector : ∀ a v, σ a ⌊ φ v = 0.
Proof.
    intros a v.
    rewrite <- (geo_reverse_reverse B (σ a ⌊ φ v)).
    rewrite rlcontr_reverse.
    rewrite geo_reverse_vector, geo_reverse_of_scalar.
    rewrite lcontr_vector_scalar.
    apply geo_reverse_zero.
Qed.

Theorem rcontr_geo_add : ∀ a v X,
    (X * φ v) ⌊ φ a = φ a ⌋ φ v * X - (X ⌊ φ a) * φ v.
Proof.
    intros a v X.
    rewrite <- (geo_reverse_reverse B ((X * φ v) ⌊ φ a)).
    rewrite rlcontr_reverse.
    rewrite geo_reverse_mult.
    do 2 rewrite geo_reverse_vector.
    rewrite lcontr_geo_add.
    rewrite lcontr_bilinear.
    do 2 rewrite scalar_lmult.
    do 2 rewrite mult_lid.
    rewrite geo_reverse_plus.
    rewrite geo_reverse_scalar.
    rewrite geo_reverse_neg.
    rewrite geo_reverse_mult.
    rewrite lrcontr_reverse.
    do 2 rewrite geo_reverse_vector.
    rewrite geo_reverse_reverse.
    reflexivity.
Qed.

Theorem rcontr_outer_add : ∀ a v X,
    (X ⋀ φ v) ⌊ φ a = φ a ⌋ φ v * X - (X ⌊ φ a) ⋀ φ v.
Proof.
    intros a v X.
    rewrite <- (geo_reverse_reverse B ((X ⋀ φ v) ⌊ φ a)).
    rewrite rlcontr_reverse.
    rewrite outer_reverse.
    do 2 rewrite geo_reverse_vector.
    rewrite lcontr_outer_add.
    rewrite lcontr_bilinear.
    do 2 rewrite scalar_lmult.
    do 2 rewrite mult_lid.
    rewrite geo_reverse_plus.
    rewrite geo_reverse_scalar.
    rewrite geo_reverse_neg.
    rewrite outer_reverse.
    rewrite lrcontr_reverse.
    do 2 rewrite geo_reverse_vector.
    rewrite geo_reverse_reverse.
    reflexivity.
Qed.

Theorem vector_lmult : ∀ v X, φ v * X = φ v ⌋ X + φ v ⋀ X.
Proof.
    intros v X.
    induction X as [|X X' n Xn X'n IHX] using grade_induction.
    {
        rewrite mult_ranni.
        rewrite lcontr_ranni.
        rewrite outer_ranni.
        rewrite plus_lid.
        reflexivity.
    }
    rewrite ldist.
    rewrite lcontr_ldist.
    rewrite outer_ldist.
    rewrite IHX; clear IHX.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite <- plus_assoc.
    rewrite (plus_comm (φ v ⌋ X')).
    rewrite plus_assoc.
    apply rplus; clear X' X'n.
    nat_destruct n.
    {
        apply geo_grade_zero_scalar in Xn as [a eq]; subst X.
        rewrite lcontr_vector_scalar.
        rewrite plus_lid.
        rewrite scalar_to_geo_one_scalar at 2.
        rewrite outer_rscalar.
        rewrite outer_rid.
        rewrite <- scalar_to_geo_comm.
        apply scalar_to_geo_scalar.
    }
    pose proof (vector_to_geo_grade B v) as v1.
    rewrite (lcontr_homo _ _ _ _ _ v1 Xn).
    rewrite (outer_homo _ _ _ _ _ v1 Xn).
    unfold geo_lcontr_base, geo_outer_base.
    rewrite (geo_grade_decompose _ _ _ _ _ v1 Xn).
    unfold min; case_if.
    2: {
        exfalso; clear - n0.
        rewrite nle_lt in n0.
        change 1 with (nat_suc 0) in n0.
        rewrite nat_sucs_lt in n0.
        apply (nat_neg2 n0).
    }
    clear l.
    change (nat_suc 1) with (nat_suc (nat_suc nat_zero)); cbn.
    do 3 rewrite plus_lid.
    unfold one at 7; cbn.
    change nat_zero with (zero (U := nat)).
    rewrite nat_minus_zero.
    change (nat_suc 0) with (one (U := nat)).
    rewrite mult_ranni, mult_rid.
    rewrite plus_rid.
    change (nat_suc n) with (1 + n).
    rewrite nat_abs_minus_comm.
    rewrite nat_abs_minus_plus.
    rewrite (plus_comm n 2).
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem vector_rmult : ∀ X v, X * φ v = X ⌊ φ v + X ⋀ φ v.
Proof.
    intros X v.
    rewrite <- (geo_reverse_reverse B (X * φ v)).
    rewrite geo_reverse_mult.
    rewrite geo_reverse_vector.
    rewrite vector_lmult.
    rewrite geo_reverse_plus.
    rewrite lrcontr_reverse.
    rewrite outer_reverse.
    rewrite geo_reverse_reverse.
    rewrite geo_reverse_vector.
    reflexivity.
Qed.

Theorem lcontr_twice : ∀ a X, φ a ⌋ (φ a ⌋ X) = 0.
Proof.
    intros a X.
    do 2 rewrite lcontr_mult_inner.
    pose proof (geo_mult_inner_alternating B a) as eq.
    inversion eq as [eq2].
    unfold linear_trans_mult_base, linear_trans_zero_base in eq2; cbn in eq2.
    apply (func_eq _ _ eq2).
Qed.
(* begin hide *)

End GeometricFormulae.
(* end hide *)
