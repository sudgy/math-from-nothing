Require Import init.

Require Import mult_pow.

Require Export geometric_construct.
Require Import geometric_involutions.
Require Import geometric_involutions_grade.
Require Import geometric_grade.
Require Import geometric_exterior_isomorphism.
Require Import geometric_decomposition.

(* begin hide *)
Section GeometricNorm.

(* end hide *)
Context {F : CRingObj} {V : ModuleObj F}.
(* begin hide *)

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

Local Open Scope geo_scope.

(* end hide *)
Definition scalar_part (A : geo B) := ex_val
    (geo_grade_zero_scalar B (grade_project A 0) (grade_project_grade A 0)).

Theorem scalar_part_eq : ∀ A, σ (scalar_part A) = grade_project A 0.
Proof.
    intros A.
    unfold scalar_part.
    rewrite_ex_val a a_eq.
    symmetry; exact a_eq.
Qed.

Theorem scalar_part_plus : ∀ A B,
    scalar_part (A + B) = scalar_part A + scalar_part B.
Proof.
    intros a b.
    apply (scalar_to_geo_eq B).
    rewrite scalar_to_geo_plus.
    do 3 rewrite scalar_part_eq.
    apply grade_project_plus.
Qed.

Theorem scalar_part_scalar : ∀ α A, scalar_part (α · A) = α * scalar_part A.
Proof.
    intros α A.
    apply (scalar_to_geo_eq B).
    rewrite scalar_to_geo_mult.
    do 2 rewrite scalar_part_eq.
    rewrite scalar_to_geo_scalar.
    apply grade_project_scalar.
Qed.

Theorem scalar_part_reverse : ∀ A, scalar_part (A†) = scalar_part A.
Proof.
    intros A.
    apply (scalar_to_geo_eq B).
    do 2 rewrite scalar_part_eq.
    rewrite <- geo_reverse_project.
    pose proof (grade_project_grade A 0) as A0.
    rewrite (geo_reverse_grade _ _ _ A0).
    unfold zero at 1, one at 2 3, plus, binom; cbn.
    rewrite pow_0_nat.
    apply scalar_id.
Qed.

Theorem scalar_part_comm : ∀ A B, scalar_part (A * B) = scalar_part (B * A).
Proof.
    intros a b.
    induction a as [|a a' m am a'm IHa] using grade_induction.
    {
        rewrite mult_lanni, mult_ranni.
        reflexivity.
    }
    rewrite rdist, ldist.
    do 2 rewrite scalar_part_plus.
    rewrite IHa.
    apply rplus; clear a' a'm IHa.
    induction b as [|b b' n bn b'n IHb] using grade_induction.
    {
        rewrite mult_lanni, mult_ranni.
        reflexivity.
    }
    rewrite rdist, ldist.
    do 2 rewrite scalar_part_plus.
    rewrite IHb.
    apply rplus; clear b' b'n IHb.
    classic_case (m = n) as [eq|neq].
    -   subst m.
        rewrite <- (geo_reverse_reverse B (a * b)).
        rewrite scalar_part_reverse.
        rewrite geo_reverse_mult.
        rewrite (geo_reverse_grade _ _ _ am).
        rewrite (geo_reverse_grade _ _ _ bn).
        rewrite scalar_lmult, scalar_rmult.
        rewrite scalar_comp.
        rewrite pow_mult_nat.
        rewrite <- (mult_lid (binom n 2)).
        rewrite <- rdist.
        rewrite pow_neg_one_even.
        rewrite scalar_id.
        reflexivity.
    -   apply (scalar_to_geo_eq B).
        do 2 rewrite scalar_part_eq.
        rewrite (geo_mult_project_smaller _ _ _ _ _ am bn).
        rewrite (geo_mult_project_smaller _ _ _ _ _ bn am).
        reflexivity.
        +   split; [>apply nat_pos|].
            intros contr.
            apply nat_abs_minus_eq_zero in contr.
            subst; contradiction.
        +   split; [>apply nat_pos|].
            intros contr.
            apply nat_abs_minus_eq_zero in contr.
            contradiction.
Qed.

Definition geo_norm2 (A : geo B) := scalar_part (A† * A).

Definition geo_normalized (A : geo B) := geo_norm2 A = 1.
(* begin hide *)

(* Eventually define it for real numbers as well *)

End GeometricNorm.
(* end hide *)
