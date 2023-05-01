Require Import init.

Require Export geometric_base.

Section GeometricNorm.

Context {F : CRingObj} {V : ModuleObj F}.
Context (B : set_type (bilinear_form (V := V))).

Let GG := geo_grade B.

Existing Instances GG.

Local Notation φ := (vector_to_geo B).
Local Notation σ := (scalar_to_geo B).
Local Notation geo := (geometric_algebra B).

Local Open Scope geo_scope.

Definition scalar_part (A : geo) := ex_val
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
    rewrite nat_pow_zero.
    apply scalar_id.
Qed.

Theorem scalar_part_comm : ∀ A B, scalar_part (A * B) = scalar_part (B * A).
Proof.
    intros a b.
    induction a as [|a a'] using grade_induction.
    {
        rewrite mult_lanni, mult_ranni.
        reflexivity.
    }
    rewrite rdist, ldist.
    do 2 rewrite scalar_part_plus.
    rewrite IHa.
    apply rplus; clear a' IHa.
    induction b as [|b b'] using grade_induction.
    {
        rewrite mult_lanni, mult_ranni.
        reflexivity.
    }
    rewrite rdist, ldist.
    do 2 rewrite scalar_part_plus.
    rewrite IHb.
    apply rplus; clear b' IHb.
    destruct a as [a [m am]].
    destruct b as [b [n bn]].
    cbn.
    classic_case (m = n) as [eq|neq].
    -   subst m.
        rewrite <- (geo_reverse_reverse B (a * b)).
        rewrite scalar_part_reverse.
        rewrite geo_reverse_mult.
        rewrite (geo_reverse_grade _ _ _ am).
        rewrite (geo_reverse_grade _ _ _ bn).
        rewrite scalar_lmult, scalar_rmult.
        rewrite scalar_comp.
        rewrite <- nat_pow_plus.
        rewrite <- (mult_lid (binom n 2)).
        rewrite <- rdist.
        rewrite nat_pow_neg_even.
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

Definition geo_norm2 (A : geo) := scalar_part (A† * A).

Definition geo_normalized (A : geo) := geo_norm2 A = 1.
(* begin hide *)

(* Eventually define it for real numbers as well *)

End GeometricNorm.
(* end hide *)
