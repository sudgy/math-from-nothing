Require Import init.

Require Export set.
Require Export unordered_list.
Require Export nat.

Require Import linear_grade.
Require Import module_category.
Require Import algebra_category.

Require Export exterior_base.
Require Export exterior_grade2.
Require Import geometric_involutions.

Section ExteriorInvolutions.

Context {F : CRingObj} (V : ModuleObj F).
Local Notation φ := (vector_to_ext V).
Local Notation σ := (scalar_to_ext V).
Local Notation ext := (exterior_algebra V).

Definition ext_involute := (geo_involute _) : ext → ext.
Local Notation "a '∗'" := (ext_involute a) (at level 10).

Theorem ext_involute_plus : ∀ u v, (u + v)∗ = u∗ + v∗.
Proof.
    apply geo_involute_plus.
Qed.
Theorem ext_involute_scalar : ∀ a v, (a · v)∗ = a · v∗.
Proof.
    apply geo_involute_scalar.
Qed.
Theorem ext_involute_mult : ∀ u v, (u * v)∗ = u∗ * v∗.
Proof.
    apply geo_involute_mult.
Qed.
Theorem ext_involute_one : 1∗ = 1.
Proof.
    apply geo_involute_one.
Qed.
Theorem ext_involute_neg : ∀ v, (-v)∗ = -v∗.
Proof.
    apply geo_involute_neg.
Qed.
Theorem ext_involute_zero : 0∗ = 0.
Proof.
    apply geo_involute_zero.
Qed.
Theorem ext_involute_of_scalar : ∀ a, (σ a)∗ = σ a.
Proof.
    apply geo_involute_of_scalar.
Qed.
Theorem ext_involute_vector : ∀ v, (φ v)∗ = -φ v.
Proof.
    apply geo_involute_vector.
Qed.
Theorem ext_involute_involute : ∀ v, v∗∗ = v.
Proof.
    apply geo_involute_involute.
Qed.

Definition ext_reverse := (geo_reverse _) : ext → ext.
Local Notation "a '†'" := (ext_reverse a) (at level 10).

Theorem ext_reverse_plus : ∀ u v, (u + v)† = u† + v†.
Proof.
    apply geo_reverse_plus.
Qed.
Theorem ext_reverse_scalar : ∀ a v, (a · v)† = a · v†.
Proof.
    apply geo_reverse_scalar.
Qed.
Theorem ext_reverse_mult : ∀ u v, (u * v)† = (v†) * (u†).
Proof.
    apply geo_reverse_mult.
Qed.
Theorem ext_reverse_one : 1† = 1.
Proof.
    apply geo_reverse_one.
Qed.
Theorem ext_reverse_neg : ∀ v, (-v)† = -v†.
Proof.
    apply geo_reverse_neg.
Qed.
Theorem ext_reverse_zero : 0† = 0.
Proof.
    apply geo_reverse_zero.
Qed.
Theorem ext_reverse_of_scalar : ∀ a, (σ a)† = σ a.
Proof.
    apply geo_reverse_of_scalar.
Qed.
Theorem ext_reverse_vector : ∀ v, (φ v)† = φ v.
Proof.
    apply geo_reverse_vector.
Qed.
Theorem ext_reverse_reverse : ∀ v, v†† = v.
Proof.
    apply geo_reverse_reverse.
Qed.

Local Open Scope nat_scope.
Local Existing Instances exterior_grade.

Theorem ext_involute_grade : ∀ (X : ext) (n : nat), of_grade n X →
    X∗ = (-(1))^n · X.
Proof.
    intros X n Xn.
    apply ext_grade_sum in Xn as [l l_eq]; subst X.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite scalar_ranni.
        apply ext_involute_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_involute_plus.
    rewrite scalar_ldist.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite ext_involute_scalar.
    rewrite scalar_comp.
    rewrite (mult_comm _ α).
    rewrite <- scalar_comp.
    apply lscalar.
    destruct x as [l n_eq]; cbn.
    subst n.
    induction l.
    -   cbn.
        rewrite nat_pow_zero.
        rewrite scalar_id.
        apply ext_involute_one.
    -   cbn.
        rewrite ext_involute_mult.
        rewrite IHl.
        rewrite ext_involute_vector.
        rewrite <- scalar_comp.
        rewrite scalar_neg_one.
        rewrite scalar_rmult.
        rewrite mult_lneg.
        reflexivity.
Qed.

Theorem ext_involute_swap : ∀ v (X : ext), φ v * X = X∗ * φ v.
Proof.
    intros v X.
    pose proof (ext_sum V X) as [l l_eq]; subst X.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ext_involute_zero.
        rewrite mult_lanni, mult_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_involute_plus.
    rewrite ldist, rdist.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite ext_involute_scalar.
    rewrite scalar_lmult, scalar_rmult.
    apply lscalar.
    induction x as [|a l].
    -   cbn.
        rewrite ext_involute_one.
        rewrite mult_lid, mult_rid.
        reflexivity.
    -   cbn.
        rewrite mult_assoc.
        rewrite ext_anticomm.
        rewrite <- mult_lneg.
        rewrite <- mult_assoc.
        rewrite IHl; clear IHl.
        rewrite ext_involute_mult.
        rewrite ext_involute_vector.
        apply mult_assoc.
Qed.

Theorem ext_reverse_grade : ∀ (X : ext) (n : nat), of_grade n X →
    X† = (-(1))^(binom n 2) · X.
Proof.
    intros X n Xn.
    apply ext_grade_sum in Xn as [l l_eq]; subst X.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite scalar_ranni.
        apply ext_reverse_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_reverse_plus.
    rewrite scalar_ldist.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite ext_reverse_scalar.
    rewrite scalar_comp.
    rewrite (mult_comm _ α).
    rewrite <- scalar_comp.
    apply lscalar.
    destruct x as [l n_eq]; cbn.
    subst n.
    induction l.
    -   cbn.
        rewrite nat_pow_zero.
        rewrite scalar_id.
        apply ext_reverse_one.
    -   rewrite list_image_add; cbn.
        rewrite list_prod_add.
        rewrite ext_reverse_mult.
        rewrite IHl; clear IHl.
        rewrite ext_reverse_vector.
        rewrite scalar_lmult.
        rewrite ext_involute_swap.
        pose proof (ext_list_grade V l) as l_grade.
        rewrite (ext_involute_grade _ _ l_grade).
        rewrite scalar_lmult.
        rewrite scalar_comp.
        apply rscalar.
        rewrite list_size_add.
        remember (list_size l) as n.
        clear Heqn l_grade.
        unfold one at 5; cbn.
        rewrite nat_plus_lsuc.
        unfold plus at 2; cbn.
        rewrite binom_suc.
        rewrite <- nat_pow_plus.
        change (nat_suc 1) with (one (U := nat) + 1).
        rewrite binom_one.
        rewrite (plus_comm n).
        rewrite <- plus_assoc.
        rewrite nat_pow_plus.
        rewrite <- (mult_lid n) at 3 4.
        rewrite <- rdist.
        rewrite nat_pow_neg_even.
        rewrite mult_rid.
        reflexivity.
Qed.
(* begin hide *)

End ExteriorInvolutions.
(* end hide *)
