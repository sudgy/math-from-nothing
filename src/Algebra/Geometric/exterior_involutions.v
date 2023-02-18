Require Import init.

Require Import mult_product.
Require Import set.
Require Import unordered_list.
Require Export nat.

Require Import linear_grade.
Require Import module_category.
Require Import algebra_category.

Require Export exterior_construct.
Require Import exterior_universal.
Require Import exterior_grade.

(* begin hide *)
Section ExteriorInvolutions.

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

Local Notation "'φ'" := (vector_to_ext V).
Local Notation "'σ'" := (scalar_to_ext V).

Local Open Scope nat_scope.

Definition ext_involute_base1 (v : module_V V) := -φ v.

Lemma ext_involute_base_plus : ∀ u v, ext_involute_base1 (u + v) =
    ext_involute_base1 u + ext_involute_base1 v.
Proof.
    intros u v.
    unfold ext_involute_base1.
    rewrite vector_to_ext_plus.
    apply neg_plus.
Qed.

Lemma ext_involute_base_scalar : ∀ a v,
    ext_involute_base1 (a · v) = a · ext_involute_base1 v.
Proof.
    intros a v.
    unfold ext_involute_base1.
    rewrite vector_to_ext_scalar.
    symmetry; apply scalar_rneg.
Qed.

Definition ext_involute_base2 := make_module_homomorphism
    F
    V
    (algebra_module (exterior_algebra V))
    ext_involute_base1
    ext_involute_base_plus
    ext_involute_base_scalar.

Lemma ext_involute_base_alternating : ∀ v,
    0 = ext_involute_base1 v * ext_involute_base1 v.
Proof.
    intros v.
    unfold ext_involute_base1.
    rewrite mult_lneg, mult_rneg.
    rewrite neg_neg.
    apply ext_alternating.
Qed.

Definition ext_involute_base3 := make_to_ext
    V
    (exterior_algebra V)
    ext_involute_base2
    ext_involute_base_alternating.

Definition ext_involute_base
    := ex_singleton (exterior_universal V ext_involute_base3).

Definition ext_involute_homo := [ext_involute_base|].
Definition ext_involute := algebra_homo_f ext_involute_homo : ext V → ext V.

Local Notation "a '∗'" := (ext_involute a) (at level 10).

(* end hide *)
Theorem ext_involute_plus : ∀ u v, (u + v)∗ = u∗ + v∗.
Proof.
    apply (algebra_homo_plus _ _ ext_involute_homo).
Qed.

Theorem ext_involute_scalar : ∀ a v, (a · v)∗ = a · v∗.
Proof.
    apply (algebra_homo_scalar _ _ ext_involute_homo).
Qed.

Theorem ext_involute_mult : ∀ u v, (u * v)∗ = u∗ * v∗.
Proof.
    apply (algebra_homo_mult _ _ ext_involute_homo).
Qed.

Theorem ext_involute_one : 1∗ = 1.
Proof.
    apply (algebra_homo_one _ _ ext_involute_homo).
Qed.

Theorem ext_involute_neg : ∀ v, (-v)∗ = -v∗.
Proof.
    apply (algebra_homo_neg ext_involute_homo).
Qed.

Theorem ext_involute_zero : 0∗ = 0.
Proof.
    apply (algebra_homo_zero ext_involute_homo).
Qed.

Theorem ext_involute_of_scalar : ∀ a, (σ a)∗ = σ a.
Proof.
    intros a.
    rewrite scalar_to_ext_one_scalar.
    rewrite ext_involute_scalar.
    rewrite ext_involute_one.
    reflexivity.
Qed.

Theorem ext_involute_vector : ∀ v, (φ v)∗ = -φ v.
Proof.
    apply [|ext_involute_base].
Qed.

Theorem ext_involute_involute : ∀ v, v∗∗ = v.
Proof.
    intros v.
    pose proof (ext_sum V v) as [l l_eq]; subst v.
    induction l as [|[a x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite ext_involute_zero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite ext_involute_plus.
    rewrite IHl; clear IHl.
    apply rplus.
    do 2 rewrite ext_involute_scalar.
    apply f_equal.
    clear a l.
    induction x as [|v l].
    {
        cbn.
        do 2 rewrite ext_involute_one.
        reflexivity.
    }
    cbn.
    do 2 rewrite ext_involute_mult.
    rewrite IHl; clear IHl.
    apply rmult.
    rewrite ext_involute_vector.
    rewrite ext_involute_neg.
    rewrite ext_involute_vector.
    apply neg_neg.
Qed.

(* begin hide *)
Definition ext_op := ext V.
Local Instance ext_op_mult : Mult ext_op := {
    mult a b := b * a
}.
Local Program Instance ext_op_ldist : Ldist ext_op.
Next Obligation.
    unfold mult; cbn.
    apply rdist.
Qed.
Local Program Instance ext_op_rdist : Rdist ext_op.
Next Obligation.
    unfold mult; cbn.
    apply ldist.
Qed.
Local Program Instance ext_op_mult_assoc : MultAssoc ext_op.
Next Obligation.
    unfold mult; cbn.
    symmetry; apply mult_assoc.
Qed.
Local Instance ext_op_one : One ext_op := {
    one := one
}.
Local Program Instance ext_op_mult_lid : MultLid ext_op.
Next Obligation.
    unfold mult; cbn.
    apply mult_rid.
Qed.
Local Program Instance ext_op_mult_rid : MultRid ext_op.
Next Obligation.
    unfold mult; cbn.
    apply mult_lid.
Qed.
Local Program Instance ext_op_scalar_lmult : ScalarLMult (cring_U F) ext_op.
Next Obligation.
    unfold mult; cbn.
    apply scalar_rmult.
Qed.
Local Program Instance ext_op_scalar_rmult : ScalarRMult (cring_U F) ext_op.
Next Obligation.
    unfold mult; cbn.
    apply scalar_lmult.
Qed.

Definition ext_op_algebra := make_algebra
    F
    (algebra_module (exterior_algebra V))
    ext_op_mult
    ext_op_ldist
    ext_op_rdist
    ext_op_mult_assoc
    ext_op_one
    ext_op_mult_lid
    ext_op_mult_rid
    ext_op_scalar_lmult
    ext_op_scalar_rmult
.

Remove Hints ext_op_mult ext_op_ldist ext_op_rdist ext_op_mult_assoc
    ext_op_one ext_op_mult_lid ext_op_mult_rid ext_op_scalar_lmult
    ext_op_scalar_rmult : typeclass_instances.

Definition ext_reverse_base1 (v : module_V V) := φ v : ext_op.

Lemma ext_reverse_base_plus : ∀ u v, ext_reverse_base1 (u + v) =
    ext_reverse_base1 u + ext_reverse_base1 v.
Proof.
    intros u v.
    unfold ext_reverse_base1.
    apply vector_to_ext_plus.
Qed.

Lemma ext_reverse_base_scalar : ∀ a v,
    ext_reverse_base1 (a · v) = a · ext_reverse_base1 v.
Proof.
    intros a v.
    unfold ext_reverse_base1.
    apply vector_to_ext_scalar.
Qed.

Definition ext_reverse_base2 := make_module_homomorphism
    F
    V
    (algebra_module ext_op_algebra)
    ext_reverse_base1
    ext_reverse_base_plus
    ext_reverse_base_scalar.

Lemma ext_reverse_base_alternating : ∀ v,
    0 = ext_reverse_base1 v * ext_reverse_base1 v.
Proof.
    intros v.
    unfold ext_reverse_base1.
    unfold mult; cbn.
    apply ext_alternating.
Qed.

Definition ext_reverse_base3 := make_to_ext
    V
    ext_op_algebra
    ext_reverse_base2
    ext_reverse_base_alternating.

Definition ext_reverse_base
    := ex_singleton (exterior_universal V ext_reverse_base3).

Definition ext_reverse_homo := [ext_reverse_base|].
Definition ext_reverse := algebra_homo_f ext_reverse_homo : ext V → ext V.

Local Notation "a '†'" := (ext_reverse a) (at level 10).

(* end hide *)
Theorem ext_reverse_plus : ∀ u v, (u + v)† = u† + v†.
Proof.
    apply (algebra_homo_plus _ _ ext_reverse_homo).
Qed.

Theorem ext_reverse_scalar : ∀ a v, (a · v)† = a · v†.
Proof.
    apply (algebra_homo_scalar _ _ ext_reverse_homo).
Qed.

Theorem ext_reverse_mult : ∀ u v,
    (@mult _ (ext_mult V) u v)† = @mult _ (ext_mult V) (v†) (u†).
Proof.
    apply (algebra_homo_mult _ _ ext_reverse_homo).
Qed.

Theorem ext_reverse_one : (@one _ (ext_one V))† = (@one _ (ext_one V)) .
Proof.
    apply (algebra_homo_one _ _ ext_reverse_homo).
Qed.

Theorem ext_reverse_neg : ∀ v, (-v)† = -v†.
Proof.
    apply (algebra_homo_neg ext_reverse_homo).
Qed.

Theorem ext_reverse_zero : 0† = 0.
Proof.
    apply (algebra_homo_zero ext_reverse_homo).
Qed.

Theorem ext_reverse_of_scalar : ∀ a, (σ a)† = σ a.
Proof.
    intros a.
    rewrite scalar_to_ext_one_scalar.
    rewrite ext_reverse_scalar.
    rewrite ext_reverse_one.
    reflexivity.
Qed.

Theorem ext_reverse_vector : ∀ v, (φ v)† = φ v.
Proof.
    apply [|ext_reverse_base].
Qed.

Theorem ext_reverse_reverse : ∀ v, v†† = v.
Proof.
    intros v.
    pose proof (ext_sum V v) as [l l_eq]; subst v.
    induction l as [|[a x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite ext_reverse_zero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite ext_reverse_plus.
    rewrite IHl; clear IHl.
    apply rplus.
    do 2 rewrite ext_reverse_scalar.
    apply f_equal.
    clear a l.
    induction x as [|v l].
    {
        cbn.
        do 2 rewrite ext_reverse_one.
        reflexivity.
    }
    cbn.
    do 2 rewrite ext_reverse_mult.
    rewrite IHl; clear IHl.
    apply rmult.
    do 2 rewrite ext_reverse_vector.
    reflexivity.
Qed.

Theorem ext_involute_grade : ∀ (X : ext V) (n : nat), of_grade n X →
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

Theorem ext_involute_swap : ∀ v (X : ext V), φ v * X = X∗ * φ v.
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

Theorem ext_reverse_grade : ∀ (X : ext V) (n : nat), of_grade n X →
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
