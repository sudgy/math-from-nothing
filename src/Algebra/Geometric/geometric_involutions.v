Require Import init.

Require Import mult_product.
Require Import card.

Require Export geometric_construct.
Require Import geometric_universal.

(* begin hide *)
Section GeometricInvolutions.

(* end hide *)
Context {F : CRing} {V : Module F}.
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
Let GSL := geo_scalar_ldist B.
Let GSR := geo_scalar_rdist B.
Let GSC := geo_scalar_comp B.
Let GSML := geo_scalar_lmult B.
Let GSMR := geo_scalar_rmult B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GL GR GMA GML GMR GS GSL GSR
    GSC GSML GSMR.

Local Notation "'φ'" := (vector_to_geo B).
Local Notation "'σ'" := (scalar_to_geo B).

Definition geo_involute_base1 (v : module_V V) := -φ v.

Lemma geo_involute_base_plus : ∀ u v, geo_involute_base1 (u + v) =
        geo_involute_base1 u + geo_involute_base1 v.
    intros u v.
    unfold geo_involute_base1.
    rewrite vector_to_geo_plus.
    apply neg_plus.
Qed.

Lemma geo_involute_base_scalar : ∀ a v,
        geo_involute_base1 (a · v) = a · geo_involute_base1 v.
    intros a v.
    unfold geo_involute_base1.
    rewrite vector_to_geo_scalar.
    symmetry; apply scalar_rneg.
Qed.

Definition geo_involute_base2 := make_module_homomorphism
    F
    V
    (algebra_module (geometric_algebra B))
    geo_involute_base1
    geo_involute_base_plus
    geo_involute_base_scalar.

Lemma geo_involute_base_contract : ∀ v,
        geo_involute_base1 v * geo_involute_base1 v = [B|] v v · 1.
    intros v.
    unfold geo_involute_base1.
    rewrite mult_lneg, mult_rneg.
    rewrite neg_neg.
    apply geo_contract.
Qed.

Definition geo_involute_base3 := make_to_geo
    B
    (geometric_algebra B)
    geo_involute_base2
    geo_involute_base_contract.

Definition geo_involute_base
    := card_one_ex (geometric_universal B geo_involute_base3).

Definition geo_involute_homo := [geo_involute_base|].
Definition geo_involute := algebra_homo_f geo_involute_homo : geo B → geo B.

Local Notation "a '∗'" := (geo_involute a) (at level 10).

(* end hide *)
Theorem geo_involute_plus : ∀ u v, (u + v)∗ = u∗ + v∗.
    apply (algebra_homo_plus _ _ geo_involute_homo).
Qed.

Theorem geo_involute_scalar : ∀ a v, (a · v)∗ = a · v∗.
    apply (algebra_homo_scalar _ _ geo_involute_homo).
Qed.

Theorem geo_involute_mult : ∀ u v, (u * v)∗ = u∗ * v∗.
    apply (algebra_homo_mult _ _ geo_involute_homo).
Qed.

Theorem geo_involute_one : 1∗ = 1.
    apply (algebra_homo_one _ _ geo_involute_homo).
Qed.

Theorem geo_involute_neg : ∀ v, (-v)∗ = -v∗.
    apply (algebra_homo_neg geo_involute_homo).
Qed.

Theorem geo_involute_zero : 0∗ = 0.
    apply (algebra_homo_zero geo_involute_homo).
Qed.

Theorem geo_involute_of_scalar : ∀ a, (σ a)∗ = σ a.
    intros a.
    rewrite scalar_to_geo_one_scalar.
    rewrite geo_involute_scalar.
    rewrite geo_involute_one.
    reflexivity.
Qed.

Theorem geo_involute_vector : ∀ v, (φ v)∗ = -φ v.
    apply [|geo_involute_base].
Qed.

Theorem geo_involute_involute : ∀ v, v∗∗ = v.
    intros v.
    pose proof (geo_sum B v) as [l l_eq]; subst v.
    induction l as [|[a x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite geo_involute_zero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite geo_involute_plus.
    rewrite IHl; clear IHl.
    apply rplus.
    do 2 rewrite geo_involute_scalar.
    apply f_equal.
    clear a l.
    induction x as [|v l].
    {
        cbn.
        do 2 rewrite geo_involute_one.
        reflexivity.
    }
    cbn.
    do 2 rewrite geo_involute_mult.
    rewrite IHl; clear IHl.
    apply rmult.
    rewrite geo_involute_vector.
    rewrite geo_involute_neg.
    rewrite geo_involute_vector.
    apply neg_neg.
Qed.

(* begin hide *)
Definition geo_op := geo B.
Local Instance geo_op_mult : Mult geo_op := {
    mult a b := b * a
}.
Local Program Instance geo_op_ldist : Ldist geo_op.
Next Obligation.
    unfold mult; cbn.
    apply rdist.
Qed.
Local Program Instance geo_op_rdist : Rdist geo_op.
Next Obligation.
    unfold mult; cbn.
    apply ldist.
Qed.
Local Program Instance geo_op_mult_assoc : MultAssoc geo_op.
Next Obligation.
    unfold mult; cbn.
    symmetry; apply mult_assoc.
Qed.
Local Instance geo_op_one : One geo_op := {
    one := one
}.
Local Program Instance geo_op_mult_lid : MultLid geo_op.
Next Obligation.
    unfold mult; cbn.
    apply mult_rid.
Qed.
Local Program Instance geo_op_mult_rid : MultRid geo_op.
Next Obligation.
    unfold mult; cbn.
    apply mult_lid.
Qed.
Local Program Instance geo_op_scalar_lmult : ScalarLMult (cring_U F) geo_op.
Next Obligation.
    unfold mult; cbn.
    apply scalar_rmult.
Qed.
Local Program Instance geo_op_scalar_rmult : ScalarRMult (cring_U F) geo_op.
Next Obligation.
    unfold mult; cbn.
    apply scalar_lmult.
Qed.

Definition geo_op_algebra := make_algebra
    F
    (algebra_module (geometric_algebra B))
    geo_op_mult
    geo_op_ldist
    geo_op_rdist
    geo_op_mult_assoc
    geo_op_one
    geo_op_mult_lid
    geo_op_mult_rid
    geo_op_scalar_lmult
    geo_op_scalar_rmult
.

Remove Hints geo_op_mult geo_op_ldist geo_op_rdist geo_op_mult_assoc
    geo_op_one geo_op_mult_lid geo_op_mult_rid geo_op_scalar_lmult
    geo_op_scalar_rmult : typeclass_instances.

Definition geo_reverse_base1 (v : module_V V) := φ v : geo_op.

Lemma geo_reverse_base_plus : ∀ u v, geo_reverse_base1 (u + v) =
        geo_reverse_base1 u + geo_reverse_base1 v.
    intros u v.
    unfold geo_reverse_base1.
    apply vector_to_geo_plus.
Qed.

Lemma geo_reverse_base_scalar : ∀ a v,
        geo_reverse_base1 (a · v) = a · geo_reverse_base1 v.
    intros a v.
    unfold geo_reverse_base1.
    apply vector_to_geo_scalar.
Qed.

Definition geo_reverse_base2 := make_module_homomorphism
    F
    V
    (algebra_module geo_op_algebra)
    geo_reverse_base1
    geo_reverse_base_plus
    geo_reverse_base_scalar.

Lemma geo_reverse_base_contract : ∀ v,
        geo_reverse_base1 v * geo_reverse_base1 v = [B|] v v · 1.
    intros v.
    unfold geo_reverse_base1.
    unfold mult; cbn.
    apply geo_contract.
Qed.

Definition geo_reverse_base3 := make_to_geo
    B
    geo_op_algebra
    geo_reverse_base2
    geo_reverse_base_contract.

Definition geo_reverse_base
    := card_one_ex (geometric_universal B geo_reverse_base3).

Definition geo_reverse_homo := [geo_reverse_base|].
Definition geo_reverse := algebra_homo_f geo_reverse_homo : geo B → geo B.

Local Notation "a '†'" := (geo_reverse a) (at level 10).

(* end hide *)
Theorem geo_reverse_plus : ∀ u v, (u + v)† = u† + v†.
    apply (algebra_homo_plus _ _ geo_reverse_homo).
Qed.

Theorem geo_reverse_scalar : ∀ a v, (a · v)† = a · v†.
    apply (algebra_homo_scalar _ _ geo_reverse_homo).
Qed.

Theorem geo_reverse_mult : ∀ u v, (u * v)† = (v†) * (u†).
    apply (algebra_homo_mult _ _ geo_reverse_homo).
Qed.

Theorem geo_reverse_one : 1† = 1.
    apply (algebra_homo_one _ _ geo_reverse_homo).
Qed.

Theorem geo_reverse_neg : ∀ v, (-v)† = -v†.
    apply (algebra_homo_neg geo_reverse_homo).
Qed.

Theorem geo_reverse_zero : 0† = 0.
    apply (algebra_homo_zero geo_reverse_homo).
Qed.

Theorem geo_reverse_of_scalar : ∀ a, (σ a)† = σ a.
    intros a.
    rewrite scalar_to_geo_one_scalar.
    rewrite geo_reverse_scalar.
    rewrite geo_reverse_one.
    reflexivity.
Qed.

Theorem geo_reverse_vector : ∀ v, (φ v)† = φ v.
    apply [|geo_reverse_base].
Qed.

Theorem geo_reverse_reverse : ∀ v, v†† = v.
    intros v.
    pose proof (geo_sum B v) as [l l_eq]; subst v.
    induction l as [|[a x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite geo_reverse_zero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite geo_reverse_plus.
    rewrite IHl; clear IHl.
    apply rplus.
    do 2 rewrite geo_reverse_scalar.
    apply f_equal.
    clear a l.
    induction x as [|v l].
    {
        cbn.
        do 2 rewrite geo_reverse_one.
        reflexivity.
    }
    cbn.
    do 2 rewrite geo_reverse_mult.
    rewrite IHl; clear IHl.
    apply rmult.
    do 2 rewrite geo_reverse_vector.
    reflexivity.
Qed.

(* begin hide *)
End GeometricInvolutions.

(* end hide *)
Notation "a '∗'" := (geo_involute _ a) (at level 10) : geo_scope.
Notation "a '†'" := (geo_reverse _ a) (at level 10) : geo_scope.
