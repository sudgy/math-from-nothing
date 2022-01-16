Require Import init.

Require Import mult_product.
Require Import card.

Require Export geometric_construct.
Require Import geometric_universal.

Section GeometricInvolutions.

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
Let GL := ga_ldist B.
Let GR := ga_rdist B.
Let GMA := ga_mult_assoc B.
Let GML := ga_mult_lid B.
Let GMR := ga_mult_rid B.
Let GS := ga_scalar B.
Let GSL := ga_scalar_ldist B.
Let GSR := ga_scalar_rdist B.
Let GSC := ga_scalar_comp B.
Let GSML := ga_scalar_lmult B.
Let GSMR := ga_scalar_rmult B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GL GR GMA GML GMR GS GSL GSR
    GSC GSML GSMR.

Local Notation "'φ'" := (vector_to_ga B).
Local Notation "'σ'" := (scalar_to_ga B).

Definition ga_conjugate_base1 (v : module_V V) := -φ v.

Lemma ga_conjugate_base_plus : ∀ u v, ga_conjugate_base1 (u + v) =
        ga_conjugate_base1 u + ga_conjugate_base1 v.
    intros u v.
    unfold ga_conjugate_base1.
    rewrite vector_to_ga_plus.
    apply neg_plus.
Qed.

Lemma ga_conjugate_base_scalar : ∀ a v,
        ga_conjugate_base1 (a · v) = a · ga_conjugate_base1 v.
    intros a v.
    unfold ga_conjugate_base1.
    rewrite vector_to_ga_scalar.
    symmetry; apply scalar_rneg.
Qed.

Definition ga_conjugate_base2 := make_module_homomorphism
    F
    V
    (algebra_module (geometric_algebra B))
    ga_conjugate_base1
    ga_conjugate_base_plus
    ga_conjugate_base_scalar.

Lemma ga_conjugate_base_contract : ∀ v,
        ga_conjugate_base1 v * ga_conjugate_base1 v = [B|] v v · 1.
    intros v.
    unfold ga_conjugate_base1.
    rewrite mult_lneg, mult_rneg.
    rewrite neg_neg.
    apply ga_contract.
Qed.

Definition ga_conjugate_base3 := make_to_ga
    B
    (geometric_algebra B)
    ga_conjugate_base2
    ga_conjugate_base_contract.

Definition ga_conjugate_base
    := card_one_ex (geometric_universal B ga_conjugate_base3).

Definition ga_conjugate_homo := [ga_conjugate_base|].
Definition ga_conjugate := algebra_homo_f ga_conjugate_homo : ga B → ga B.

Local Notation "a '∗'" := (ga_conjugate a) (at level 10).

Theorem ga_conjugate_plus : ∀ u v, (u + v)∗ = u∗ + v∗.
    apply (algebra_homo_plus _ _ ga_conjugate_homo).
Qed.

Theorem ga_conjugate_scalar : ∀ a v, (a · v)∗ = a · v∗.
    apply (algebra_homo_scalar _ _ ga_conjugate_homo).
Qed.

Theorem ga_conjugate_mult : ∀ u v, (u * v)∗ = u∗ * v∗.
    apply (algebra_homo_mult _ _ ga_conjugate_homo).
Qed.

Theorem ga_conjugate_one : 1∗ = 1.
    apply (algebra_homo_one _ _ ga_conjugate_homo).
Qed.

Theorem ga_conjugate_neg : ∀ v, (-v)∗ = -v∗.
    apply (algebra_homo_neg ga_conjugate_homo).
Qed.

Theorem ga_conjugate_zero : 0∗ = 0.
    apply (algebra_homo_zero ga_conjugate_homo).
Qed.

Theorem ga_conjugate_of_scalar : ∀ a, (σ a)∗ = σ a.
    intros a.
    rewrite scalar_to_ga_one_scalar.
    rewrite ga_conjugate_scalar.
    rewrite ga_conjugate_one.
    reflexivity.
Qed.

Theorem ga_conjugate_vector : ∀ v, (φ v)∗ = -φ v.
    apply [|ga_conjugate_base].
Qed.

Theorem ga_conjugate_conjugate : ∀ v, v∗∗ = v.
    intros v.
    pose proof (ga_sum B v) as [l l_eq]; subst v.
    induction l as [|[a x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite ga_conjugate_zero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite ga_conjugate_plus.
    rewrite IHl; clear IHl.
    apply rplus.
    do 2 rewrite ga_conjugate_scalar.
    apply f_equal.
    clear a l.
    induction x as [|v l].
    {
        cbn.
        do 2 rewrite ga_conjugate_one.
        reflexivity.
    }
    cbn.
    do 2 rewrite ga_conjugate_mult.
    rewrite IHl; clear IHl.
    apply rmult.
    rewrite ga_conjugate_vector.
    rewrite ga_conjugate_neg.
    rewrite ga_conjugate_vector.
    apply neg_neg.
Qed.

Definition ga_op := ga B.
Local Instance ga_op_mult : Mult ga_op := {
    mult a b := b * a
}.
Local Program Instance ga_op_ldist : Ldist ga_op.
Next Obligation.
    unfold mult; cbn.
    apply rdist.
Qed.
Local Program Instance ga_op_rdist : Rdist ga_op.
Next Obligation.
    unfold mult; cbn.
    apply ldist.
Qed.
Local Program Instance ga_op_mult_assoc : MultAssoc ga_op.
Next Obligation.
    unfold mult; cbn.
    symmetry; apply mult_assoc.
Qed.
Local Instance ga_op_one : One ga_op := {
    one := one
}.
Local Program Instance ga_op_mult_lid : MultLid ga_op.
Next Obligation.
    unfold mult; cbn.
    apply mult_rid.
Qed.
Local Program Instance ga_op_mult_rid : MultRid ga_op.
Next Obligation.
    unfold mult; cbn.
    apply mult_lid.
Qed.
Local Program Instance ga_op_scalar_lmult : ScalarLMult (cring_U F) ga_op.
Next Obligation.
    unfold mult; cbn.
    apply scalar_rmult.
Qed.
Local Program Instance ga_op_scalar_rmult : ScalarRMult (cring_U F) ga_op.
Next Obligation.
    unfold mult; cbn.
    apply scalar_lmult.
Qed.

Definition ga_op_algebra := make_algebra
    F
    (algebra_module (geometric_algebra B))
    ga_op_mult
    ga_op_ldist
    ga_op_rdist
    ga_op_mult_assoc
    ga_op_one
    ga_op_mult_lid
    ga_op_mult_rid
    ga_op_scalar_lmult
    ga_op_scalar_rmult
.

Definition ga_reverse_base1 (v : module_V V) := φ v : ga_op.

Lemma ga_reverse_base_plus : ∀ u v, ga_reverse_base1 (u + v) =
        ga_reverse_base1 u + ga_reverse_base1 v.
    intros u v.
    unfold ga_reverse_base1.
    apply vector_to_ga_plus.
Qed.

Lemma ga_reverse_base_scalar : ∀ a v,
        ga_reverse_base1 (a · v) = a · ga_reverse_base1 v.
    intros a v.
    unfold ga_reverse_base1.
    apply vector_to_ga_scalar.
Qed.

Definition ga_reverse_base2 := make_module_homomorphism
    F
    V
    (algebra_module ga_op_algebra)
    ga_reverse_base1
    ga_reverse_base_plus
    ga_reverse_base_scalar.

Lemma ga_reverse_base_contract : ∀ v,
        ga_reverse_base1 v * ga_reverse_base1 v = [B|] v v · 1.
    intros v.
    unfold ga_reverse_base1.
    unfold mult; cbn.
    apply ga_contract.
Qed.

Definition ga_reverse_base3 := make_to_ga
    B
    ga_op_algebra
    ga_reverse_base2
    ga_reverse_base_contract.

Definition ga_reverse_base
    := card_one_ex (geometric_universal B ga_reverse_base3).

Definition ga_reverse_homo := [ga_reverse_base|].
Definition ga_reverse := algebra_homo_f ga_reverse_homo : ga B → ga B.

Local Notation "a '†'" := (ga_reverse a) (at level 10).

Theorem ga_reverse_plus : ∀ u v, (u + v)† = u† + v†.
    apply (algebra_homo_plus _ _ ga_reverse_homo).
Qed.

Theorem ga_reverse_scalar : ∀ a v, (a · v)† = a · v†.
    apply (algebra_homo_scalar _ _ ga_reverse_homo).
Qed.

Theorem ga_reverse_mult : ∀ u v,
        (@mult _ (ga_mult B) u v)† = @mult _ (ga_mult B) (v†) (u†).
    apply (algebra_homo_mult _ _ ga_reverse_homo).
Qed.

Theorem ga_reverse_one : (@one _ (ga_one B))† = (@one _ (ga_one B)) .
    apply (algebra_homo_one _ _ ga_reverse_homo).
Qed.

Theorem ga_reverse_neg : ∀ v, (-v)† = -v†.
    apply (algebra_homo_neg ga_reverse_homo).
Qed.

Theorem ga_reverse_zero : 0† = 0.
    apply (algebra_homo_zero ga_reverse_homo).
Qed.

Theorem ga_reverse_of_scalar : ∀ a, (σ a)† = σ a.
    intros a.
    rewrite scalar_to_ga_one_scalar.
    rewrite ga_reverse_scalar.
    rewrite ga_reverse_one.
    reflexivity.
Qed.

Theorem ga_reverse_vector : ∀ v, (φ v)† = φ v.
    apply [|ga_reverse_base].
Qed.

Theorem ga_reverse_reverse : ∀ v, v†† = v.
    intros v.
    pose proof (ga_sum B v) as [l l_eq]; subst v.
    induction l as [|[a x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite ga_reverse_zero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    do 2 rewrite ga_reverse_plus.
    rewrite IHl; clear IHl.
    apply rplus.
    do 2 rewrite ga_reverse_scalar.
    apply f_equal.
    clear a l.
    induction x as [|v l].
    {
        cbn.
        do 2 rewrite ga_reverse_one.
        reflexivity.
    }
    cbn.
    do 2 rewrite ga_reverse_mult.
    rewrite IHl; clear IHl.
    apply rmult.
    do 2 rewrite ga_reverse_vector.
    reflexivity.
Qed.

End GeometricInvolutions.

Notation "a '∗'" := (ga_conjugate _ a) (at level 10) : ga_scope.
Notation "a '†'" := (ga_reverse _ a) (at level 10) : ga_scope.
