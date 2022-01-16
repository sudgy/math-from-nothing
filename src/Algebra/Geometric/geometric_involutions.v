Require Import init.

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

End GeometricInvolutions.
