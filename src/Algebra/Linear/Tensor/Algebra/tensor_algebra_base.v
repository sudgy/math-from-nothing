Require Import init.

(*Require Import tensor_algebra_traditional_universal.*)
Require Import tensor_algebra_direct_universal.

Require Export algebra_category.
Require Import category_initterm.

Section TensorAlgebraBase.

Context {F : CRingObj} (V : ModuleObj F).
Let U := cring_U F.

Definition to_tensor_algebra := ex_val (tensor_algebra_ex V).
Definition tensor_algebra := (to_algebra_algebra V) to_tensor_algebra.
Definition tensor_algebra_ex := ex_proof (tensor_algebra_ex V).
Definition vector_to_tensor_homo := (to_algebra_homo V) to_tensor_algebra.
Definition vector_to_tensor := module_homo_f vector_to_tensor_homo.

Theorem tensor_algebra_universal : @initial (TO_ALGEBRA V) to_tensor_algebra.
Proof.
    apply tensor_algebra_ex.
Qed.

Theorem vector_to_tensor_plus : ∀ u v : module_V V, vector_to_tensor (u + v) =
    vector_to_tensor u + vector_to_tensor v.
Proof.
    apply module_homo_plus.
Qed.
Theorem vector_to_tensor_scalar : ∀ a (v : module_V V), vector_to_tensor (a · v)
    = a · vector_to_tensor v.
Proof.
    apply module_homo_scalar.
Qed.
Theorem vector_to_tensor_zero : vector_to_tensor (zero (U := module_V V)) = 0.
Proof.
    apply module_homo_zero.
Qed.

Definition scalar_to_tensor (a : U) : algebra_V tensor_algebra := a · 1.

Theorem scalar_to_tensor_plus : ∀ a b,
    scalar_to_tensor (a + b) = scalar_to_tensor a + scalar_to_tensor b.
Proof.
    intros a b.
    unfold scalar_to_tensor.
    apply scalar_rdist.
Qed.

Theorem scalar_to_tensor_zero : scalar_to_tensor 0 = 0.
Proof.
    unfold scalar_to_tensor.
    apply scalar_lanni.
Qed.

Theorem scalar_to_tensor_mult : ∀ a b,
    scalar_to_tensor (a * b) = scalar_to_tensor a * scalar_to_tensor b.
Proof.
    intros a b.
    unfold scalar_to_tensor.
    rewrite scalar_lmult, scalar_rmult.
    rewrite scalar_comp, mult_lid.
    reflexivity.
Qed.

Theorem scalar_to_tensor_scalar : ∀ a A, scalar_to_tensor a * A = a · A.
Proof.
    intros a A.
    unfold scalar_to_tensor.
    rewrite scalar_lmult.
    rewrite mult_lid.
    reflexivity.
Qed.

Theorem scalar_to_tensor_one : scalar_to_tensor 1 = 1.
Proof.
    unfold scalar_to_tensor.
    apply scalar_id.
Qed.

Theorem scalar_to_tensor_comm : ∀ a A,
    scalar_to_tensor a * A = A * scalar_to_tensor a.
Proof.
    intros a A.
    unfold scalar_to_tensor.
    rewrite scalar_lmult, scalar_rmult.
    rewrite mult_lid, mult_rid.
    reflexivity.
Qed.

End TensorAlgebraBase.

Arguments vector_to_tensor {F V}.
