Require Import init.

Require Import tensor_power_base.
Require Import module_category.
Require Import linear_grade_sum.

Require Import nat.
Require Import unordered_list.
Require Import plus_sum.
Require Import set.
Require Import card.

(** This file contains the definition of the algebra and the proofs that it
forms a vector space over the original field.
*)

(* begin hide *)
Section TensorAlgebra.

(* end hide *)
Context {F : CRing} (V : Module F).

(* begin hide *)
Let U := cring_U F.
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Let TP k := module_plus (tensor_power V k).
Let TZ k := module_zero (tensor_power V k).
Let TN k := module_neg (tensor_power V k).
Let TPC k := module_plus_comm (tensor_power V k).
Let TPA k := module_plus_assoc (tensor_power V k).
Let TPZ k := module_plus_lid (tensor_power V k).
Let TPN k := module_plus_linv (tensor_power V k).
Let TSM k := module_scalar (tensor_power V k).
Let TSMC k := module_scalar_comp (tensor_power V k).
Let TSMO k := module_scalar_id (tensor_power V k).
Let TSML k := module_scalar_ldist (tensor_power V k).
Let TSMR k := module_scalar_rdist (tensor_power V k).
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD TP TZ TN TPC
    TPA TPZ TPN TSM TSMC TSMO TSML TSMR.

Local Open Scope card_scope.

(* end hide *)
Definition tensor_algebra_base := grade_sum nat (tensor_power V).
Definition tensor_algebra_plus := grade_sum_plus nat (tensor_power V).
Definition tensor_algebra_zero := grade_sum_zero nat (tensor_power V).
Definition tensor_algebra_neg := grade_sum_neg nat (tensor_power V).
Definition tensor_algebra_plus_comm := grade_sum_plus_comm nat (tensor_power V).
Definition tensor_algebra_plus_assoc := grade_sum_plus_assoc nat (tensor_power V).
Definition tensor_algebra_plus_lid := grade_sum_plus_lid nat (tensor_power V).
Definition tensor_algebra_plus_linv := grade_sum_plus_linv nat (tensor_power V).
Definition tensor_algebra_scalar_mult := grade_sum_scalar_mult nat (tensor_power V).
Definition tensor_algebra_scalar_comp := grade_sum_scalar_comp nat (tensor_power V).
Definition tensor_algebra_scalar_id := grade_sum_scalar_id nat (tensor_power V).
Definition tensor_algebra_scalar_ldist := grade_sum_scalar_ldist nat (tensor_power V).
Definition tensor_algebra_scalar_rdist := grade_sum_scalar_rdist nat (tensor_power V).
Definition tensor_grade := grade_sum_grade nat (tensor_power V).
Definition power_to_tensor {k} A := single_to_grade_sum nat (tensor_power V) (k:=k) A.
Definition power_to_tensor_base {k} A := single_to_grade_sum_base nat (tensor_power V) (k:=k) A.

Let k_tensor k := module_V (tensor_power V k).

Local Existing Instances tensor_algebra_plus tensor_algebra_zero
    tensor_algebra_scalar_mult.

Theorem power_to_tensor_k_eq : ∀ k n (eq : k = n) (A : k_tensor k),
        power_to_tensor A =
        power_to_tensor (module_homo_f (tensor_power_nat_eq V eq) A).
    intros k n eq A.
    destruct eq.
    cbn.
    reflexivity.
Qed.
Theorem power_to_tensor_eq : ∀ k, ∀ (A B : k_tensor k),
        power_to_tensor A = power_to_tensor B → A = B.
    apply single_to_grade_sum_eq.
Qed.
Theorem power_to_tensor_plus : ∀ k (A B : k_tensor k),
        power_to_tensor (A + B) =
        power_to_tensor A + power_to_tensor B.
    apply single_to_grade_sum_plus.
Qed.
Theorem power_to_tensor_scalar : ∀ k α (A : k_tensor k),
        power_to_tensor (α · A) = α · power_to_tensor A.
    apply single_to_grade_sum_scalar.
Qed.
Lemma power_to_tensor_zero : ∀ k, (power_to_tensor (k := k) 0) = 0.
    apply single_to_grade_sum_zero.
Qed.
(* begin hide *)

End TensorAlgebra.
(* end hide *)
