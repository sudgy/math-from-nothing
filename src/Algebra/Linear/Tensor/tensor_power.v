Require Import init.

Require Import tensor_product_universal.
Require Import tensor_product_isomorphisms.
Require Import tensor_product_assoc.
Require Import module_category.

Require Import nat.

Section TensorPower.

Local Arguments cat_compose : simpl never.

Infix "⊗" := tensor_product.

Fixpoint tensor_power {F : CRing} (V : Module F) (n : nat) :=
    match n with
    | nat_zero => cring_module F
    | nat_suc n' => V ⊗ tensor_power V n'
    end.

Definition tensor_power_nat_eq {m n : nat} {F : CRing} (V : Module F) (eq : m = n)
        : ModuleHomomorphism (tensor_power V m) (tensor_power V n).
    rewrite eq.
    exact 𝟙.
Defined.

Fixpoint tensor_power_mult1 {F : CRing} (V : Module F) (n : nat)
    : ModuleHomomorphism ((tensor_power V n) ⊗ V) (tensor_power V (nat_suc n))
:=
    match n with
    | nat_zero => tensor_product_comm_homo (cring_module F) V
    | nat_suc n' =>
        tensor_product_riso_homo V
            (tensor_power V n' ⊗ V)
            (tensor_power V (nat_suc n'))
            (tensor_power_mult1 V n') ∘
        tensor_product_assoc_inv_homo V (tensor_power V n') V
    end.

Fixpoint tensor_power_mult {F : CRing} (V : Module F) (m n : nat)
    : ModuleHomomorphism
        (tensor_power V m ⊗ tensor_power V n)
        (tensor_power V (m + n))
:=
    match n with
    | nat_zero =>
        tensor_power_nat_eq V (Logic.eq_sym (plus_rid m)) ∘
        tensor_product_rid_homo (tensor_power V m)
    | nat_suc n' =>
        tensor_power_mult V (nat_suc m) n' ∘
        tensor_product_liso_homo
            (tensor_power V m ⊗ V)
            (tensor_power V (nat_suc m))
            (tensor_power V n')
            (tensor_power_mult1 V m) ∘
        tensor_product_assoc_homo
            (tensor_power V m)
            V
            (tensor_power V n')
    end.

Context {F : CRing} (V : Module F).

Theorem tensor_power_mult1_iso :
        ∀ n, isomorphism (C0 := MODULE F) (tensor_power_mult1 V n).
    intros n.
    induction n.
    -   cbn.
        apply tensor_product_comm_iso.
    -   cbn.
        apply compose_isomorphism.
        +   apply tensor_product_riso_iso.
            exact IHn.
        +   apply tensor_product_assoc_inv_iso.
Qed.

Theorem tensor_power_mult_iso :
        ∀ m n, isomorphism (C0 := MODULE F) (tensor_power_mult V m n).
    intros m n.
    revert m.
    induction n; intros.
    -   cbn.
        apply compose_isomorphism.
        +   unfold tensor_power_nat_eq, Logic.eq_rect_r, Logic.eq_rect.
            destruct (Logic.eq_sym _).
            apply id_isomorphism.
        +   apply tensor_product_rid_iso.
    -   cbn.
        repeat apply compose_isomorphism.
        +   exact (IHn (nat_suc m)).
        +   apply tensor_product_liso_iso.
            apply tensor_power_mult1_iso.
        +   apply tensor_product_assoc_iso.
Qed.

End TensorPower.
