Require Import init.

Require Import set.
Require Import card.

Require Export exterior_construct.
Require Import exterior_universal.
Require Import module_category.
Require Import algebra_category.

Section ExteriorOutermorphism.

Context {F : CRing} (V1 V2 : Module F).

Let V1P := module_plus V1.
Let V1S := module_scalar V1.

Existing Instances V1P V1S.

Let E1P := ext_plus V1.
Let E1Z := ext_zero V1.
Let E1N := ext_neg V1.
Let E1M := ext_mult V1.
Let E1O := ext_one V1.
Let E1S := ext_scalar V1.

Existing Instances E1P E1Z E1N E1M E1O E1S.

Let E2P := ext_plus V2.
Let E2Z := ext_zero V2.
Let E2N := ext_neg V2.
Let E2M := ext_mult V2.
Let E2O := ext_one V2.
Let E2S := ext_scalar V2.

Existing Instances E2P E2Z E2N E2M E2O E2S.

Variable f : ModuleHomomorphism V1 V2.

Definition outermorphism_base1 x := vector_to_ext V2 (module_homo_f f x) : ext V2.

Lemma outermorphism_base_plus : ∀ u v, outermorphism_base1 (u + v) =
        outermorphism_base1 u + outermorphism_base1 v.
    intros u v.
    unfold outermorphism_base1.
    rewrite (module_homo_plus _ _ f).
    apply vector_to_ext_plus.
Qed.

Lemma outermorphism_base_scalar : ∀ a v, outermorphism_base1 (a · v) =
        a · outermorphism_base1 v.
    intros a v.
    unfold outermorphism_base1.
    rewrite (module_homo_scalar _ _ f).
    apply vector_to_ext_scalar.
Qed.

Definition outermorphism_base2 := make_module_homomorphism
    F
    V1
    (algebra_module (exterior_algebra V2))
    outermorphism_base1
    outermorphism_base_plus
    outermorphism_base_scalar.

Lemma outermorphism_base2_alternating :
        ∀ v, 0 = outermorphism_base1 v * outermorphism_base1 v.
    intros v.
    unfold outermorphism_base1.
    apply ext_alternating.
Qed.

Definition outermorphism_base3 := make_to_ext
    V1
    (exterior_algebra V2)
    outermorphism_base2
    outermorphism_base2_alternating.

Definition outermorphism_base
    := card_one_ex (exterior_universal V1 outermorphism_base3).

Definition outermorphism_homo := [outermorphism_base|].
Definition outermorphism := algebra_homo_f outermorphism_homo : ext V1 → ext V2.

Theorem outermorphism_eq : ∀ v, outermorphism (vector_to_ext V1 v) =
        vector_to_ext V2 (module_homo_f f v).
    apply [|outermorphism_base].
Qed.

Theorem outermorphism_plus :
        ∀ u v, outermorphism (u + v) = outermorphism u + outermorphism v.
    apply (algebra_homo_plus _ _ outermorphism_homo).
Qed.

Theorem outermorphism_scalar :
        ∀ a v, outermorphism (a · v) = a · outermorphism v.
    apply (algebra_homo_scalar _ _ outermorphism_homo).
Qed.

Theorem outermorphism_mult :
        ∀ u v, outermorphism (u * v) = outermorphism u * outermorphism v.
    apply (algebra_homo_mult _ _ outermorphism_homo).
Qed.

Theorem outermorphism_one : outermorphism 1 = 1.
    apply (algebra_homo_one _ _ outermorphism_homo).
Qed.

Theorem outermorphism_neg : ∀ v, outermorphism (-v) = -outermorphism v.
    apply (algebra_homo_neg outermorphism_homo).
Qed.

Theorem outermorphism_zero : outermorphism 0 = 0.
    apply (algebra_homo_zero outermorphism_homo).
Qed.

End ExteriorOutermorphism.

Arguments outermorphism {F V1 V2}.
