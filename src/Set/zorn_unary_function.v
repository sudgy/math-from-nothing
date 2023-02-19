Require Import init.

Require Import set_base.
Require Import set_type.
Require Export relation.

#[universes(template)]
Record set_function_type (U V : Type) := make_set_function {
    domain : U → Prop;
    set_function : set_type domain → V;
}.

Arguments make_set_function {U} {V}.
Arguments domain {U} {V}.
Arguments set_function {U} {V}.

Notation "f ⟨ x ⟩" := (set_function f x) (at level 69).

(* begin hide *)
Section FunctionOrder.

Local Open Scope set_scope.
(* end hide *)
Context {U V : Type}.
Definition func_le (f g : set_function_type U V) :=
    domain f ⊆ domain g ⋏ λ sub,
        ∀ x : set_type (domain f),
            f⟨x⟩ = g⟨[[x|]|sub [x|] [|x]]⟩.

Global Instance func_le_refl : Reflexive func_le.
Proof.
    split.
    intros f.
    split with (refl _).
    intros [x x_in]; cbn.
    apply f_equal.
    rewrite set_type_eq2.
    reflexivity.
Qed.

Global Instance func_le_antisym : Antisymmetric func_le.
Proof.
    split.
    intros f g [f_sub_g fg] [g_sub_f gf]; cbn in *.
    pose proof (antisym f_sub_g g_sub_f) as set_eq.
    destruct f as [f_dom f], g as [g_dom g]; cbn in *.
    subst g_dom.
    apply f_equal.
    apply functional_ext.
    intros x.
    rewrite fg.
    apply f_equal.
    apply set_type_simpl.
Qed.

Global Instance func_le_trans : Transitive func_le.
Proof.
    split.
    intros f g h [f_sub_g fg] [g_sub_h gh]; cbn in *.
    split with (trans f_sub_g g_sub_h); cbn.
    intros x.
    rewrite fg.
    rewrite gh; cbn.
    apply f_equal.
    rewrite set_type_eq2.
    reflexivity.
Qed.
(* begin hide *)

End FunctionOrder.
(* end hide *)
