Require Import init.

Require Import set_base.
Require Import set_type.
Require Export relation.

#[universes(template)]
Record bin_set_function_type (U V : Type) := make_bin_set_function {
    bin_domain : U → Prop;
    bin_set_function : set_type bin_domain → set_type bin_domain → V;
}.

Arguments make_bin_set_function {U} {V}.
Arguments bin_domain {U} {V}.
Arguments bin_set_function {U} {V}.

Notation "f ⟨ x , y ⟩" := (bin_set_function f x y) (at level 69).

(* begin hide *)
Section FunctionOrder.

Local Open Scope set_scope.
(* end hide *)
Context {U V : Type}.

Definition bin_func_le (f g : bin_set_function_type U V) :=
    bin_domain f ⊆ bin_domain g ⋏ λ sub,
        ∀ x y : set_type (bin_domain f),
            f⟨x, y⟩ = g⟨[[x|]|sub [x|] [|x]], [[y|]|sub [y|] [|y]]⟩.

Global Instance bin_func_le_refl : Reflexive bin_func_le.
Proof.
    split.
    intros f.
    split with (refl _).
    intros x y.
    apply f_equal2; symmetry; apply set_type_simpl.
Qed.

Global Instance bin_func_le_antisym : Antisymmetric bin_func_le.
Proof.
    split.
    intros f g [f_sub_g fg] [g_sub_f gf]; cbn in *.
    pose proof (antisym f_sub_g g_sub_f) as sets_eq.
    destruct f as [f_dom f], g as [g_dom g]; cbn in *.
    subst g_dom.
    apply f_equal.
    apply functional_ext.
    intros x.
    apply functional_ext.
    intros y.
    rewrite fg.
    apply f_equal2; apply set_type_simpl.
Qed.

Global Instance bin_func_le_trans : Transitive bin_func_le.
Proof.
    split.
    intros g f h [f_sub_g fg] [g_sub_h gh]; cbn in *.
    split with (trans f_sub_g g_sub_h); cbn.
    intros x y.
    rewrite (fg x y).
    rewrite gh; cbn.
    apply f_equal2; rewrite set_type_eq2; reflexivity.
Qed.
(* begin hide *)

End FunctionOrder.
(* end hide *)
