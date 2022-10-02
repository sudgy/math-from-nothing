Require Import init.

Require Import set_base.
Require Import set_type.
Require Export relation.

#[universes(template)]
Record set_function_type (U V : Type) := make_set_function {
    domain : U → Prop;
    set_function : set_type domain → V;
}.
#[universes(template)]
Record bin_set_function_type (U V : Type) := make_bin_set_function {
    bin_domain : U → Prop;
    bin_set_function : set_type bin_domain → set_type bin_domain → V;
}.

Arguments make_set_function {U} {V}.
Arguments domain {U} {V}.
Arguments set_function {U} {V}.
Arguments make_bin_set_function {U} {V}.
Arguments bin_domain {U} {V}.
Arguments bin_set_function {U} {V}.

Notation "f ⟨ x ⟩" := (set_function f x) (at level 69).
Notation "f ⟨ x , y ⟩" := (bin_set_function f x y) (at level 69).

(* begin hide *)
Section FunctionOrder.

Open Scope set_scope.
(* end hide *)
Context {U V : Type}.
Definition func_le (f g : set_function_type U V) :=
    ∃ sub : (domain f ⊆ domain g),
        ∀ x : set_type (domain f),
            f⟨x⟩ = g⟨[[x|]|sub [x|] [|x]]⟩.

Lemma func_le_refl : ∀ f, func_le f f.
Proof.
    intros f.
    exists (@refl (U → Prop) subset _ (domain f)).
    intros [x x_in].
    apply f_equal.
    apply set_type_eq.
    reflexivity.
Qed.
Global Instance func_le_refl_class : Reflexive func_le := {
    refl := func_le_refl
}.

Lemma func_le_antisym : ∀ f g, func_le f g → func_le g f → f = g.
Proof.
    intros f g [f_sub_g fg] [g_sub_f gf]; cbn in *.
    assert (domain f = domain g) as sets_eq.
    {
        apply antisym; assumption.
    }
    destruct f as [f_dom f], g as [g_dom g]; cbn in *.
    subst.
    apply f_equal.
    apply functional_ext.
    intros x.
    rewrite fg.
    apply f_equal.
    apply set_type_eq.
    reflexivity.
Qed.
Global Instance func_le_antisym_class : Antisymmetric func_le := {
    antisym := func_le_antisym
}.

Lemma func_le_trans : ∀ f g h, func_le f g → func_le g h → func_le f h.
Proof.
    intros f g h [f_sub_g fg] [g_sub_h gh]; cbn in *.
    exists (trans f_sub_g g_sub_h); cbn.
    intros x.
    specialize (fg x).
    rewrite gh in fg.
    rewrite fg.
    apply f_equal.
    apply set_type_eq.
    reflexivity.
Qed.
Global Instance func_le_trans_class : Transitive func_le := {
    trans := func_le_trans
}.

Definition bin_func_le (f g : bin_set_function_type U V) :=
    ∃ sub : (bin_domain f ⊆ bin_domain g),
        ∀ x y : set_type (bin_domain f),
            f⟨x, y⟩ = g⟨[[x|]|sub [x|] [|x]], [[y|]|sub [y|] [|y]]⟩.

Lemma bin_func_le_refl : ∀ f, bin_func_le f f.
Proof.
    intros f.
    exists (refl _).
    intros x y.
    apply f_equal2; apply set_type_eq; reflexivity.
Qed.
Global Instance bin_func_le_refl_class : Reflexive bin_func_le := {
    refl := bin_func_le_refl
}.

Lemma bin_func_le_antisym : ∀ f g, bin_func_le f g → bin_func_le g f → f = g.
Proof.
    intros f g [f_sub_g fg] [g_sub_f gf]; cbn in *.
    assert (bin_domain f = bin_domain g) as sets_eq.
    {
        apply antisym; assumption.
    }
    destruct f as [f_dom f], g as [g_dom g]; cbn in *.
    subst.
    apply f_equal.
    apply functional_ext.
    intros x.
    apply functional_ext.
    intros y.
    rewrite fg.
    apply f_equal2; apply set_type_eq; reflexivity.
Qed.
Global Instance bin_func_le_antisym_class : Antisymmetric bin_func_le := {
    antisym := bin_func_le_antisym
}.

Lemma bin_func_le_trans :
    ∀ f g h, bin_func_le f g → bin_func_le g h → bin_func_le f h.
Proof.
    intros g f h [f_sub_g fg] [g_sub_h gh]; cbn in *.
    exists (trans f_sub_g g_sub_h); cbn.
    intros x y.
    specialize (fg x y).
    rewrite gh in fg.
    rewrite fg; cbn.
    apply f_equal2; apply set_type_eq; reflexivity.
Qed.
Global Instance bin_func_le_trans_class : Transitive bin_func_le := {
    trans := bin_func_le_trans
}.
(* begin hide *)
End FunctionOrder.
(* end hide *)
