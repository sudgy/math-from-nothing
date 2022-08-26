Require Import init.

Require Import set_base.
Require Import set_type.
Require Export relation.
Require Import nat.

Definition image {U V} (f : U → V) := λ y, ∃ x, y = f x.
Definition image_under {U V} (f : U → V) (S : U → Prop)
    := λ y, ∃ x, S x ∧ y = f x.
Definition inverse_image {U V} (f : U → V) (T : V → Prop)
    := λ x, T (f x).

Theorem image_inverse_sub {U V} : ∀ (f : U → V) S,
    subset (image_under f (inverse_image f S)) S.
Proof.
    intros f S y [x [x_in eq]].
    subst y.
    exact x_in.
Qed.

Theorem image_sub {U V} :
    ∀ (f : U → V) S T, (S ⊆ T → image_under f S ⊆ image_under f T)%set.
Proof.
    intros f S T sub y [x [Sx y_eq]].
    subst y.
    apply sub in Sx.
    exists x.
    split; trivial.
Qed.

Theorem inverse_complement {U V} : ∀ (f : U → V) S,
    inverse_image f (complement S) = complement (inverse_image f S).
Proof.
    intros f S.
    reflexivity.
Qed.

Fixpoint iterate_func {U} (f : U → U) n :=
    match n with
    | nat_zero => identity
    | nat_suc n' => λ x, f (iterate_func f n' x)
    end.

Theorem inverse_image_bij_inv {U V} : ∀ S (f : U → V) f_bij,
    (inverse_image (bij_inv f f_bij) S) = image_under f S.
Proof.
    intros S f f_bij.
    apply antisym.
    -   intros y y_in.
        unfold inverse_image in y_in.
        exists (bij_inv f f_bij y).
        split; try exact y_in.
        rewrite inverse_eq2 by apply bij_inv_inv.
        reflexivity.
    -   intros y [x [Sx y_eq]]; subst y.
        unfold inverse_image.
        rewrite inverse_eq1 by apply bij_inv_inv.
        exact Sx.
Qed.

Theorem bij_inverse_image {U V} : ∀ S (f : U → V),
    bijective f → image_under f (inverse_image f S) = S.
Proof.
    intros S f f_bij.
    apply antisym.
    -   intros y [x [Sfx y_eq]]; subst y.
        exact Sfx.
    -   intros y Sy.
        exists (bij_inv f f_bij y).
        unfold inverse_image.
        rewrite inverse_eq2 by apply bij_inv_inv.
        split; trivial.
Qed.

Theorem inverse_image_bij {U V} : ∀ S (f : U → V),
    injective f → inverse_image f (image_under f S) = S.
Proof.
    intros S f f_bij.
    apply antisym.
    -   intros x [y [Sy eq]].
        apply f_bij in eq.
        subst.
        exact Sy.
    -   intros x Sx.
        exists x.
        split; trivial.
Qed.


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
