Require Import init.

Require Import set_base.
Require Import set_type.
Require Export relation.
Require Import nat.

Theorem func_eq {A B} : ∀ f1 f2 : A → B, f1 = f2 → ∀ x, f1 x = f2 x.
Proof.
    intros f1 f2 eq x.
    rewrite eq; reflexivity.
Qed.

Theorem f_eq_iff {A B} : ∀ {f : A → B}, (∀ a b, f a = f b → a = b) →
    ∀ a b, f a = f b ↔ a = b.
Proof.
    intros f f_eq a b.
    split.
    -   apply f_eq.
    -   intros eq; subst; reflexivity.
Qed.

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

Definition injective {U V} (f : U → V) := ∀ a b, f a = f b → a = b.
Definition surjective {U V} (f : U → V) := ∀ y, ∃ x, f x = y.
Definition bijective {U V} (f : U → V) := injective f ∧ surjective f.

Definition identity {U} (x : U) := x.
Fixpoint iterate_func {U} (f : U → U) n :=
    match n with
    | nat_zero => identity
    | nat_suc n' => λ x, f (iterate_func f n' x)
    end.

Theorem identity_injective {U} : injective (@identity U).
Proof.
    intros a b eq.
    exact eq.
Qed.
Theorem identity_surjective {U} : surjective (@identity U).
Proof.
    intros x.
    exists x.
    reflexivity.
Qed.
Theorem identity_bijective {U} : bijective (@identity U).
Proof.
    split.
    -   exact identity_injective.
    -   exact identity_surjective.
Qed.

Definition is_inverse {U V} (f : U → V) (g : V → U) := ∀ x y, f x = y ↔ g y = x.
Theorem inverse_symmetric {U V} : ∀ (f : U → V) (g : V → U),
    is_inverse f g → is_inverse g f.
Proof.
    intros f g f_inv.
    split; apply f_inv.
Qed.
Theorem inverse_eq1 {U V} : ∀ (f : U → V) (g : V → U), is_inverse f g →
    ∀ x, g (f x) = x.
Proof.
    intros f g inv x.
    apply (inv x (f x)).
    reflexivity.
Qed.
Theorem inverse_eq2 {U V} : ∀ (f : U → V) (g : V → U), is_inverse f g →
    ∀ x, f (g x) = x.
Proof.
    intros f g inv x.
    apply (inv (g x) x).
    reflexivity.
Qed.

Theorem bijective_inverse_ex {U V} : ∀ f : U → V, bijective f →
    ∃ g, is_inverse f g.
Proof.
    intros f [f_inj f_sur].
    exists (λ y, ex_val (f_sur y)).
    split.
    -   intros eq.
        unpack_ex_val a a_ex a_eq; rewrite a_ex.
        rewrite <- eq in a_eq.
        apply f_inj.
        exact a_eq.
    -   unpack_ex_val a a_ex a_eq; rewrite a_ex.
        intros eq.
        subst x y.
        reflexivity.
Qed.
Definition bij_inv {U V} (f : U → V) (f_bij : bijective f) :=
    ex_val (bijective_inverse_ex f f_bij).
Theorem bij_inv_inv {U V} : ∀ (f : U → V) f_bij, is_inverse f (bij_inv f f_bij).
Proof.
    intros f f_bij.
    unfold bij_inv.
    unpack_ex_val g g_ex g_inv; rewrite g_ex.
    exact g_inv.
Qed.
Theorem bij_inv_bij {U V} : ∀ (f : U → V) f_bij, bijective (bij_inv f f_bij).
Proof.
    intros f [f_inv f_sur].
    unfold bij_inv.
    unpack_ex_val g g_ex g_inv; rewrite g_ex.
    split.
    -   intros a b eq.
        unfold is_inverse in g_inv.
        pose proof (g_inv (g b) a) as [C eq1]; clear C; specialize (eq1 eq).
        symmetry in eq.
        pose proof (g_inv (g a) b) as [C eq2]; clear C; specialize (eq2 eq).
        rewrite <- eq1.
        rewrite <- eq2 at 2.
        rewrite eq.
        reflexivity.
    -   intros x.
        exists (f x).
        apply g_inv.
        reflexivity.
Qed.

Theorem inj_comp {U V W} : ∀ (f : U → V) (g : V → W),
    injective f → injective g → injective (λ x, g (f x)).
Proof.
    intros f g f_inj g_inj a b eq.
    apply g_inj in eq.
    apply f_inj in eq.
    exact eq.
Qed.
Theorem sur_comp {U V W} : ∀ (f : U → V) (g : V → W),
    surjective f → surjective g → surjective (λ x, g (f x)).
Proof.
    intros f g f_sur g_sur z.
    destruct (g_sur z) as [y y_eq].
    destruct (f_sur y) as [x x_eq].
    exists x.
    rewrite x_eq.
    exact y_eq.
Qed.
Theorem bij_comp {U V W} : ∀ (f : U → V) (g : V → W),
    bijective f → bijective g → bijective (λ x, g (f x)).
Proof.
    intros f g [f_inj f_sur] [g_inj g_sur].
    split.
    -   apply inj_comp; assumption.
    -   apply sur_comp; assumption.
Qed.

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

Definition empty_function A B (H : A → False) := λ x : A, False_rect B (H x).

Theorem empty_inj {A B H} : injective (empty_function A B H).
Proof.
    intros a.
    contradiction (H a).
Qed.
Theorem empty_bij {A B H} : (B → False) → bijective (empty_function A B H).
Proof.
    intros BH.
    split; try apply empty_inj.
    intros b.
    contradiction (BH b).
Qed.

Theorem partition_principle {A B} :
    (∃ f : A → B, surjective f) → ∃ f : B → A, injective f.
Proof.
    intros [f f_sur].
    unfold surjective in f_sur.
    exists (λ b, ex_val (f_sur b)).
    intros x y eq.
    unfold ex_val in eq.
    destruct (ex_to_type (f_sur x)); cbn in *.
    destruct (ex_to_type (f_sur y)); cbn in *.
    subst.
    reflexivity.
Qed.

Theorem inverse_ex_bijective {A B} : ∀ (f : A → B) (g : B → A),
    (∀ x, f (g x) = x) → (∀ x, g (f x) = x) → bijective f.
Proof.
    intros f g fg gf.
    split.
    -   intros a b eq.
        apply (f_equal g) in eq.
        do 2 rewrite gf in eq.
        exact eq.
    -   intros y.
        exists (g y).
        rewrite fg.
        reflexivity.
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
