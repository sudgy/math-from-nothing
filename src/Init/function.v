(** Basic definitions and theorems relating to functions. *)

Require Import base_logic.

Theorem functional_ext2 {A B C} : ∀ f g : A → B → C, (∀ a b, f a b = g a b) →
    f = g.
Proof.
    intros f g eq.
    apply functional_ext.
    intros a.
    apply functional_ext.
    intros b.
    apply eq.
Qed.

Theorem func_eq {A} {B : A → Type} :
    ∀ f1 f2 : ∀ x, B x, f1 = f2 → ∀ x, f1 x = f2 x.
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

Definition identity {U} (x : U) := x.
Definition empty_function A B (H : A → False) := λ x : A, False_rect B (H x).

Class Injective {U V} (f : U → V) := {
    inj : ∀ a b, f a = f b → a = b
}.
Class Surjective {U V} (f : U → V) := {
    sur : ∀ y, ∃ x, f x = y
}.
Arguments sur {U V} f {Surjective}.
Class Bijective {U V} (f : U → V) := {
    bij_inj : Injective f;
    bij_sur : Surjective f;
}.

Global Instance bijective_injective {U V} (f : U → V) `{@Bijective U V f}
    : Injective f.
Proof.
    apply H.
Qed.
Global Instance bijective_surjective {U V} (f : U → V) `{@Bijective U V f}
    : Surjective f.
Proof.
    apply H.
Qed.

Global Instance identity_bijective {U} : Bijective (@identity U).
Proof.
    split; split.
    -   intros a b eq.
        exact eq.
    -   intros x.
        exists x.
        reflexivity.
Qed.
(** Keeping this seems to cause too many freezes *)
Global Remove Hints identity_bijective : typeclass_instances.

Global Instance inj_comp {U V W} (f : U → V) (g : V → W)
    `{@Injective U V f, @Injective V W g}
    : Injective (λ x, g (f x)).
Proof.
    split.
    intros a b eq.
    do 2 apply inj in eq.
    exact eq.
Qed.
Global Instance sur_comp {U V W} (f : U → V) (g : V → W)
    `{@Surjective U V f, @Surjective V W g}
    : Surjective (λ x, g (f x)).
Proof.
    split.
    intros z.
    destruct (sur g z) as [y y_eq].
    destruct (sur f y) as [x x_eq].
    exists x.
    rewrite x_eq.
    exact y_eq.
Qed.
Global Instance bij_comp {U V W} (f : U → V) (g : V → W)
    `{f_bij : @Bijective U V f, g_bij : @Bijective V W g}
    : Bijective (λ x, g (f x)).
Proof.
    destruct f_bij as [f_inj f_sur].
    destruct g_bij as [g_inj g_sur].
    split.
    -   apply inj_comp; assumption.
    -   apply sur_comp; assumption.
Qed.
(** Keeping these seems to cause too many freezes *)
Global Remove Hints inj_comp sur_comp bij_comp : typeclass_instances.

Theorem empty_inj {A B H} : Injective (empty_function A B H).
Proof.
    split.
    intros a.
    contradiction (H a).
Qed.
Theorem empty_sur {A B} : ∀ f : A → B, (B → False) → Surjective f.
    intros f BH.
    split.
    intros y.
    contradiction (BH y).
Qed.
Theorem empty_bij {A B H} : (B → False) → Bijective (empty_function A B H).
Proof.
    intros BH.
    split.
    -   apply empty_inj.
    -   apply (empty_sur _ BH).
Qed.

Theorem partition_principle {A B} :
    ∀ f : A → B, Surjective f → ∃ g : B → A, Injective g.
Proof.
    intros f f_sur.
    exists (λ b, ex_val (sur f b)).
    split.
    intros x y eq.
    rewrite_ex_val a a_eq.
    rewrite_ex_val b b_eq.
    subst.
    reflexivity.
Qed.

Theorem inj_neq {A B} (f : A → B) `{@Injective A B f} :
    ∀ a b, a ≠ b → f a ≠ f b.
Proof.
    intros a b neq contr.
    apply inj in contr.
    contradiction.
Qed.

Definition is_inverse {U V} (f : U → V) (g : V → U)
    := (∀ x, f (g x) = x) ∧ (∀ x, g (f x) = x).

Theorem inverse_symmetric {U V} : ∀ (f : U → V) (g : V → U),
    is_inverse f g → is_inverse g f.
Proof.
    intros f g f_inv.
    split; apply f_inv.
Qed.
Theorem inverse_eq1 {U V} : ∀ (f : U → V) (g : V → U), is_inverse f g →
    ∀ x, g (f x) = x.
Proof.
    intros f g inv.
    apply inv.
Qed.
Theorem inverse_eq2 {U V} : ∀ (f : U → V) (g : V → U), is_inverse f g →
    ∀ x, f (g x) = x.
Proof.
    intros f g inv x.
    apply inv.
Qed.

Theorem bijective_inverse_ex {U V} (f : U → V) `{Bijective (U := U) (V := V) f}:
    ∃ g, is_inverse f g.
Proof.
    exists (λ y, ex_val (sur f y)).
    split; intros eq.
    -   rewrite_ex_val a a_eq.
        exact a_eq.
    -   rewrite_ex_val a a_eq.
        apply inj in a_eq.
        exact a_eq.
Qed.

Theorem inverse_ex_bijective {A B} : ∀ (f : A → B) (g : B → A),
    is_inverse f g → Bijective f.
Proof.
    intros f g [fg gf].
    split; split.
    -   intros a b eq.
        apply (f_equal g) in eq.
        do 2 rewrite gf in eq.
        exact eq.
    -   intros y.
        exists (g y).
        apply fg.
Qed.

Definition bij_inv {U V} (f : U → V) `{f_bij : @Bijective U V f} :=
    ex_val (bijective_inverse_ex f).

Theorem bij_inv_inv {U V} : ∀ (f : U → V) `{@Bijective U V f},
    is_inverse f (bij_inv f).
Proof.
    intros f f_bij.
    unfold bij_inv.
    rewrite_ex_val g g_inv.
    exact g_inv.
Qed.

Theorem bij_inv_bij {U V} : ∀ (f : U → V) `{f_bij : @Bijective U V f},
    Bijective (bij_inv f).
Proof.
    intros f f_bij.
    pose proof (bij_inv_inv f) as g_inv.
    split; split.
    -   intros a b eq.
        unfold is_inverse in g_inv.
        rewrite <- (land g_inv a).
        rewrite <- (land g_inv b).
        rewrite eq.
        reflexivity.
    -   intros x.
        exists (f x).
        apply g_inv.
Qed.

Theorem bij_inv_eq1 {U V} : ∀ (f : U → V) `{Bijective U V f},
    ∀ x, bij_inv f (f x) = x.
Proof.
    intros f f_bij x.
    apply inverse_eq1.
    apply bij_inv_inv.
Qed.
Theorem bij_inv_eq2 {U V} : ∀ (f : U → V) `{Bijective U V f},
    ∀ x, f (bij_inv f x) = x.
Proof.
    intros f f_bij x.
    apply inverse_eq2.
    apply bij_inv_inv.
Qed.
