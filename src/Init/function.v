(** Basic definitions and theorems relating to functions. *)

Require Import base_logic.

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

Definition identity {U} (x : U) := x.
Definition empty_function A B (H : A → False) := λ x : A, False_rect B (H x).

Definition injective {U V} (f : U → V) := ∀ a b, f a = f b → a = b.
Definition surjective {U V} (f : U → V) := ∀ y, ∃ x, f x = y.
Definition bijective {U V} (f : U → V) := injective f ∧ surjective f.

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

Theorem empty_inj {A B H} : injective (empty_function A B H).
Proof.
    intros a.
    contradiction (H a).
Qed.
Theorem empty_sur {A B} : ∀ f : A → B, (B → False) → surjective f.
    intros f BH y.
    contradiction (BH y).
Qed.
Theorem empty_bij {A B H} : (B → False) → bijective (empty_function A B H).
Proof.
    intros BH.
    split.
    -   apply empty_inj.
    -   apply (empty_sur _ BH).
Qed.

Theorem partition_principle {A B} :
    ∀ f : A → B, surjective f → ∃ g : B → A, injective g.
Proof.
    intros f f_sur.
    unfold surjective in f_sur.
    exists (λ b, ex_val (f_sur b)).
    intros x y eq.
    rewrite_ex_val a a_eq.
    rewrite_ex_val b b_eq.
    subst.
    reflexivity.
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

Theorem bijective_inverse_ex {U V} : ∀ f : U → V, bijective f →
    ∃ g, is_inverse f g.
Proof.
    intros f [f_inj f_sur].
    exists (λ y, ex_val (f_sur y)).
    split; intros eq.
    -   rewrite_ex_val a a_eq.
        exact a_eq.
    -   rewrite_ex_val a a_eq.
        apply f_inj in a_eq.
        exact a_eq.
Qed.

Theorem inverse_ex_bijective {A B} : ∀ (f : A → B) (g : B → A),
    is_inverse f g → bijective f.
Proof.
    intros f g [fg gf].
    split.
    -   intros a b eq.
        apply (f_equal g) in eq.
        do 2 rewrite gf in eq.
        exact eq.
    -   intros y.
        exists (g y).
        apply fg.
Qed.

Definition bij_inv {U V} (f : U → V) (f_bij : bijective f) :=
    ex_val (bijective_inverse_ex f f_bij).

Theorem bij_inv_inv {U V} : ∀ (f : U → V) f_bij, is_inverse f (bij_inv f f_bij).
Proof.
    intros f f_bij.
    unfold bij_inv.
    rewrite_ex_val g g_inv.
    exact g_inv.
Qed.

Theorem bij_inv_bij {U V} : ∀ (f : U → V) f_bij, bijective (bij_inv f f_bij).
Proof.
    intros f f_bij.
    pose proof (bij_inv_inv f f_bij) as g_inv.
    split.
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
