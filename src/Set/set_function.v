Require Import init.

Require Import set_base.

Definition image {U V} (f : U → V) := λ y, ∃ x, y = f x.
Definition image_under {U V} (f : U → V) (S : U → Prop)
    := λ y, ∃ x, S x ∧ y = f x.
Definition inverse_image {U V} (f : U → V) (T : V → Prop)
    := λ x, T (f x).

Theorem image_under_in {U V} : ∀ (f : U → V) (S : U → Prop) x,
    S x → image_under f S (f x).
Proof.
    intros f S x Sx.
    exists x.
    split.
    -   exact Sx.
    -   reflexivity.
Qed.

Theorem image_inverse_sub {U V} : ∀ (f : U → V) (S : V → Prop),
    image_under f (inverse_image f S) ⊆ S.
Proof.
    intros f S y [x [x_in eq]].
    subst y.
    exact x_in.
Qed.

Theorem image_sub {U V} :
    ∀ (f : U → V) S T, S ⊆ T → image_under f S ⊆ image_under f T.
Proof.
    intros f S T sub y [x [Sx y_eq]].
    subst y.
    apply sub in Sx.
    apply image_under_in.
    exact Sx.
Qed.

Theorem inverse_complement {U V} : ∀ (f : U → V) S,
    inverse_image f (𝐂 S) = 𝐂 (inverse_image f S).
Proof.
    intros f S.
    reflexivity.
Qed.

Theorem inverse_image_bij_inv {U V} : ∀ S (f : U → V) `{@Bijective U V f},
    (inverse_image (bij_inv f) S) = image_under f S.
Proof.
    intros S f f_bij.
    apply antisym.
    -   intros y y_in.
        unfold inverse_image in y_in.
        exists (bij_inv f y).
        split; [>exact y_in|].
        symmetry; apply inverse_eq2.
        apply bij_inv_inv.
    -   intros y [x [Sx y_eq]]; subst y.
        unfold inverse_image.
        rewrite inverse_eq1 by apply bij_inv_inv.
        exact Sx.
Qed.

Theorem bij_inverse_image {U V} : ∀ S (f : U → V),
    Bijective f → image_under f (inverse_image f S) = S.
Proof.
    intros S f f_bij.
    apply antisym; [>apply image_inverse_sub|].
    intros y Sy.
    exists (bij_inv f y).
    unfold inverse_image.
    rewrite inverse_eq2 by apply bij_inv_inv.
    split.
    -   exact Sy.
    -   reflexivity.
Qed.

Theorem inj_inverse_image {U V} : ∀ S (f : U → V),
    Injective f → inverse_image f (image_under f S) = S.
Proof.
    intros S f f_inj.
    apply antisym.
    -   intros x [y [Sy eq]].
        apply inj in eq.
        subst.
        exact Sy.
    -   intros x Sx.
        apply image_under_in.
        exact Sx.
Qed.
