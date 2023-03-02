Require Import init.

Require Import list_perm.
Require Export unordered_list_base.

Require Import equivalence.

Unset Keyed Unification.

Lemma ulist_image_wd A B : ∀ (f : A → B) a b, list_permutation a b →
    to_equiv (ulist_equiv B) (list_image a f) =
    to_equiv (ulist_equiv B) (list_image b f).
Proof.
    intros a b f ab.
    equiv_simpl.
    apply list_image_perm.
    exact ab.
Qed.
Definition ulist_image {A B} (l : ulist A) (f : A → B) :=
    unary_op (E := ulist_equiv A) (ulist_image_wd A B f) l.

Theorem ulist_image_end {A B : Type} : ∀ f : A → B,
    ulist_image ulist_end f = ulist_end.
Proof.
    intros f.
    unfold ulist_end, ulist_image; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_image_add {A B : Type} : ∀ a l (f : A → B),
    ulist_image (a ::: l) f = f a ::: ulist_image l f.
Proof.
    intros a l f.
    equiv_get_value l.
    unfold ulist_image, ulist_add; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_image_conc {A B : Type} : ∀ a b (f : A → B),
    ulist_image (a +++ b) f = ulist_image a f +++ ulist_image b f.
Proof.
    intros a b f.
    equiv_get_value a b.
    unfold ulist_image, ulist_conc; equiv_simpl.
    rewrite list_image_conc.
    apply list_perm_refl.
Qed.

Theorem ulist_image_comp {A B C : Type} :
    ∀ (l : ulist A) (f : A → B) (g : B → C),
    ulist_image (ulist_image l f) g = ulist_image l (λ x, g (f x)).
Proof.
    intros l f g.
    equiv_get_value l.
    unfold ulist_image; equiv_simpl.
    rewrite list_image_comp.
    apply list_perm_refl.
Qed.
