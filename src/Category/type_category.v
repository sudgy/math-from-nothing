Require Import init.

Require Import category_base.

Require Import set.

Program Instance TYPE : Category := {
    cat_U := Type;
    cat_morphism A B := A → B;
    cat_compose A B C f g := λ x, f (g x);
    cat_id A := (@identity A);
}.

Theorem set_category_isomorphism : ∀ {A B} (f : cat_morphism TYPE A B),
        isomorphism f → bijective f.
    intros A B f [g [g_eq1 g_eq2]].
    cbn in *.
    assert (∀ x, f (g x) = x) as f_eq1.
    {
        intros x.
        exact (func_eq _ _ g_eq1 x).
    }
    assert (∀ x, g (f x) = x) as f_eq2.
    {
        intros x.
        exact (func_eq _ _ g_eq2 x).
    }
    split.
    -   intros a b eq.
        apply (f_equal g) in eq.
        do 2 rewrite f_eq2 in eq.
        exact eq.
    -   intros y.
        exists (g y).
        apply f_eq1.
Qed.
