Require Import init.

Require Import category_base.

Require Import set.

(* begin show *)
Program Definition TYPE : Category := {|
    cat_U := Type;
    morphism A B := A → B;
    cat_compose A B C f g := λ x, f (g x);
    cat_id A := (@identity A);
|}.
(* end show *)

Theorem set_category_isomorphism : ∀ {A B : TYPE} (f : morphism A B),
    isomorphism f → Bijective f.
Proof.
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
    split; split.
    -   intros a b eq.
        apply (f_equal g) in eq.
        do 2 rewrite f_eq2 in eq.
        exact eq.
    -   intros y.
        exists (g y).
        apply f_eq1.
Qed.

(* begin show *)
Program Definition SINGLETON : Category := {|
    cat_U := singleton_type;
    morphism A B := singleton_type;
    cat_compose A B C f g := Single;
    cat_id A := Single;
|}.
(* end show *)
Next Obligation.
    apply singleton_type_eq.
Qed.
Next Obligation.
    apply singleton_type_eq.
Qed.
