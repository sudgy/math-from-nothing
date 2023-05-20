Require Import init.

Require Import category_base.

Program Definition SINGLETON : Category := {|
    cat_U := singleton_type;
    morphism A B := singleton_type;
    cat_compose A B C f g := Single;
    cat_id A := Single;
|}.
Next Obligation.
    apply singleton_type_eq.
Qed.
Next Obligation.
    apply singleton_type_eq.
Qed.

Program Definition TYPE : Category := {|
    cat_U := Type;
    morphism A B := A → B;
    cat_compose A B C f g := λ x, f (g x);
    cat_id A := (@identity A);
|}.

Theorem set_category_isomorphism : ∀ {A B : TYPE} (f : morphism A B),
    is_isomorphism f → Bijective f.
Proof.
    intros A B f [g [g_eq1 g_eq2]].
    apply (inverse_ex_bijective f g).
    split; apply func_eq; assumption.
Qed.
