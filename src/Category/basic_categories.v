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

Theorem set_category_monomorphism : ∀ {A B : TYPE} (f : morphism A B),
    monomorphism f ↔ Injective f.
Proof.
    intros A B f.
    split.
    -   intros f_mono.
        split.
        intros a b eq.
        specialize (f_mono A (λ _, a) (λ _, b)).
        specialize (f_mono (functional_ext _ _ _ (λ _, eq))).
        exact (func_eq _ _ f_mono a).
    -   intros inj C g h eq.
        functional_intros x.
        pose proof (func_eq _ _ eq x) as eq2.
        cbn in eq2.
        apply inj in eq2.
        exact eq2.
Qed.

Theorem set_category_epimorphism : ∀ {A B : TYPE} (f : morphism A B),
    epimorphism f ↔ Surjective f.
Proof.
    intros A B f.
    split.
    -   intros f_epi.
        split.
        intros y.
        specialize (f_epi Prop (λ _, True) (λ z, ∃ a, f a = z)).
        cbn in f_epi.
        prove_parts f_epi.
        {
            functional_intros x.
            symmetry; apply prop_is_true.
            exists x.
            reflexivity.
        }
        pose proof (func_eq _ _ f_epi y) as eq; cbn in eq.
        symmetry in eq.
        rewrite <- prop_eq_true in eq.
        exact eq.
    -   intros f_sur C g h eq.
        functional_intros y.
        pose proof (sur f y) as [x x_eq].
        pose proof (func_eq _ _ eq x) as eq2; cbn in eq2.
        rewrite x_eq in eq2.
        exact eq2.
Qed.

Theorem set_category_isomorphism : ∀ {A B : TYPE} (f : morphism A B),
    is_isomorphism f ↔ Bijective f.
Proof.
    intros A B f.
    split.
    -   intros [g [g_eq1 g_eq2]].
        apply (inverse_ex_bijective f g).
        split; apply func_eq; assumption.
    -   intros f_bij.
        exists (bij_inv f).
        split; apply functional_ext; apply bij_inv_inv.
Qed.
