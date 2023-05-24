Require Import init.

Require Import category_base.
Require Import category_product.
Require Import category_coproduct.
Require Import set.

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

Global Program Instance type_has_product : HasProducts TYPE := {
    product A B := make_product_obj A B (A * B)%type fst snd
}.
Next Obligation.
    intros [P p1 p2].
    cbn.
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        exists (λ x, (p1 x, p2 x)).
        split; cbn.
        all: apply functional_ext; reflexivity.
    -   intros [a [a_eq1 a_eq2]] [b [b_eq1 b_eq2]].
        cbn in *.
        rewrite set_type_eq2.
        functional_intros x.
        rewrite <- b_eq1 in a_eq1.
        rewrite <- b_eq2 in a_eq2.
        pose proof (func_eq _ _ a_eq1 x) as eq1.
        pose proof (func_eq _ _ a_eq2 x) as eq2.
        cbn in eq1, eq2.
        apply prod_combine; assumption.
Qed.

Global Program Instance type_has_coproducts : HasCoproducts TYPE := {
    coproduct A B := make_coproduct_obj A B (A + B)%type inl inr
}.
Next Obligation.
    intros [S i1 i2].
    cbn.
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        exists (λ x, match x with
            | inl a => i1 a
            | inr b => i2 b
        end).
        split; cbn.
        all: apply functional_ext; reflexivity.
    -   intros [a [a_eq1 a_eq2]] [b [b_eq1 b_eq2]].
        cbn in *.
        rewrite set_type_eq2.
        functional_intros x.
        destruct x as [x|x].
        +   rewrite <- b_eq1 in a_eq1.
            exact (func_eq _ _ a_eq1 x).
        +   rewrite <- b_eq2 in a_eq2.
            exact (func_eq _ _ a_eq2 x).
Qed.
