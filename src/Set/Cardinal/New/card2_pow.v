Require Import init.

Require Export card2_mult.

Open Scope card_scope.

Lemma card_pow_wd : ∀ A B C D, A ~ B → C ~ D → (C → A) ~ (D → B).
Proof.
    intros A B C D [f f_bij] [g g_bij].
    exists (λ h, (λ x, f (h (bij_inv g x)))).
    split; split.
    -   intros h1 h2 eq.
        functional_intros c.
        pose proof (func_eq _ _ eq) as eq2; cbn in eq2.
        specialize (eq2 (g c)).
        rewrite bij_inv_eq1 in eq2.
        apply inj in eq2.
        exact eq2.
    -   intros h.
        exists (λ c, bij_inv f (h (g c))).
        functional_intros d.
        do 2 rewrite bij_inv_eq2.
        reflexivity.
Qed.

Definition card_pow := binary_op (binary_self_wd card_pow_wd).
Infix "^" := card_pow : card_scope.

Theorem func_size : ∀ A B, |A → B| = |B| ^ |A|.
Proof.
    intros A B.
    unfold card_pow; cbn.
    rewrite binary_op_eq.
    reflexivity.
Qed.

Theorem card_pow_zero : ∀ κ, κ ^ 0 = 1.
Proof.
    intros A.
    equiv_get_value A.
    unfold zero, one, card_pow; equiv_simpl.
    exists (λ _, Single).
    split; split.
    -   intros f g eq.
        functional_intros x.
        contradiction (empty_false x).
    -   intros y.
        exists (empty_function _ _ empty_false).
        apply singleton_type_eq.
Qed.

Theorem card_zero_pow : ∀ κ, 0 ≠ κ → 0 ^ κ = 0.
Proof.
    intros A neq.
    equiv_get_value A.
    symmetry.
    unfold zero at 2, card_pow; equiv_simpl.
    apply card_false_0.
    intros f.
    apply neq.
    apply card_false_0.
    intros a.
    contradiction (empty_false (f a)).
Qed.

Theorem card_one_pow : ∀ κ, 1 ^ κ = 1.
Proof.
    intros A.
    equiv_get_value A.
    unfold one, card_pow; equiv_simpl.
    exists (λ _, Single).
    split; split.
    -   intros f g eq.
        functional_intros a.
        apply singleton_type_eq.
    -   intros y.
        exists (λ _, Single).
        apply singleton_type_eq.
Qed.

Theorem card_pow_one : ∀ κ, κ ^ 1 = κ.
Proof.
    intros A.
    equiv_get_value A.
    unfold one, card_pow; equiv_simpl.
    exists (λ f, f Single).
    split; split.
    -   intros f g eq.
        functional_intros x.
        rewrite (singleton_type_eq x Single).
        exact eq.
    -   intros y.
        exists (λ _, y).
        reflexivity.
Qed.

Theorem card_pow_plus : ∀ κ μ ν, κ ^ (μ + ν) = κ ^ μ * κ ^ ν.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold plus, mult, card_pow; equiv_simpl.
    exists (λ f, ((λ b, f (inl b)), (λ c, f (inr c)))).
    split; split.
    -   intros f g eq.
        apply prod_split in eq as [eq1' eq2'].
        pose proof (func_eq _ _ eq1') as eq1.
        pose proof (func_eq _ _ eq2') as eq2.
        clear eq1' eq2'; cbn in eq1, eq2.
        functional_intros [b|c].
        +   apply eq1.
        +   apply eq2.
    -   intros [f g].
        exists (λ x, match x with
                     | inl b => f b
                     | inr c => g c
                     end).
        apply f_equal2.
        all: reflexivity.
Qed.

Theorem card_pow_pow : ∀ κ μ ν, (κ ^ μ) ^ ν = κ ^ (μ * ν).
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold mult, card_pow; equiv_simpl.
    exists (λ f, λ x, f (snd x) (fst x)).
    split; split.
    -   intros f g eq.
        pose proof (func_eq _ _ eq) as eq2; cbn in eq2.
        functional_intros c.
        functional_intros b.
        exact (eq2 (b, c)).
    -   intros f.
        exists (λ c, λ b, f (b, c)).
        functional_intros [b c].
        reflexivity.
Qed.

Theorem card_pow_mult : ∀ κ μ ν, (κ * μ) ^ ν = κ ^ ν * μ ^ ν.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold mult, card_pow; equiv_simpl.
    exists (λ f, ((λ c, fst (f c)), (λ c, snd (f c)))).
    split; split.
    -   intros f g eq.
        functional_intros c.
        apply prod_split in eq as [eq1' eq2'].
        pose proof (func_eq _ _ eq1') as eq1.
        pose proof (func_eq _ _ eq2') as eq2.
        clear eq1' eq2'; cbn in eq1, eq2.
        specialize (eq1 c).
        specialize (eq2 c).
        apply prod_combine; assumption.
    -   intros [f g].
        exists (λ c, (f c, g c)).
        cbn.
        reflexivity.
Qed.

Theorem prop_size : |Prop| = 2.
Proof.
    unfold one, plus; equiv_simpl.
    exists (λ P, If P then (inl Single) else (inr Single)).
    split; split.
    -   intros A B eq.
        classic_case A as [a|a]; classic_case B as [b|b].
        +   apply propositional_ext.
            split; intro; assumption.
        +   contradiction (inlr_neq eq).
        +   contradiction (inrl_neq eq).
        +   apply propositional_ext.
            split; apply contrapositive_iff; intro; assumption.
    -   intros [y|y].
        +   exists True.
            classic_case True; [>|contradiction].
            apply f_equal.
            apply singleton_type_eq.
        +   exists False.
            classic_case False; [>contradiction|].
            apply f_equal.
            apply singleton_type_eq.
Qed.

Theorem power_set_size : ∀ A, |A → Prop| = 2 ^ |A|.
Proof.
    intros A.
    rewrite func_size.
    rewrite prop_size.
    reflexivity.
Qed.

Theorem card_lt_pow2 : ∀ κ, κ < 2^κ.
Proof.
    intros A.
    equiv_get_value A.
    rewrite <- power_set_size.
    apply power_set_bigger.
Qed.

Close Scope card_scope.
