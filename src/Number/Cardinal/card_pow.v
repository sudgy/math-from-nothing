Require Import init.

Require Export card_mult.

Open Scope card_scope.

Lemma card_pow_wd : ∀ A B C D, A ~ B → C ~ D → (C → A) ~ (D → B).
Proof.
    intros A B C D [f f_bij] [g g_bij].
    exists (λ h d, f (h (bij_inv g d))).
    apply (inverse_ex_bijective _ (λ h c, bij_inv f (h (g c)))).
    split.
    -   functional_intros h x.
        do 2 rewrite bij_inv_eq2.
        reflexivity.
    -   functional_intros h x.
        do 2 rewrite bij_inv_eq1.
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
    apply (inverse_ex_bijective _ (λ _, empty_function _ _ empty_false)).
    split.
    -   apply singleton_type_eq.
    -   intros f.
        functional_intros x.
        contradiction (empty_false x).
Qed.

Theorem card_zero_pow : ∀ κ, 0 ≠ κ → 0 ^ κ = 0.
Proof.
    intros A neq.
    equiv_get_value A.
    symmetry.
    unfold zero at 2, card_pow; equiv_simpl.
    apply card_false_0.
    intros f.
    pose proof (card_nz_ex neq) as a.
    contradiction (empty_false (f a)).
Qed.

Theorem card_one_pow : ∀ κ, 1 ^ κ = 1.
Proof.
    intros A.
    equiv_get_value A.
    unfold one, card_pow; equiv_simpl.
    exists (λ _, Single).
    apply (inverse_ex_bijective _ (λ _ _, Single)).
    split.
    -   apply singleton_type_eq.
    -   functional_intros f x.
        apply singleton_type_eq.
Qed.

Theorem card_pow_one : ∀ κ, κ ^ 1 = κ.
Proof.
    intros A.
    equiv_get_value A.
    unfold one, card_pow; equiv_simpl.
    exists (λ f, f Single).
    apply (inverse_ex_bijective _ (λ a _, a)).
    split.
    -   reflexivity.
    -   functional_intros f x.
        apply f_equal.
        apply singleton_type_eq.
Qed.

Theorem card_pow_plus : ∀ κ μ ν, κ ^ (μ + ν) = κ ^ μ * κ ^ ν.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold plus, mult, card_pow; equiv_simpl.
    exists (λ f, ((λ b, f (inl b)), (λ c, f (inr c)))).
    apply (inverse_ex_bijective _ (λ f x, match x with
                                          | inl b => fst f b
                                          | inr c => snd f c
                                          end)).
    split.
    -   intros [f1 f2]; reflexivity.
    -   functional_intros f [x|x]; reflexivity.
Qed.

Theorem card_pow_pow : ∀ κ μ ν, (κ ^ μ) ^ ν = κ ^ (μ * ν).
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold mult, card_pow; equiv_simpl.
    exists (λ f, λ x, f (snd x) (fst x)).
    apply (inverse_ex_bijective _ (λ f c b, f (b, c))).
    split.
    -   functional_intros f [b c]; reflexivity.
    -   functional_intros f c b; reflexivity.
Qed.

Theorem card_pow_mult : ∀ κ μ ν, (κ * μ) ^ ν = κ ^ ν * μ ^ ν.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold mult, card_pow; equiv_simpl.
    exists (λ f, ((λ c, fst (f c)), (λ c, snd (f c)))).
    apply (inverse_ex_bijective _ (λ f x, (fst f x, snd f x))).
    split.
    -   intros f.
        apply prod_combine; reflexivity.
    -   functional_intros f x; cbn.
        apply prod_combine; reflexivity.
Qed.

Theorem prop_size : |Prop| = 2.
Proof.
    unfold one, plus; equiv_simpl.
    exists (λ P, If P then (inl Single) else (inr Single)).
    apply (inverse_ex_bijective _ (λ x, match x with
                                        | inl _ => True
                                        | inr _ => False
                                        end)).
    split.
    -   intros [x|x].
        +   rewrite (if_true true).
            apply f_equal; apply singleton_type_eq.
        +   rewrite (if_false not_false).
            apply f_equal; apply singleton_type_eq.
    -   intros P.
        classic_case P as [p|np].
        +   symmetry; exact (prop_is_true p).
        +   symmetry; exact (prop_is_false np).
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
