Require Import init.

Require Export card2_order.
Require Export set.

Open Scope card_scope.

Lemma card_plus_wd : ∀ A B C D, A ~ B → C ~ D → (A + C ~ B + D)%type.
Proof.
    intros A B C D [f f_bij] [g g_bij].
    exists (λ x, match x with
                 | inl a => inl (f a)
                 | inr c => inr (g c)
                 end).
    apply (inverse_ex_bijective _ (λ x, match x with
        | inl b => inl (bij_inv f b)
        | inr d => inr (bij_inv g d)
        end)).
    split.
    -   intros [x|x].
        +   rewrite bij_inv_eq2; reflexivity.
        +   rewrite bij_inv_eq2; reflexivity.
    -   intros [x|x].
        +   rewrite bij_inv_eq1; reflexivity.
        +   rewrite bij_inv_eq1; reflexivity.
Qed.

Global Instance card_plus_class : Plus card := {
    plus := binary_op (binary_self_wd card_plus_wd)
}.

Global Instance card_plus_assoc_class : PlusAssoc card.
Proof.
    split.
    intros A B C.
    equiv_get_value A B C.
    unfold plus; equiv_simpl.
    exists (λ x,
        match x with
        | inl a => inl (inl a)
        | inr x' => match x' with
                    | inl b => inl (inr b)
                    | inr c => inr c
                    end
        end).
    apply (inverse_ex_bijective _ (λ x,
        match x with
        | inl x' => match x' with
                    | inl a => inl a
                    | inr b => inr (inl b)
                    end
        | inr c => inr (inr c)
        end)).
    split.
    -   intros [[a|b]|c]; reflexivity.
    -   intros [a|[b|c]]; reflexivity.
Qed.

Global Instance card_plus_comm_class : PlusComm card.
Proof.
    split.
    intros A B.
    equiv_get_value A B.
    unfold plus; equiv_simpl.
    exists (λ x, match x with
                 | inl a => inr a
                 | inr b => inl b
                 end).
    apply (inverse_ex_bijective _ (λ x,
        match x with
        | inl b => inr b
        | inr a => inl a
        end)).
    split; intros [x|x]; reflexivity.
Qed.

Global Instance card_zero : Zero card := {
    zero := |empty_type|
}.

Global Instance card_plus_lid_class : PlusLid card.
Proof.
    split.
    intros A.
    equiv_get_value A.
    unfold zero, plus; equiv_simpl.
    exists (λ x, match x with
                 | inl y => False_rect _ (empty_false y)
                 | inr a => a
                 end).
    apply (inverse_ex_bijective _ (λ x, inr x)).
    split.
    -   reflexivity.
    -   intros [x|x].
        +   contradiction (empty_false x).
        +   reflexivity.
Qed.

Global Instance card_le_lplus_class : OrderLplus card.
Proof.
    split.
    intros A B C.
    equiv_get_value A B C.
    unfold le, plus; equiv_simpl.
    intros [f f_inj].
    exists (λ x, match x with
                 | inl c => inl c
                 | inr a => inr (f a)
                 end).
    split.
    intros [c1|a1] [c2|a2] eq.
    -   apply inl_eq in eq.
        subst; reflexivity.
    -   contradiction (inlr_neq eq).
    -   contradiction (inrl_neq eq).
    -   apply inr_eq in eq.
        apply inj in eq.
        subst; reflexivity.
Qed.

Global Instance card_pos : OrderPositive card.
Proof.
    split.
    intros A.
    equiv_get_value A.
    unfold zero, le; equiv_simpl.
    exists (empty_function _ _ empty_false).
    apply empty_inj.
Qed.

Theorem card_false_0 : ∀ A, (A → False) → 0 = |A|.
Proof.
    intros A A_false.
    unfold zero; equiv_simpl.
    exists (empty_function _ _ empty_false).
    split.
    apply empty_inj.
    split.
    intros a.
    contradiction (A_false a).
Qed.

Theorem card_nz_ex {U} : 0 ≠ |U| → U.
Proof.
    intros neq.
    classic_contradiction contr.
    apply card_false_0 in contr.
    contradiction.
Qed.

Close Scope card_scope.
