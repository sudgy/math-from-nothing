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
    split; split.
    -   intros [a1|c1] [a2|c2] eq.
        +   apply inl_eq in eq.
            apply inj in eq.
            subst; reflexivity.
        +   contradiction (inlr_neq eq).
        +   contradiction (inrl_neq eq).
        +   apply inr_eq in eq.
            apply inj in eq.
            subst; reflexivity.
    -   intros [b|d].
        +   pose proof (sur f b) as [a eq].
            exists (inl a).
            rewrite eq.
            reflexivity.
        +   pose proof (sur g d) as [c eq].
            exists (inr c).
            rewrite eq.
            reflexivity.
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
    split; split.
    -   intros [a1|[b1|c1]] [a2|[b2|c2]] eq.
        +   do 2 apply inl_eq in eq.
            subst; reflexivity.
        +   apply inl_eq in eq.
            contradiction (inlr_neq eq).
        +   contradiction (inlr_neq eq).
        +   apply inl_eq in eq.
            contradiction (inrl_neq eq).
        +   apply inl_eq in eq.
            apply inr_eq in eq.
            subst; reflexivity.
        +   contradiction (inlr_neq eq).
        +   contradiction (inrl_neq eq).
        +   contradiction (inrl_neq eq).
        +   apply inr_eq in eq.
            subst; reflexivity.
    -   intros [[a|b]|c].
        +   exists (inl a).
            reflexivity.
        +   exists (inr (inl b)).
            reflexivity.
        +   exists (inr (inr c)).
            reflexivity.
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
    split; split.
    -   intros [a1|b1] [a2|b2] eq.
        +   apply inr_eq in eq.
            subst; reflexivity.
        +   contradiction (inrl_neq eq).
        +   contradiction (inlr_neq eq).
        +   apply inl_eq in eq.
            subst; reflexivity.
    -   intros [b|a].
        +   exists (inr b).
            reflexivity.
        +   exists (inl a).
            reflexivity.
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
    split; split.
    -   intros [x|a1]; [>contradiction (empty_false x)|].
        intros [x|a2]; [>contradiction (empty_false x)|].
        intro eq.
        subst; reflexivity.
    -   intros a.
        exists (inr a).
        reflexivity.
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

Theorem card_pos : ∀ κ, 0 ≤ κ.
Proof.
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
