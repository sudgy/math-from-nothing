Require Import init.

Require Export card2_order.
Require Export set.
Require Import ord.

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

Global Instance ord_to_card_zero : HomomorphismZero ord_to_card.
Proof.
    split.
    unfold ord_to_card, zero; cbn.
    rewrite unary_op_eq; cbn.
    reflexivity.
Qed.

Global Instance ord_to_card_plus : HomomorphismPlus ord_to_card.
Proof.
    split.
    intros A B.
    equiv_get_value A B.
    unfold ord_to_card at 2 3.
    unfold plus at 2; equiv_simpl.
    symmetry; apply ord_to_card_eq2.
    pose (α := to_ord A).
    pose (β := to_ord B).
    fold α β.
    assert (∀ a : A, ord_type_init_ord_base A a < α + β)
        as f_lt1.
    {
        intros a.
        apply (lt_le_trans2 (ord_le_self_rplus _ _)).
        unfold α, ord_type_init_ord_base.
        rewrite ord_lt_simpl.
        exists a.
        apply refl.
    }
    assert (∀ b : B, α + ord_type_init_ord_base B b < α + β)
        as f_lt2.
    {
        intros b.
        apply lt_lplus.
        unfold β, ord_type_init_ord_base.
        rewrite ord_lt_simpl.
        exists b.
        apply refl.
    }
    exists (λ x, match x with
        | inl a => [ord_type_init_ord_base A a |f_lt1 a]
        | inr b => [α + ord_type_init_ord_base B b |f_lt2 b]
        end).
    pose proof (ord_type_init_ord_base_inj A).
    pose proof (ord_type_init_ord_base_inj B).
    pose proof (ord_type_init_ord_bij A).
    pose proof (ord_type_init_ord_bij B).
    split; split.
    -   intros [a1|b1] [a2|b2] eq; rewrite set_type_eq2 in eq.
        +   apply inj in eq.
            subst; reflexivity.
        +   pose proof (ord_type_init_ord_in a1) as ltq.
            unfold initial_segment in ltq.
            fold α in ltq.
            rewrite eq in ltq.
            apply (le_lt_trans (ord_le_self_rplus _ _)) in ltq.
            contradiction (irrefl _ ltq).
        +   pose proof (ord_type_init_ord_in a2) as ltq.
            unfold initial_segment in ltq.
            fold α in ltq.
            rewrite <- eq in ltq.
            apply (le_lt_trans (ord_le_self_rplus _ _)) in ltq.
            contradiction (irrefl _ ltq).
        +   apply plus_lcancel in eq.
            apply inj in eq.
            subst; reflexivity.
    -   intros [γ γ_lt].
        unfold initial_segment in γ_lt.
        classic_case (γ < α) as [γ_lt2|γ_ge].
        +   pose proof (sur (ord_type_init_ord A) [γ|γ_lt2]) as [a a_eq].
            exists (inl a).
            apply set_type_eq2.
            unfold ord_type_init_ord in a_eq.
            rewrite set_type_eq2 in a_eq.
            exact a_eq.
        +   rewrite nlt_le in γ_ge.
            apply ord_le_ex in γ_ge as [δ δ_eq]; subst γ.
            pose proof γ_lt as δ_lt.
            apply lt_plus_lcancel in δ_lt.
            pose proof (sur (ord_type_init_ord B) [δ|δ_lt]) as [b b_eq].
            exists (inr b).
            apply set_type_eq2.
            apply lplus.
            unfold ord_type_init_ord in b_eq.
            rewrite set_type_eq2 in b_eq.
            exact b_eq.
Qed.

Close Scope card_scope.
