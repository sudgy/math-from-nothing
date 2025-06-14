Require Import init.

Require Export card2_plus.

Open Scope card_scope.

Lemma card_mult_wd : ∀ A B C D, A ~ B → C ~ D → (A * C ~ B * D)%type.
Proof.
    intros A B C D [f f_bij] [g g_bij].
    exists (λ x, (f (fst x), g (snd x))).
    split; split.
    -   intros [a1 c1] [a2 c2] eq; cbn in eq.
        apply prod_split in eq as [eq1 eq2].
        apply inj in eq1, eq2.
        subst; reflexivity.
    -   intros [b d].
        pose proof (sur f b) as [a a_eq].
        pose proof (sur g d) as [c c_eq].
        exists (a, c); cbn.
        rewrite a_eq, c_eq.
        reflexivity.
Qed.
Global Instance card_mult_class : Mult card := {
    mult := binary_op (binary_self_wd card_mult_wd)
}.

Theorem card_mult_type : ∀ A B, |(A*B)%type| = |A| * |B|.
Proof.
    intros A B.
    unfold mult; cbn.
    rewrite binary_op_eq.
    reflexivity.
Qed.

Global Instance card_mult_assoc_class : MultAssoc card.
Proof.
    split.
    intros A B C.
    equiv_get_value A B C.
    unfold mult; equiv_simpl.
    exists (λ x, ((fst x, fst (snd x)), snd (snd x))).
    split; split.
    -   intros [a1 [b1 c1]] [a2 [b2 c2]] eq.
        cbn in eq.
        apply prod_split in eq as [eq1 eq3].
        apply prod_split in eq1 as [eq1 eq2].
        subst; reflexivity.
    -   intros [[a b] c].
        exists (a, (b, c)).
        cbn.
        reflexivity.
Qed.

Global Instance card_mult_comm_class : MultComm card.
Proof.
    split.
    intros A B.
    equiv_get_value A B.
    unfold mult; equiv_simpl.
    exists (λ x, (snd x, fst x)).
    split; split.
    -   intros [a1 b1] [a2 b2] eq.
        cbn in eq.
        apply prod_split in eq as [eq1 eq2].
        subst; reflexivity.
    -   intros [b a].
        exists (a, b).
        cbn.
        reflexivity.
Qed.

Global Instance card_mult_lanni_class : MultLanni card.
Proof.
    split.
    intros A.
    equiv_get_value A.
    unfold zero, mult; equiv_simpl.
    exists (λ x, False_rect _ (empty_false (fst x))).
    split; split.
    -   intros [x a].
        contradiction (empty_false x).
    -   intros x.
        contradiction (empty_false x).
Qed.

Global Instance card_one : One card := {
    one := |singleton_type|
}.

Global Instance card_mult_lid_class : MultLid card.
Proof.
    split.
    intros A.
    equiv_get_value A.
    unfold one, mult; equiv_simpl.
    exists (λ x, snd x).
    split; split.
    -   intros [x a] [y b] eq.
        cbn in eq.
        apply prod_combine; cbn.
        +   apply singleton_type_eq.
        +   exact eq.
    -   intros a.
        exists (Single, a).
        reflexivity.
Qed.

Global Instance card_ldist_class : Ldist card.
Proof.
    split.
    intros A B C.
    equiv_get_value A B C.
    unfold plus, mult; equiv_simpl.
    exists (λ x, match (snd x) with
                 | inl b => inl (fst x, b)
                 | inr c => inr (fst x, c)
                 end).
    split; split.
    -   intros [a1 [b1|c1]] [a2 [b2|c2]] eq; cbn in eq.
        +   apply inl_eq in eq.
            apply prod_split in eq as [eq1 eq2].
            subst; reflexivity.
        +   contradiction (inlr_neq eq).
        +   contradiction (inrl_neq eq).
        +   apply inr_eq in eq.
            apply prod_split in eq as [eq1 eq2].
            subst; reflexivity.
    -   intros [[a b]|[a c]].
        +   exists (a, inl b).
            cbn.
            reflexivity.
        +   exists (a, inr c).
            cbn.
            reflexivity.
Qed.

Theorem card_mult_zero : ∀ κ μ, 0 = κ * μ → {0 = κ} + {0 = μ}.
Proof.
    intros A B.
    equiv_get_value A B.
    unfold mult; equiv_simpl.
    intros eq.
    apply or_to_strong.
    apply or_right.
    intros A_nz.
    apply card_false_0.
    intros b.
    apply A_nz.
    apply card_false_0.
    intros a.
    symmetry in eq.
    unfold zero in eq; equiv_simpl in eq.
    destruct eq as [f].
    contradiction (empty_false (f (a, b))).
Qed.

Theorem card_le_lmult : ∀ {κ μ} ν, κ ≤ μ → ν * κ ≤ ν * μ.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold le, mult; equiv_simpl.
    intros [f f_inj].
    exists (λ x, (fst x, f (snd x))).
    split.
    intros [c1 a1] [c2 a2] eq.
    cbn in eq.
    apply prod_split in eq as [eq1 eq2].
    apply f_inj in eq2.
    subst; reflexivity.
Qed.

Global Instance card_le_lmult_pos_class : OrderLmult card.
Proof.
    split.
    intros κ μ ν ν_pos.
    apply card_le_lmult.
Qed.

Theorem card_le_rmult : ∀ {κ μ} ν, κ ≤ μ → κ * ν ≤ μ * ν.
Proof.
    intros κ μ ν.
    apply le_rmult_pos.
    apply card_pos.
Qed.

Close Scope card_scope.
