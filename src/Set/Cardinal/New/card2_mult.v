Require Import init.

Require Export card2_plus.

Open Scope card_scope.

Lemma card_mult_wd : ∀ A B C D, A ~ B → C ~ D → (A * C ~ B * D)%type.
Proof.
    intros A B C D [f f_bij] [g g_bij].
    exists (λ x, (f (fst x), g (snd x))).
    apply (inverse_ex_bijective _ (λ x,(bij_inv f (fst x), bij_inv g (snd x)))).
    split; cbn.
    -   intros x.
        do 2 rewrite bij_inv_eq2.
        destruct x; reflexivity.
    -   intros x.
        do 2 rewrite bij_inv_eq1.
        destruct x; reflexivity.
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
    apply (inverse_ex_bijective _ (λ x, (fst (fst x), (snd (fst x), snd x)))).
    split; cbn.
    -   intros [[a b] c]; reflexivity.
    -   intros [a [b c]]; reflexivity.
Qed.

Global Instance card_mult_comm_class : MultComm card.
Proof.
    split.
    intros A B.
    equiv_get_value A B.
    unfold mult; equiv_simpl.
    exists (λ x, (snd x, fst x)).
    apply (inverse_ex_bijective _ (λ x, (snd x, fst x))).
    split; cbn.
    -   intros [b a]; reflexivity.
    -   intros [a b]; reflexivity.
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
    apply (inverse_ex_bijective _ (λ x, (Single, x))).
    split; cbn.
    -   reflexivity.
    -   intros [s x]; cbn.
        apply prod_combine; cbn.
        +   apply singleton_type_eq.
        +   reflexivity.
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
    apply (inverse_ex_bijective _ (λ x,
        match x with
        | inl b => (fst b, inl (snd b))
        | inr c => (fst c, inr (snd c))
        end)).
    split.
    -   intros [[a b] | [a c]]; reflexivity.
    -   intros [a [b | c]]; reflexivity.
Qed.

Global Instance card_mult_zero : MultZero card.
Proof.
    split.
    intros A B.
    equiv_get_value A B.
    unfold mult; equiv_simpl.
    intros eq.
    rewrite <- not_not, not_or.
    intros [A_nz B_nz].
    apply card_nz_ex in A_nz as a.
    apply card_nz_ex in B_nz as b.
    symmetry in eq.
    unfold zero in eq; equiv_simpl in eq.
    destruct eq as [f].
    contradiction (empty_false (f (a, b))).
Qed.

Global Instance card_le_lmult : OrderLmult card.
Proof.
    split.
    intros A B C C_pos; clear C_pos.
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

Close Scope card_scope.
