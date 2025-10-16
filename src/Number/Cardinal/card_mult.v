Require Import init.

Require Export card_plus.
Require Import ord.

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

Global Instance ord_to_card_one : HomomorphismOne ord_to_card.
Proof.
    split.
    unfold one, ord_to_card; cbn.
    rewrite unary_op_eq.
    reflexivity.
Qed.

Global Instance ord_to_card_mult : HomomorphismMult ord_to_card.
Proof.
    split.
    intros A B.
    equiv_get_value A B.
    unfold ord_to_card at 2 3.
    unfold mult at 2; equiv_simpl.
    symmetry; apply ord_to_card_eq2.
    pose (α := to_ord A).
    pose (β := to_ord B).
    fold α β.
    assert (∀ a b, α * ord_type_init_ord_base B b
                     + ord_type_init_ord_base A a < α * β) as f_lt.
    {
        intros a b.
        pose proof (ord_type_init_ord_in a) as a_lt.
        pose proof (ord_type_init_ord_in b) as b_lt.
        unfold initial_segment in a_lt, b_lt.
        fold α in a_lt.
        fold β in b_lt.
        apply (lt_lplus (α * ord_type_init_ord_base B b)) in a_lt.
        apply (lt_le_trans a_lt).
        rewrite <- ord_mult_suc.
        apply le_lmult.
        rewrite ord_le_suc_lt.
        exact b_lt.
    }
    exists (λ x, [α * ord_type_init_ord_base B (snd x)
                    + ord_type_init_ord_base A (fst x) | f_lt (fst x) (snd x)]).
    pose proof (ord_type_init_ord_base_inj A).
    pose proof (ord_type_init_ord_base_inj B).
    pose proof (ord_type_init_ord_bij A).
    pose proof (ord_type_init_ord_bij B).
    split; split.
    -   intros [a1 b1] [a2 b2]; cbn; intros eq.
        assert (0 ≠ α) as α_nz.
        {
            intros α_z.
            pose proof (ord_type_init_ord_in a1) as ltq.
            unfold initial_segment in ltq.
            fold α in ltq.
            rewrite <- α_z in ltq.
            contradiction (not_neg ltq).
        }
        rewrite set_type_eq2 in eq.
        pose proof (ord_type_init_ord_in a1) as ltq1.
        unfold initial_segment in ltq1; fold α in ltq1.
        apply (lt_lplus (α * ord_type_init_ord_base B b1)) in ltq1.
        rewrite eq in ltq1.
        pose proof (ord_type_init_ord_in a2) as ltq2.
        unfold initial_segment in ltq2; fold α in ltq2.
        apply (lt_lplus (α * ord_type_init_ord_base B b2)) in ltq2.
        rewrite <- eq in ltq2.
        apply (le_lt_trans (ord_le_self_rplus _ _)) in ltq1.
        apply (le_lt_trans (ord_le_self_rplus _ _)) in ltq2.
        rewrite <- ord_mult_suc in ltq1, ltq2.
        apply (lt_mult_lcancel α α_nz) in ltq1, ltq2.
        rewrite ord_lt_suc_le in ltq1, ltq2.
        pose proof (antisym ltq1 ltq2) as eq'.
        apply inj in eq'.
        subst b2.
        apply plus_lcancel in eq.
        apply inj in eq.
        subst a2.
        reflexivity.
    -   intros [γ γ_lt].
        unfold initial_segment in γ_lt.
        assert (0 ≠ α) as α_nz.
        {
            intros α_z.
            rewrite <- α_z in γ_lt.
            rewrite mult_lanni in γ_lt.
            contradiction (not_neg γ_lt).
        }
        pose proof (ord_div γ α α_nz) as [ε [δ [γ_eq δ_lt]]].
        assert (ε < β) as ε_lt.
        {
            apply (lt_mult_lcancel α α_nz).
            apply (le_lt_trans2 γ_lt).
            rewrite γ_eq.
            apply ord_le_self_rplus.
        }
        pose proof (sur (ord_type_init_ord A) [δ|δ_lt]) as [a a_eq].
        pose proof (sur (ord_type_init_ord B) [ε|ε_lt]) as [b b_eq].
        exists (a, b).
        rewrite set_type_eq2; cbn.
        unfold ord_type_init_ord in a_eq, b_eq.
        rewrite set_type_eq2 in a_eq.
        rewrite set_type_eq2 in b_eq.
        rewrite a_eq, b_eq.
        symmetry; exact γ_eq.
Qed.

Theorem card_not_trivial : 0 ≠ 1.
Proof.
    intros eq.
    symmetry in eq.
    unfold zero, one in eq; equiv_simpl in eq.
    destruct eq as [f].
    destruct (f Single).
Qed.

Global Instance card_not_trivial_class : NotTrivial card := {
    not_trivial_a := 0;
    not_trivial_b := 1;
    not_trivial := card_not_trivial;
}.

Theorem card_one_pos : 0 < 1.
Proof.
    apply all_pos2.
    exact card_not_trivial.
Qed.

Close Scope card_scope.
