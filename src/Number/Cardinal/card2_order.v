Require Import init.

Require Import nat.

Require Import ord2_order.
Require Export card2_base.

Open Scope card_scope.

Section CardOrder.

Let card_le A B := ∃ f : A → B, Injective f.
Local Infix "≦" := card_le.

Lemma card_le_wd_one : ∀ A B C D, A ~ B → C ~ D → A ≦ C → B ≦ D.
Proof.
    intros A B C D [f f_bij] [g g_bij] [h h_inj].
    pose (f' := bij_inv f).
    exists (λ x, g (h (f' x))).
    split.
    intros a b eq.
    apply g_bij in eq.
    apply h_inj in eq.
    apply (bij_inv_bij f) in eq.
    exact eq.
Qed.

Lemma card_le_wd : ∀ A B C D, A ~ B → C ~ D → (A ≦ C) = (B ≦ D).
Proof.
    intros A B C D AB CD.
    apply propositional_ext.
    split.
    -   apply card_le_wd_one; assumption.
    -   pose proof (eq_symmetric card_equiv) as sym.
        apply card_le_wd_one; apply sym; assumption.
Qed.

End CardOrder.

Global Instance card_order : Order card := {
    le := binary_op card_le_wd;
}.

Global Instance card_le_antisym : Antisymmetric le.
Proof.
    split.
    intros A B AB BC.
    equiv_get_value A B.
    unfold le in AB, BC.
    equiv_simpl in AB.
    equiv_simpl in BC.
    equiv_simpl.
    destruct AB as [f f_inj], BC as [g g_inj].
    pose (lonely b := ∀ a, f a ≠ b).
    pose (descendent_of b1 b0 := ∃ n, b1 = iterate_func (λ x, f (g x)) n b0).
    pose (has_ancestor a := ∃ b, lonely b ∧ descendent_of (f a) b).
    assert (∀ a, has_ancestor a → ∃ b, g b = a) as parent_ex.
    {
        intros a [b [b_lonely [n descendent]]].
        destruct n; cbn in descendent.
        -   specialize (b_lonely a).
            contradiction.
        -   apply inj in descendent.
            exists (iterate_func (λ x, f (g x)) n b).
            symmetry; exact descendent.
    }
    pose (parent a (H : has_ancestor a) := ex_val (parent_ex a H)).
    assert (∀ a H, g (parent a H) = a) as parent_eq.
    {
        intros a H.
        exact (ex_proof (parent_ex a H)).
    }
    exists (λ a, IfH has_ancestor a
                 then λ H, parent a H
                 else λ _, f a).
    split; split.
    -   assert (∀ (a1 a2 : A) (P : has_ancestor a1),
            ¬has_ancestor a2 → parent a1 P = f a2 → a1 = a2) as wlog.
        {
            intros a1 a2 a1_eq a2_eq.
            intro a_eq.
            apply (f_equal g) in a_eq.
            rewrite parent_eq in a_eq.
            destruct a1_eq as [b [b_lonely b_descendent]].
            subst.
            exfalso; apply a2_eq.
            destruct b_descendent as [n eq].
            exists b.
            split; [>exact b_lonely|].
            destruct n; cbn in eq.
            -   specialize (b_lonely (g (f a2))).
                contradiction.
            -   do 2 apply inj in eq.
                exists n.
                exact eq.
        }
        intros a1 a2 a_eq.
        classic_case (has_ancestor a1) as [a1_eq|a1_eq];
            classic_case (has_ancestor a2) as [a2_eq|a2_eq].
        +   apply (f_equal g) in a_eq.
            do 2 rewrite parent_eq in a_eq.
            exact a_eq.
        +   exact (wlog a1 a2 a1_eq a2_eq a_eq).
        +   symmetry; symmetry in a_eq; exact (wlog a2 a1 a2_eq a1_eq a_eq).
        +   apply f_inj.
            exact a_eq.
    -   intros y.
        classic_case (∃ b, lonely b ∧ descendent_of y b) as [y_eq|y_eq].
        +   destruct y_eq as [b [b_lonely [n b_descendent]]].
            exists (g y).
            classic_case (has_ancestor (g y)) as [y_eq|y_eq].
            *   apply g_inj.
                apply parent_eq.
            *   exfalso; apply y_eq.
                rewrite b_descendent.
                exists b.
                split; [>exact b_lonely|].
                exists (nat_suc n).
                reflexivity.
        +   pose proof y_eq as y_eq2.
            rewrite not_ex in y_eq2.
            specialize (y_eq2 y).
            rewrite and_comm in y_eq2.
            rewrite not_and_impl in y_eq2.
            prove_parts y_eq2; [>exists 0; reflexivity|].
            unfold lonely in y_eq2.
            rewrite not_all in y_eq2.
            destruct y_eq2 as [a y_eq2].
            rewrite not_not in y_eq2.
            exists a.
            rewrite <- y_eq2 in y_eq.
            classic_case (has_ancestor a); [>contradiction|exact y_eq2].
Qed.

Theorem ord_to_card_le : ∀ α β, α ≤ β → ord_to_card α ≤ ord_to_card β.
Proof.
    intros A B leq.
    equiv_get_value A B.
    unfold le in leq; equiv_simpl in leq.
    unfold le, ord_to_card; equiv_simpl.
    destruct leq as [f [f_inj]].
    exists f.
    exact f_inj.
Qed.

Theorem card_to_initial_ord_le :
    ∀ κ μ, card_to_initial_ord κ ≤ card_to_initial_ord μ → κ ≤ μ.
Proof.
    intros κ μ leq.
    apply ord_to_card_le in leq.
    do 2 rewrite card_to_initial_ord_to_card_eq in leq.
    exact leq.
Qed.

Global Instance card_le_wo : WellOrdered le.
Proof.
    split.
    intros S S_ex.
    pose (f (κ : set_type S) := card_to_initial_ord [κ|]).
    pose (S' α := ∃ κ, f κ = α).
    assert (∃ x, S' x) as S'_ex.
    {
        destruct S_ex as [κ Sκ].
        exists (card_to_initial_ord κ).
        unfold S'.
        exists [κ|Sκ].
        unfold f; cbn.
        reflexivity.
    }
    pose proof (well_ordered S' S'_ex) as [α [[[κ Sκ] κ_eq] α_min]].
    unfold f in κ_eq; cbn in κ_eq.
    exists κ.
    split; [>exact Sκ|].
    intros μ Sμ.
    specialize (α_min (card_to_initial_ord μ)).
    prove_parts α_min.
    {
        exists [μ|Sμ].
        reflexivity.
    }
    rewrite <- κ_eq in α_min.
    apply card_to_initial_ord_le in α_min.
    exact α_min.
Qed.

Global Instance card_to_initial_ord_le2 : HomomorphismLe card_to_initial_ord.
Proof.
    split.
    intros a b leq.
    classic_contradiction ltq.
    rewrite nle_lt in ltq.
    destruct ltq as [leq2 neq].
    apply card_to_initial_ord_le in leq2.
    pose proof (antisym leq leq2) as eq.
    subst; contradiction.
Qed.

Theorem ord_to_card_lt : ∀ α β, ord_to_card α < ord_to_card β → α < β.
Proof.
    intros α β ltq.
    classic_contradiction leq.
    rewrite nlt_le in leq.
    apply ord_to_card_le in leq.
    contradiction (irrefl _ (lt_le_trans ltq leq)).
Qed.

Theorem card_to_initial_ord_other_eq : ∀ α,
    (∀ β, β < α → ord_to_card β < ord_to_card α) →
    card_to_initial_ord (ord_to_card α) = α.
Proof.
    intros α lt_α.
    apply antisym; [>apply ord_to_card_to_initial_ord_le|].
    order_contradiction ltq.
    specialize (lt_α _ ltq).
    rewrite card_to_initial_ord_to_card_eq in lt_α.
    contradiction (irrefl _ lt_α).
Qed.

Theorem card_lt_ex : ∀ U V, |U| < |V| → ∀ f : U → V, ∃ y, ∀ x, f x ≠ y.
Proof.
    intros U V ltq f.
    classic_contradiction f_sur.
    rewrite <- nle_lt in ltq.
    apply ltq.
    unfold le; equiv_simpl.
    apply (partition_principle f).
    split.
    intros y.
    rewrite not_ex in f_sur.
    specialize (f_sur y).
    rewrite not_all in f_sur.
    destruct f_sur as [x eq].
    rewrite not_not in eq.
    exists x.
    exact eq.
Qed.

Theorem power_set_bigger : ∀ A, |A| < |A → Prop|.
Proof.
    intros A.
    split.
    -   unfold le; equiv_simpl.
        exists (λ a, ❴a❵).
        split.
        intros a b eq.
        unfold list_to_set in eq.
        pose proof (func_eq _ _ eq) as eq2.
        specialize (eq2 b).
        cbn in eq2.
        rewrite eq2.
        reflexivity.
    -   intros eq.
        equiv_simpl in eq.
        destruct eq as [f f_bij].
        pose (B x := ¬f x x).
        pose proof (sur f B) as [x x_eq].
        unfold B in x_eq.
        pose proof (func_eq _ _ x_eq x) as eq; cbn in eq.
        apply any_prop_neq in eq.
        exact eq.
Qed.

Theorem card_unbounded : ∀ κ, ∃ μ, κ < μ.
Proof.
    intros A.
    equiv_get_value A.
    exists (|A → Prop|).
    apply power_set_bigger.
Qed.

Close Scope card_scope.
