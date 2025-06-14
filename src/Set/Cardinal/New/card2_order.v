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

Theorem card_to_initial_ord_le :
    ∀ κ μ, card_to_initial_ord κ ≤ card_to_initial_ord μ → κ ≤ μ.
Proof.
    intros κ μ leq.
    remember (card_to_initial_ord κ) as α.
    apply (f_equal ord_to_card) in Heqα.
    rewrite card_to_initial_ord_to_card_eq in Heqα.
    remember (card_to_initial_ord μ) as β.
    apply (f_equal ord_to_card) in Heqβ.
    rewrite card_to_initial_ord_to_card_eq in Heqβ.
    unfold ord_to_card in *.
    equiv_get_value α β.
    equiv_simpl in Heqα.
    equiv_simpl in Heqβ.
    unfold le in leq; equiv_simpl in leq.
    destruct leq as [f [f_inj [f_le f_lt]]].
    equiv_get_value κ μ.
    unfold le; equiv_simpl.
    exists f.
    exact f_inj.
Qed.

Global Instance card_le_trans : Transitive le.
Proof.
    split.
    intros A B C AB BC.
    equiv_get_value A B C.
    unfold le in *.
    equiv_simpl.
    equiv_simpl in AB.
    equiv_simpl in BC.
    destruct AB as [f f_bij].
    destruct BC as [g g_bij].
    exists (λ x, g (f x)).
    apply inj_comp; assumption.
Qed.

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
            destruct a1_eq as [lb1 [lb1_lonely lb1_descendent]].
            subst.
            exfalso; apply a2_eq.
            destruct lb1_descendent as [n eq].
            exists lb1.
            split; [>exact lb1_lonely|].
            destruct n; cbn in eq.
            -   specialize (lb1_lonely (g (f a2))).
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
    -   intros b.
        classic_case (∃ bl, lonely bl ∧ descendent_of b bl) as [b_eq|b_eq].
        +   destruct b_eq as [bl [bl_lonely [n bl_descendent]]].
            exists (g b).
            classic_case (has_ancestor (g b)) as [b_eq|b_eq].
            *   apply g_inj.
                apply parent_eq.
            *   exfalso; apply b_eq.
                rewrite bl_descendent.
                exists bl.
                split; [>exact bl_lonely|].
                exists (nat_suc n).
                reflexivity.
        +   pose proof b_eq as b_eq2.
            rewrite not_ex in b_eq2.
            specialize (b_eq2 b).
            rewrite and_comm in b_eq2.
            rewrite not_and_impl in b_eq2.
            prove_parts b_eq2; [>exists 0; reflexivity|].
            unfold lonely in b_eq2.
            rewrite not_all in b_eq2.
            destruct b_eq2 as [a b_eq2].
            rewrite not_not in b_eq2.
            exists a.
            rewrite <- b_eq2 in b_eq.
            classic_case (has_ancestor a); [>contradiction|exact b_eq2].
Qed.

Theorem ord_to_card_lt : ∀ α β, ord_to_card α < ord_to_card β → α < β.
Proof.
    intros A B ltq.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    assert (ord_to_card B ≤ ord_to_card A) as leq.
    {
        equiv_get_value A B.
        unfold ord_to_card, le; equiv_simpl.
        unfold le in contr; equiv_simpl in contr.
        destruct contr as [f [f_inj]].
        exists f.
        exact f_inj.
    }
    contradiction (irrefl _ (le_lt_trans leq ltq)).
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

Close Scope card_scope.
