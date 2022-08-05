Require Import init.

Require Import well_order.
Require Import card_base.
Require Import set.
Require Import function.
Require Export ord_basic.
Require Import nat.

Unset Keyed Unification.

(* begin hide *)
Open Scope card_scope.

Section CardOrder.

Local Open Scope card_scope.

Let card_le A B := ∃ f : A → B, injective f.
Local Infix "≦" := card_le.

Lemma card_le_wd_one : ∀ A B C D, A ~ B → C ~ D → A ≦ C → B ≦ D.
    intros A B C D [f f_bij] [g g_bij] [h h_inj].
    pose (f' := bij_inv f f_bij).
    exists (λ x, g (h (f' x))).
    intros a b eq.
    apply g_bij in eq.
    apply h_inj in eq.
    apply (bij_inv_bij f f_bij) in eq.
    exact eq.
Qed.

Lemma card_le_wd : ∀ A B C D, A ~ B → C ~ D → (A ≦ C) = (B ≦ D).
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
(* end hide *)
Theorem card_to_initial_ord_lte :
        ∀ κ μ, card_to_initial_ord κ < card_to_initial_ord μ → κ <= μ.
    intros κ μ lt.
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
    rewrite ord_lt_initial in lt.
    destruct lt as [x [f [f_bij f_iso]]].
    equiv_get_value κ μ.
    unfold le; equiv_simpl.
    exists (λ a, [f a|]).
    intros a b eq.
    apply f_bij.
    apply set_type_eq.
    exact eq.
Qed.

(* begin hide *)
Lemma card_le_connex : ∀ κ μ, {κ <= μ} + {μ <= κ}.
    intros A B.
    classic_case (A = B) as [eq|neq].
    {
        subst.
        left.
        exists identity.
        apply identity_bijective.
    }
    apply or_to_strong.
    pose (α := card_to_initial_ord A).
    pose (β := card_to_initial_ord B).
    pose proof (trichotomy α β) as [[leq|eq]|leq].
    -   left.
        apply card_to_initial_ord_lte.
        exact leq.
    -   apply card_to_initial_ord_eq in eq.
        contradiction.
    -   right.
        apply card_to_initial_ord_lte.
        exact leq.
Qed.
Global Instance card_le_connex_class : Connex le := {
    connex := card_le_connex
}.

Lemma card_le_transitive : ∀ κ μ ν, κ <= μ → μ <= ν → κ <= ν.
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
Global Instance card_le_trans_class : Transitive le := {
    trans := card_le_transitive
}.

Lemma card_le_antisymmetric : ∀ κ μ, κ <= μ → μ <= κ → κ = μ.
    intros A B AB BC.
    equiv_get_value A B.
    unfold le in AB, BC.
    equiv_simpl in AB.
    equiv_simpl in BC.
    equiv_simpl.
    destruct AB as [f f_inj], BC as [g g_inj].
    pose (lonely b := ∀ a, f a ≠ b).
    pose (descendent_of b1 b0 := ∃ n, b1 = iterate_func (λ x, f (g x)) n b0).
    assert (∀ a, (∃ b, lonely b ∧ descendent_of (f a) b) → ∃ b, g b = a) as h_ex.
    {
        intros a [b [b_lonely [n descendent]]].
        destruct n; simpl in descendent.
        -   specialize (b_lonely a).
            contradiction.
        -   apply f_inj in descendent.
            exists (iterate_func (λ x, f (g x)) n b).
            symmetry; exact descendent.
    }
    pose (h a :=
        match (strong_excluded_middle (∃ b, lonely b ∧ descendent_of (f a) b)) with
        |   strong_or_left H => ex_val (h_ex a H)
        |   strong_or_right _ => f a
        end
    ).
    exists h.
    split.
    -   assert (∀ (a1 a2 : A) (P : (∃ b, lonely b ∧ descendent_of (f a1) b)),
                                  ¬(∃ b, lonely b ∧ descendent_of (f a2) b) →
                                    ex_val (h_ex a1 P) = f a2 → a1 = a2) as wlog.
        {
            clear - f_inj g_inj.
            intros a1 a2 a1_eq a2_eq.
            destruct a1_eq as [lb1 [lb1_lonely lb1_descendent]].
            rewrite_ex_val b1 b1_eq.
            intro a_eq.
            subst.
            rewrite not_ex in a2_eq.
            specialize (a2_eq lb1).
            rewrite not_and in a2_eq.
            destruct a2_eq as [a2_eq|a2_eq]; try contradiction.
            destruct lb1_descendent as [n eq].
            destruct n.
            -   simpl in eq.
                specialize (lb1_lonely (g (f a2))).
                contradiction.
            -   unfold descendent_of in a2_eq.
                rewrite not_ex in a2_eq.
                specialize (a2_eq n).
                simpl in eq.
                apply f_inj in eq.
                apply g_inj in eq.
                contradiction.
        }
        intros a1 a2 a_eq.
        unfold h in a_eq.
        classic_case (∃ b, lonely b ∧ descendent_of (f a1) b) as [a1_eq|a1_eq];
        classic_case (∃ b, lonely b ∧ descendent_of (f a2) b) as [a2_eq|a2_eq].
        +   destruct a1_eq as [lb1 [lb1_lonely lb1_descendent]].
            destruct a2_eq as [lb2 [lb2_lonely lb2_descendent]].
            revert a_eq.
            rewrite_ex_val b1 b1_eq.
            rewrite_ex_val b2 b2_eq.
            intro a_eq.
            subst.
            reflexivity.
        +   exact (wlog a1 a2 a1_eq a2_eq a_eq).
        +   symmetry; symmetry in a_eq; exact (wlog a2 a1 a2_eq a1_eq a_eq).
        +   apply f_inj.
            exact a_eq.
    -   intros b.
        unfold h.
        classic_case (∃ bl, lonely bl ∧ descendent_of b bl) as [b_eq|b_eq].
        +   destruct b_eq as [bl [bl_lonely [n bl_descendent]]].
            exists (g b).
            classic_case (∃ b', lonely b' ∧ descendent_of (f (g b)) b') as [b_eq|b_eq].
            *   rewrite_ex_val b' b'_eq.
                apply g_inj.
                exact b'_eq.
            *   rewrite not_ex in b_eq.
                specialize (b_eq bl).
                rewrite not_and_impl in b_eq.
                specialize (b_eq bl_lonely).
                unfold descendent_of in b_eq.
                rewrite bl_descendent in b_eq.
                rewrite not_ex in b_eq.
                specialize (b_eq (nat_suc n)).
                simpl in b_eq.
                contradiction.
        +   pose proof b_eq as b_eq2.
            rewrite not_ex in b_eq2.
            specialize (b_eq2 b).
            rewrite not_and in b_eq2.
            destruct b_eq2 as [b_eq2|b_eq2].
            *   unfold lonely in b_eq2.
                rewrite not_all in b_eq2.
                destruct b_eq2 as [a b_eq2].
                rewrite not_not in b_eq2.
                exists a.
                rewrite <- b_eq2 in b_eq.
                classic_case (∃ bl, lonely bl ∧ descendent_of (f a) bl); auto.
                contradiction.
            *   unfold descendent_of in b_eq2.
                rewrite not_ex in b_eq2.
                specialize (b_eq2 zero).
                contradiction b_eq2; reflexivity.
Qed.
Global Instance card_le_antisym_class : Antisymmetric le := {
    antisym := card_le_antisymmetric
}.
(* end hide *)
Theorem ord_to_card_lt : ∀ α β, ord_to_card α < ord_to_card β → α < β.
    intros α β leq.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    rewrite ord_le_lt in contr.
    destruct contr as [contr|contr].
    -   subst.
        destruct leq; contradiction.
    -   destruct leq as [leq neq].
        assert (ord_to_card β <= ord_to_card α) as leq2.
        {
            clear leq neq.
            rename α into A.
            rename β into B.
            equiv_get_value A B.
            rewrite ord_lt_initial in contr.
            unfold le, ord_to_card; equiv_simpl.
            destruct contr as [x [f [f_bij f_iso]]]; clear f_iso.
            exists (λ x, [f x|]).
            intros a b eq.
            apply f_bij.
            apply set_type_eq.
            exact eq.
        }
        pose proof (antisym leq leq2).
        contradiction.
Qed.

(* begin hide *)
Lemma card_le_wf : ∀ S : card → Prop, (∃ κ, S κ) → ∃ κ, is_minimal le S κ.
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
    pose proof (well_founded S' S'_ex) as [α [[[κ Sκ] κ_eq] α_min]].
    unfold f in κ_eq; cbn in κ_eq.
    exists κ.
    split; try exact Sκ.
    intros μ Sμ μ_neq μ_leq.
    assert (μ < κ) as leq by (split; assumption); clear μ_neq μ_leq.
    rewrite <- card_to_initial_ord_to_card_eq in leq.
    rewrite <- (card_to_initial_ord_to_card_eq μ) in leq.
    apply ord_to_card_lt in leq.
    rewrite κ_eq in leq.
    assert (S' (card_to_initial_ord μ)) as S'μ by (exists [μ|Sμ]; reflexivity).
    apply (α_min _ S'μ); apply leq.
Qed.
Global Instance card_le_wf_class : WellFounded le := {
    well_founded := card_le_wf
}.
(* end hide *)
Theorem card_le_sub : ∀ κ A, κ <= |A| → ∃ S : A → Prop, |set_type S| = κ.
    intros B A leq.
    equiv_get_value B.
    unfold le in leq; equiv_simpl in leq.
    destruct leq as [f f_inj].
    exists (λ y, ∃ x, f x = y).
    equiv_simpl.
    exists (λ (y : set_type (λ y, ∃ x, f x = y)), ex_val [|y]).
    split.
    -   intros [a a_ex] [b b_ex] eq; cbn in *.
        apply set_type_eq; cbn.
        rewrite <- (ex_proof a_ex).
        rewrite <- (ex_proof b_ex).
        unfold ex_val in eq.
        rewrite eq.
        reflexivity.
    -   intros y.
        assert (∃ x, f x = f y) by (exists y; reflexivity).
        exists [f y|H].
        cbn.
        apply f_inj.
        rewrite <- (ex_proof H).
        reflexivity.
Qed.

Theorem card_sub_le : ∀ (A : Type) (S : A → Prop), |set_type S| <= |A|.
    intros A S.
    unfold le; equiv_simpl.
    exists (λ x, [x|]).
    intros a b eq.
    apply set_type_eq.
    exact eq.
Qed.

(* begin hide *)
Open Scope set_scope.
(* end hide *)
Theorem card_minus_le {U} : ∀ (A B : U → Prop),
        |set_type (A - B)| <= |set_type A|.
    intros A B.
    unfold le; equiv_simpl.
    exists (λ x, [[x|]|land [|x]]).
    intros a b eq.
    inversion eq as [eq2].
    apply set_type_eq.
    exact eq2.
Qed.

Theorem image_under_le {U V} : ∀ (A : U → Prop) (f : U → V),
        |set_type (image_under f A)| <= |set_type A|.
    intros A f.
    unfold le; equiv_simpl.
    exists (λ x, [ex_val [|x] | land (ex_proof [|x])]).
    intros a b eq.
    inversion eq as [eq2]; clear eq.
    rewrite_ex_val x xH.
    rewrite_ex_val y yH.
    destruct xH as [Ax a_eq], yH as [Ay b_eq].
    subst.
    apply set_type_eq.
    rewrite a_eq, b_eq.
    reflexivity.
Qed.
(* begin hide *)
Close Scope set_scope.
Close Scope card_scope.
(* end hide *)
