Require Import init.

Require Export ord2_order.
Require Import set_induction.

Open Scope ord_scope.

Definition ord_plus_le (A B : ord_type) (a b : A + B) :=
    match a, b with
    | inl a', inl b' => a' ≤ b'
    | inl a', inr b' => True
    | inr a', inl b' => False
    | inr a', inr b' => a' ≤ b'
    end.

Section OrdPlusDef.

Context (A B : ord_type).

Definition ord_plus_order := {|le a b := ord_plus_le A B a b|}.
Global Existing Instance ord_plus_order.

Lemma ord_plus_antisym : Antisymmetric le.
Proof.
    split.
    intros [x|x] [y|y] xy yx; unfold le in *; cbn in *.
    -   rewrite (antisym xy yx).
        reflexivity.
    -   contradiction yx.
    -   contradiction xy.
    -   rewrite (antisym xy yx).
        reflexivity.
Qed.

Lemma ord_plus_wo : WellOrdered (ord_plus_le A B).
Proof.
    split.
    intros S [x Sx].
    classic_case (∃ a : A, S (inl a)) as [a_ex|a_nex].
    -   destruct a_ex as [a Sa].
        clear x Sx.
        pose (S' x := S (inl x)).
        pose proof (well_ordered S' (ex_intro _ _ Sa)) as [m [S'm m_least]].
        exists (inl m).
        split; [>exact S'm|].
        intros [y|y] Sy; cbn.
        2: exact true.
        apply m_least.
        exact Sy.
    -   rewrite not_ex in a_nex.
        destruct x as [x|b].
        1: contradiction (a_nex x Sx).
        pose (S' x := S (inr x)).
        pose proof (well_ordered S' (ex_intro _ _ Sx)) as [m [S'm m_least]].
        exists (inr m).
        split; [>exact S'm|].
        intros [y|y] Sy; cbn.
        1: contradiction (a_nex y Sy).
        apply m_least.
        exact Sy.
Qed.

Lemma inl_lt : ∀ a b, inl a < inl b ↔ a < b.
Proof.
    intros a b.
    split; intros [leq neq].
    all: split.
    all: unfold le in *; cbn in *.
    -   exact leq.
    -   apply (inl_neq a b) in neq.
        exact neq.
    -   exact leq.
    -   apply inl_neq.
        exact neq.
Qed.

Lemma inr_lt : ∀ a b, inr a < inr b ↔ a < b.
Proof.
    intros a b.
    split; intros [leq neq].
    all: split.
    all: unfold le in *; cbn in *.
    -   exact leq.
    -   apply (inr_neq a b) in neq.
        exact neq.
    -   exact leq.
    -   apply inr_neq.
        exact neq.
Qed.

Lemma inlr_lt : ∀ a b, inl a < inr b.
Proof.
    intros a b.
    split.
    -   exact true.
    -   apply inlr_neq.
Qed.

End OrdPlusDef.

Notation "A ⊕ B" :=
    (make_ord_type (ord_U A + ord_U B) (ord_plus_order A B)
    (ord_plus_antisym A B) (ord_plus_wo A B))
    : ord_scope.

Lemma ord_plus_wd : ∀ A B C D : ord_type, A ~ B → C ~ D → (A ⊕ C) ~ (B ⊕ D).
Proof.
    intros A B C D [f] [g].
    split.
    exists (λ x, match x with
        | inl a => inl (f a)
        | inr c => inr (g c)
        end
    ).
    1: split.
    all: split.
    -   intros [x|x] [y|y] eq.
        +   apply inl_eq in eq.
            apply inj in eq.
            rewrite eq.
            reflexivity.
        +   apply inlr_neq in eq.
            contradiction.
        +   apply inrl_neq in eq.
            contradiction.
        +   apply inr_eq in eq.
            apply inj in eq.
            rewrite eq.
            reflexivity.
    -   intros [y|y].
        +   pose proof (sur f y) as [x eq].
            exists (inl x).
            rewrite eq.
            reflexivity.
        +   pose proof (sur g y) as [x eq].
            exists (inr x).
            rewrite eq.
            reflexivity.
    -   intros [a|a] [c|c] leq; unfold le in *; cbn in *.
        +   apply homo_le.
            exact leq.
        +   exact true.
        +   contradiction.
        +   apply homo_le.
            exact leq.
Qed.

Global Instance ord_plus : Plus ord := {
    plus := binary_op (binary_self_wd ord_plus_wd)
}.

Global Instance ord_plus_assoc : PlusAssoc ord.
Proof.
    split.
    intros A B C.
    equiv_get_value A B C.
    unfold plus; equiv_simpl.
    split.
    exists (λ x, match x with
        | inl a => inl (inl a)
        | inr bc => match bc with
            | inl b => inl (inr b)
            | inr c => inr c
            end
        end
    ).
    1: split.
    all: split; cbn.
    -   intros [a|[a|a]] [b|[b|b]] eq.
        +   apply inl_eq in eq.
            apply inl_eq in eq.
            rewrite eq.
            reflexivity.
        +   apply inl_eq in eq.
            apply inlr_neq in eq.
            contradiction.
        +   apply inlr_neq in eq.
            contradiction.
        +   apply inl_eq in eq.
            apply inrl_neq in eq.
            contradiction.
        +   apply inl_eq in eq.
            apply inr_eq in eq.
            rewrite eq.
            reflexivity.
        +   apply inlr_neq in eq.
            contradiction.
        +   apply inrl_neq in eq.
            contradiction.
        +   apply inrl_neq in eq.
            contradiction.
        +   apply inr_eq in eq.
            rewrite eq.
            reflexivity.
    -   intros [[x|x]|x].
        +   exists (inl x).
            reflexivity.
        +   exists (inr (inl x)).
            reflexivity.
        +   exists (inr (inr x)).
            reflexivity.
    -   intros [a|[a|a]] [b|[b|b]] leq; unfold le in *; cbn in *.
        1, 2, 4, 5: unfold le; cbn.
        2, 5, 6: exact true.
        2, 4, 5: contradiction.
        all: exact leq.
Qed.

Global Instance ord_zero : Zero ord := {
    zero := to_ord (make_ord_type empty_type _ _ _)
}.

Global Instance ord_plus_lid : PlusLid ord.
Proof.
    split.
    intros A.
    equiv_get_value A.
    symmetry.
    unfold zero, plus; equiv_simpl.
    split.
    exists inr.
    1: split.
    all: split; cbn.
    -   intros a b eq.
        apply inr_eq in eq.
        exact eq.
    -   intros [y|y].
        +   contradiction (empty_false y).
        +   exists y.
            reflexivity.
    -   intros a b leq.
        exact leq.
Qed.

Global Instance ord_plus_rid : PlusRid ord.
Proof.
    split.
    intros A.
    equiv_get_value A.
    symmetry.
    unfold zero, plus; equiv_simpl.
    split.
    exists inl.
    1: split.
    all: split; cbn.
    -   intros a b eq.
        apply inl_eq in eq.
        exact eq.
    -   intros [y|y].
        +   exists y.
            reflexivity.
        +   contradiction (empty_false y).
    -   intros a b leq.
        exact leq.
Qed.

Theorem ord_lt_lplus : ∀ {α β} γ, α < β → γ + α < γ + β.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold plus; equiv_simpl.
    do 2 rewrite ord_lt_simpl.
    intros [x [f]].
    exists (inr x).
    split.
    pose (g (x : C + A) := match x with
        | inl c => inl c
        | inr a => inr [f a|]
        end).
    assert (∀ a, initial_segment (inr x) (g a)) as g_in.
    {
        intros [c|a]; unfold initial_segment; cbn.
        -   apply inlr_lt.
        -   apply inr_lt.
            exact [|f a].
    }
    exists (λ a, [g a| g_in a]).
    1: split.
    all: split.
    -   intros c a eq.
        apply set_type_eq in eq; cbn in eq.
        unfold g in eq.
        destruct c as [c|c], a as [a|a].
        +   apply inl_eq in eq.
            rewrite eq.
            reflexivity.
        +   apply inlr_neq in eq.
            contradiction.
        +   apply inrl_neq in eq.
            contradiction.
        +   apply inr_eq in eq.
            apply set_type_eq in eq.
            destruct f.
            apply inj in eq.
            rewrite eq.
            reflexivity.
    -   intros [[y|y] y_lt].
        +   exists (inl y).
            unfold g.
            apply set_type_eq2.
            reflexivity.
        +   assert (y < x) as y_lt2.
            {
                unfold initial_segment in y_lt.
                apply inr_lt in y_lt.
                exact y_lt.
            }
            pose proof (sur f [y|y_lt2]) as [a f_eq].
            exists (inr a).
            unfold g.
            apply set_type_eq2.
            rewrite f_eq.
            reflexivity.
    -   intros [c|c] [a|a].
        all: unfold le; cbn.
        all: intros leq.
        all: unfold le; cbn.
        +   exact leq.
        +   exact true.
        +   contradiction.
        +   apply (homo_le (f := f)) in leq.
            exact leq.
Qed.

Global Instance ord_plus_lcancel : PlusLcancel ord.
Proof.
    split.
    intros α β γ eq.
    destruct (trichotomy α β) as [[ltq|eq']|ltq].
    -   apply (ord_lt_lplus γ) in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply (ord_lt_lplus γ) in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

Global Instance ord_le_lplus : OrderLplus ord.
Proof.
    split.
    intros α β γ leq.
    classic_case (α = β) as [eq|neq].
    -   subst.
        apply refl.
    -   apply ord_lt_lplus.
        split; assumption.
Qed.

Theorem ord_pos : ∀ α, 0 ≤ α.
Proof.
    intros A.
    equiv_get_value A.
    unfold zero; equiv_simpl.
    apply ord_le_simpl; cbn.
    exists (λ a, False_rect _ (empty_false a)).
    split; split; cbn.
    -   intros a.
        contradiction (empty_false a).
    -   intros a.
        contradiction (empty_false a).
Qed.

Theorem ord_pos2 : ∀ α, 0 ≠ α → 0 < α.
Proof.
    intros α neq.
    split.
    -   apply ord_pos.
    -   exact neq.
Qed.

Theorem ord_le_ex : ∀ α β, α ≤ β → ∃ γ, α + γ = β.
Proof.
    intros A B.
    equiv_get_value A B.
    unfold le, plus; equiv_simpl.
    intros [f [f_inj [f_le f_lt]]].
    exists (to_ord (sub_ord_type (λ b : B, ∀ a : A, f a ≠ b))).
    equiv_simpl.
    split.
    exists (λ x, match x with
        | inl a => f a
        | inr b => [b|]
        end).
    1: split.
    all: split; cbn.
    -   intros [a|a] [b|b] eq.
        +   apply inj in eq.
            rewrite eq.
            reflexivity.
        +   contradiction ([|b] a eq).
        +   symmetry in eq.
            contradiction ([|a] b eq).
        +   apply set_type_eq in eq.
            rewrite eq.
            reflexivity.
    -   intros b.
        classic_case (∀ a, f a ≠ b) as [above|below].
        +   exists (inr [_|above]).
            reflexivity.
        +   rewrite not_all in below.
            destruct below as [a eq].
            rewrite not_not in eq.
            exists (inl a).
            exact eq.
    -   intros [a|a] [b|b] leq.
        all: unfold le in leq; cbn in leq.
        +   apply homo_le.
            exact leq.
        +   apply f_lt.
            exact [|b].
        +   contradiction.
        +   exact leq.
Qed.

Theorem ord_lt_ex : ∀ α β, α < β → ∃ γ, 0 ≠ γ ∧ α + γ = β.
Proof.
    intros α β ltq.
    pose proof (ord_le_ex _ _ (land ltq)) as [γ eq].
    exists γ.
    split; [>|exact eq].
    intros contr; subst.
    rewrite plus_rid in ltq.
    contradiction (irrefl _ ltq).
Qed.

Theorem ord_lt_plus_lcancel : ∀ {α β} γ, γ + α < γ + β → α < β.
Proof.
    intros α β γ ltq.
    apply ord_lt_ex in ltq as [δ [δ_nz eq]].
    rewrite <- plus_assoc in eq.
    apply plus_lcancel in eq; clear γ.
    rewrite <- eq; clear β eq.
    rewrite <- plus_rid at 1.
    apply ord_lt_lplus.
    apply ord_pos2.
    exact δ_nz.
Qed.

Global Instance ord_le_plus_lcancel : OrderPlusLcancel ord.
Proof.
    split.
    intros α β γ leq.
    classic_case (γ + α = γ + β) as [eq|neq].
    -   apply plus_lcancel in eq.
        rewrite eq.
        apply refl.
    -   apply (ord_lt_plus_lcancel γ).
        split; assumption.
Qed.

Theorem ord_le_self_rplus : ∀ α β, α ≤ α + β.
Proof.
    intros α β.
    rewrite <- plus_rid at 1.
    apply le_lplus.
    apply ord_pos.
Qed.

Theorem ord_le_self_lplus : ∀ α β, α ≤ β + α.
Proof.
    intros A B.
    equiv_get_value A B.
    unfold plus; equiv_simpl.
    apply ord_le_simpl.
    exists (λ x, inr x).
    split; split.
    -   intros a b eq.
        apply inr_eq in eq.
        exact eq.
    -   intros a b leq.
        exact leq.
Qed.

Global Instance ord_le_rplus : OrderRplus ord.
Proof.
    split.
    intros α β γ leq.
    apply ord_le_ex in leq as [δ eq].
    rewrite <- eq.
    rewrite <- plus_assoc.
    apply le_lplus.
    apply ord_le_self_lplus.
Qed.

Theorem ord_lt_plus_rcancel : ∀ {α β} γ, α + γ < β + γ → α < β.
Proof.
    intros α β γ eq.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    apply le_rplus with γ in contr.
    contradiction (irrefl _ (le_lt_trans contr eq)).
Qed.

Theorem ord_lt_self_rplus : ∀ α β, 0 ≠ β → α < α + β.
Proof.
    intros α β β_nz.
    split.
    -   apply ord_le_self_rplus.
    -   intros contr.
        rewrite <- plus_rid in contr at 1.
        apply plus_lcancel in contr.
        contradiction.
Qed.

Theorem ord_false_0 : ∀ A : ord_type, (A → False) → 0 = to_ord A.
Proof.
    intros A A_false.
    unfold zero; equiv_simpl.
    split.
    exists (λ a, False_rect _ (empty_false a)).
    1: split.
    all: split; cbn.
    -   intros a.
        contradiction (empty_false a).
    -   intros y.
        contradiction (A_false y).
    -   intros a.
        contradiction (empty_false a).
Qed.

Close Scope ord_scope.
