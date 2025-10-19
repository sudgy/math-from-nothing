Require Import init.

Require Export ord_sup.
Require Export card_large.
Require Import set_induction.
Require Import nat.

Lemma ord_suc_ex : ∀ α : ord, ∃ β, α < β.
Proof.
    intros α.
    pose proof (card_unbounded (ord_to_card α)) as [μ μ_gt].
    exists (card_to_initial_ord μ).
    rewrite <- card_to_initial_ord_to_card_eq in μ_gt.
    apply ord_to_card_lt in μ_gt.
    exact μ_gt.
Qed.

Definition ord_suc (α : ord) : ord := ex_val (well_ordered _ (ord_suc_ex α)).

Theorem ord_lt_suc : ∀ α, α < ord_suc α.
Proof.
    intros α.
    apply (ex_proof (well_ordered _ (ord_suc_ex α))).
Qed.

Theorem ord_suc_least : ∀ α β, α < β → ord_suc α ≤ β.
Proof.
    intros α.
    apply (ex_proof (well_ordered _ (ord_suc_ex α))).
Qed.

Theorem ord_le_suc : ∀ α, α ≤ ord_suc α.
Proof.
    intros α.
    apply ord_lt_suc.
Qed.

Theorem ord_le_suc_lt : ∀ α β, ord_suc α ≤ β ↔ α < β.
Proof.
    intros α β.
    split; [>|apply ord_suc_least].
    intros leq.
    apply (lt_le_trans (ord_lt_suc α)).
    exact leq.
Qed.

Theorem ord_sucs_lt : ∀ α β, ord_suc α < ord_suc β ↔ α < β.
Proof.
    intros α β.
    split; intros ltq.
    -   rewrite <- ord_le_suc_lt.
        order_contradiction ltq'.
        rewrite <- ord_le_suc_lt in ltq'.
        contradiction (irrefl _ (lt_le_trans ltq ltq')).
    -   rewrite <- ord_le_suc_lt in ltq.
        order_contradiction leq.
        rewrite ord_le_suc_lt in leq.
        contradiction (irrefl _ (lt_le_trans leq ltq)).
Qed.

Theorem ord_sucs_le : ∀ α β, ord_suc α ≤ ord_suc β ↔ α ≤ β.
Proof.
    intros α β.
    split; intros leq.
    -   order_contradiction ltq.
        apply ord_sucs_lt in ltq.
        contradiction (irrefl _ (le_lt_trans leq ltq)).
    -   order_contradiction ltq.
        rewrite ord_sucs_lt in ltq.
        contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

Theorem ord_suc_eq : ∀ {α β}, ord_suc α = ord_suc β → α = β.
Proof.
    intros α β eq.
    destruct (trichotomy α β) as [[ltq|eq']|ltq].
    -   rewrite <- ord_sucs_lt in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   rewrite <- ord_sucs_lt in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

Theorem ord_lt_suc_le : ∀ α β, α < ord_suc β ↔ α ≤ β.
Proof.
    intros α β.
    rewrite <- ord_sucs_le.
    rewrite ord_le_suc_lt.
    reflexivity.
Qed.

Global Instance ord_zero : Zero ord := {
    zero := to_ord (make_ord_type empty_type _ _ _)
}.

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

Global Instance ord_pos : OrderPositive ord.
Proof.
    split.
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

Theorem ord_zero_suc : ∀ α, 0 ≠ ord_suc α.
Proof.
    intros α.
    assert (0 < ord_suc α) as α_pos.
    {
        apply (le_lt_trans (all_pos α)).
        apply ord_lt_suc.
    }
    apply α_pos.
Qed.

Definition suc_ord (α : ord) := ∃ β, α = ord_suc β.

Definition lim_ord (α : ord) := 0 ≠ α ∧ ¬suc_ord α.

Theorem suc_ord_suc : ∀ α, suc_ord (ord_suc α).
Proof.
    intros α.
    exists α.
    reflexivity.
Qed.

Theorem not_suc_ord : ∀ α, ¬suc_ord α → 0 = α ∨ lim_ord α.
Proof.
    intros α α_nsuc.
    apply or_right.
    intros α_nz.
    split; assumption.
Qed.

Theorem zero_not_suc_ord : ¬suc_ord 0.
Proof.
    intros [α contr].
    contradiction (ord_zero_suc _ contr).
Qed.

Theorem ord_sup_f_zero : ∀ β f, 0 = ord_sup β f → ∀ α, 0 = f α.
Proof.
    intros β f f_z α.
    apply all_neg_eq.
    rewrite f_z.
    apply ord_sup_ge.
Qed.

Theorem ord_sup_constant : ∀ α β, 0 ≠ β → ord_sup β (λ _, α) = α.
Proof.
    intros α β β_nz.
    apply ord_sup_eq.
    -   intros γ.
        apply refl.
    -   intros ε ε_ge.
        exact (ε_ge [0|all_pos2 β_nz]).
Qed.

Theorem ord_lim_gt : ∀ α, lim_ord α → ord_suc 0 < α.
Proof.
    intros α α_lim.
    split.
    -   rewrite ord_le_suc_lt.
        apply all_pos2.
        apply α_lim.
    -   intros eq.
        apply (rand α_lim).
        exists 0.
        symmetry; exact eq.
Qed.

Theorem ord_induction :
    ∀ S : ord → Prop,
    (S 0) →
    (∀ α, S α → S (ord_suc α)) →
    (∀ α, lim_ord α → (∀ β, β < α → S β) → S α) →
    ∀ α, S α.
Proof.
    intros S S0 S_suc S_lim α.
    induction α as [α IHα] using transfinite_induction.
    classic_case (0 = α) as [α_z|α_nz].
    2: classic_case (suc_ord α) as [α_suc|α_nsuc].
    -   rewrite <- α_z.
        exact S0.
    -   destruct α_suc as [β β_eq]; subst α.
        apply S_suc.
        apply IHα.
        apply ord_lt_suc.
    -   apply S_lim; [>|exact IHα].
        split; assumption.
Qed.

Theorem ord_near_lim : ∀ α,
    ∃ n β, ¬suc_ord β ∧ iterate_func ord_suc n β = α.
Proof.
    intros α.
    induction α as [|α IHα|α α_lim IHα] using ord_induction.
    -   exists 0, 0.
        split.
        +   apply zero_not_suc_ord.
        +   reflexivity.
    -   destruct IHα as [n [β [β_lim α_eq]]].
        exists (nat_suc n), β.
        split; [>exact β_lim|].
        cbn.
        rewrite α_eq.
        reflexivity.
    -   exists 0, α.
        split; [>apply α_lim|].
        reflexivity.
Qed.

Theorem ord_far_lim : ∀ α β, α < β → (∀ n, iterate_func ord_suc n α ≠ β) →
    ∃ γ n, lim_ord γ ∧ α < γ ∧ iterate_func ord_suc n γ = β.
Proof.
    assert (∀ α γ n, (∀ m, iterate_func ord_suc m α ≠ iterate_func ord_suc n γ)
        → α < iterate_func ord_suc n γ → α < γ) as lem.
    {
        intros α γ n α_neq α_lt.
        order_contradiction leq.
        rewrite <- not_not in α_neq.
        rewrite not_all in α_neq.
        apply α_neq; clear α_neq.
        nat_induction n.
        -   unfold zero in α_lt; cbn in α_lt.
            contradiction (irrefl _ (lt_le_trans α_lt leq)).
        -   cbn in α_lt.
            classic_case (α = iterate_func ord_suc n γ) as [α_eq|α_neq].
            +   exists 1.
                rewrite not_not.
                unfold one; cbn.
                apply f_equal.
                rewrite α_eq.
                reflexivity.
            +   rewrite ord_lt_suc_le in α_lt.
                specialize (IHn (make_and α_lt α_neq)) as [m eq].
                exists (nat_suc m).
                rewrite not_not in *.
                cbn.
                rewrite eq.
                reflexivity.
    }
    intros α β ltq β_neq.
    pose proof (ord_near_lim β) as [n [γ [γ_nsuc β_eq]]].
    apply not_suc_ord in γ_nsuc as [γ_z|γ_lim].
    -   exfalso.
        subst β γ.
        apply (@not_neg _ _ _ _ _ _ _ α).
        exact (lem α 0 n β_neq ltq).
    -   exists γ, n.
        split; [>exact γ_lim|].
        split; [>|exact β_eq].
        subst β.
        exact (lem α γ n β_neq ltq).
Qed.

Theorem ord_sup_lim_eq : ∀ α, lim_ord α → ord_sup α (λ δ, [δ|]) = α.
Proof.
    intros α α_lim.
    apply antisym.
    -   apply ord_sup_least.
        intros [β β_lt].
        apply β_lt.
    -   apply ord_sup_other_leq.
        intros ε ε_ge.
        order_contradiction ltq.
        rewrite <- ord_le_suc_lt in ltq.
        assert (ord_suc ε ≠ α) as neq.
        {
            intros eq.
            apply (rand α_lim).
            exists ε.
            symmetry; exact eq.
        }
        specialize (ε_ge [ord_suc ε|make_and ltq neq]).
        cbn in ε_ge.
        rewrite <- nlt_le in ε_ge.
        apply ε_ge.
        apply ord_lt_suc.
Qed.

Theorem ord_recursion {X} : ∀
    (f0 : X)
    (f_suc : ord → X → X)
    (f_lim : ∀ α : ord, (set_type (λ β, β < α) → X) → X),
    ∃ g : ord → X,
        (g 0 = f0) ∧
        (∀ α, g (ord_suc α) = f_suc α (g α)) ∧
        (∀ α, lim_ord α → g α = f_lim α (λ x, g [x|])).
Proof.
    intros f0 f_suc f_lim.
    assert (∀ α, suc_ord α → ∃ β : set_type (λ β, β < α), α = ord_suc [β|])
        as suc_ex.
    {
        intros α [β α_eq].
        subst α.
        exists [β|ord_lt_suc β].
        reflexivity.
    }
    pose (f α h :=
        IfH 0 = α
        then
            λ _, f0
        else λ _, (IfH (suc_ord α)
        then
            λ H, f_suc [ex_val (suc_ex α H)|] (h (ex_val (suc_ex α H)))
        else
            λ _, f_lim α h)).
    exists (ex_val (transfinite_recursion X f)).
    rewrite_ex_val g g_eq.
    split; [>|split].
    -   rewrite g_eq.
        unfold f.
        classic_case (0 = 0); [>|contradiction].
        reflexivity.
    -   intros α.
        rewrite g_eq.
        unfold f.
        classic_case (0 = ord_suc α) as [Sα_z|Sα_nz].
        1: contradiction (ord_zero_suc α Sα_z).
        classic_case (suc_ord (ord_suc α)) as [α_suc|α_nsuc].
        2: contradiction (α_nsuc (suc_ord_suc α)).
        rewrite_ex_val α' α'_eq.
        apply ord_suc_eq in α'_eq.
        rewrite <- α'_eq.
        reflexivity.
    -   intros α [α_nz α_nsuc].
        rewrite g_eq.
        unfold f.
        classic_case (0 = α); [>contradiction|].
        classic_case (suc_ord α); [>contradiction|].
        reflexivity.
Qed.

Section OrdSucType.

Context (A : ord_type).

Global Instance plus_one_le : Order (A + singleton_type) := {
    le a b :=
        match a, b with
        | inl a', inl b' => a' ≤ b'
        | inr _, inl _ => False
        | _, inr _ => True
        end
}.

Global Instance plus_one_le_antisym : Antisymmetric le.
Proof.
    split.
    intros a b ab ba.
    unfold le in ab, ba; cbn in *.
    destruct a as [a|s1], b as [b|s2].
    -   rewrite (antisym ab ba).
        reflexivity.
    -   contradiction.
    -   contradiction.
    -   apply f_equal.
        apply singleton_type_eq.
Qed.

Global Instance plus_one_le_wo : WellOrdered le.
Proof.
    split.
    intros S [x Sx].
    classic_case (∃ a, S (inl a)) as [[a Sa]|nSa].
    -   pose (S' a := S (inl a)).
        pose proof (well_ordered S' (ex_intro _ _ Sa)) as [m [Sm m_least]].
        exists (inl m).
        split; [>exact Sm|].
        intros [y|s] Sy.
        +   apply (m_least _ Sy).
        +   exact true.
    -   exists (inr Single).
        split.
        +   destruct x as [a|s].
            *   exfalso; apply nSa.
                exists a.
                exact Sx.
            *   applys_eq Sx.
                apply f_equal.
                apply singleton_type_eq.
        +   intros y Sy.
            destruct y as [a|s].
            *   exfalso; apply nSa.
                exists a.
                exact Sy.
            *   exact true.
Qed.

Definition plus_one_order_type
    := make_ord_type _ _ plus_one_le_antisym plus_one_le_wo : ord_type.

Theorem ord_suc_type : ord_suc (to_ord A) = to_ord plus_one_order_type.
Proof.
    apply antisym.
    -   rewrite ord_le_suc_lt.
        apply ord_lt_simpl.
        exists (inr Single).
        split.
        assert (∀ a, inl a < inr Single) as a_lt.
        {
            intros a.
            split.
            -   exact true.
            -   apply inlr_neq.
        }
        exists (λ a, [inl a|a_lt a]).
        1: split.
        +   split.
            intros a b eq.
            apply set_type_eq in eq; cbn in eq.
            apply inl_eq in eq.
            exact eq.
        +   split.
            intros [a a_lt'].
            destruct a as [a|s].
            *   exists a.
                apply set_type_eq; reflexivity.
            *   destruct a_lt' as [a_le a_neq].
                exfalso.
                rewrite (singleton_type_eq s Single) in a_neq.
                contradiction.
        +   split.
            intros a b leq.
            unfold le; cbn.
            unfold le; cbn.
            exact leq.
    -   pose proof (ord_lt_suc (to_ord A)) as ltq.
        remember (ord_suc (to_ord A)) as B.
        clear HeqB.
        equiv_get_value B.
        apply ord_lt_simpl in ltq as [b [[f]]].
        apply ord_le_simpl.
        exists (λ a, match a with
            | inl a' => [f a'|]
            | inr _ => b
            end).
        split; split.
        +   intros [x|s1] [y|s2] eq.
            *   apply set_type_eq in eq.
                apply inj in eq.
                rewrite eq; reflexivity.
            *   pose proof [|f x] as ltq.
                unfold initial_segment in ltq.
                rewrite eq in ltq.
                contradiction (irrefl _ ltq).
            *   pose proof [|f y] as ltq.
                unfold initial_segment in ltq.
                rewrite eq in ltq.
                contradiction (irrefl _ ltq).
            *   apply f_equal.
                apply singleton_type_eq.
        +   intros [x|s1] [y|s2] xy.
            *   unfold le in xy; cbn in xy.
                apply homo_le in xy.
                exact xy.
            *   apply [|f x].
            *   unfold le in xy; cbn in xy.
                contradiction.
            *   apply refl.
Qed.

End OrdSucType.
