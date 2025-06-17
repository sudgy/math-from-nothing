Require Import init.

Require Export ord2_order.
Require Import set_induction.

Require Import card2_large.

Open Scope ord_scope.

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

Module OrdPlusDef.
Section OrdPlusDef.

Context (α : ord).

Definition f (β : ord) (g : set_type (λ x, x < β) → ord) :=
    If 0 = β then α else
    ex_val (well_ordered _ (ord_initial_small _ g)).

Definition g := ex_val (transfinite_recursion _ f).
Lemma g_eq : ∀ β : ord, g β = f β (λ δ : set_type (λ δ, δ < β), g [δ|]).
Proof.
    exact (ex_proof (transfinite_recursion _ f)).
Qed.

End OrdPlusDef.
End OrdPlusDef.

Global Instance ord_plus : Plus ord := {
    plus α β := OrdPlusDef.g α β
}.

Global Instance ord_plus_rid : PlusRid ord.
Proof.
    split.
    intros α.
    unfold plus; cbn.
    rewrite OrdPlusDef.g_eq.
    unfold OrdPlusDef.f.
    classic_case (0 = 0) as [eq|neq].
    -   reflexivity.
    -   contradiction.
Qed.

Definition ord_plus_set α β := λ γ, ∀ δ, δ < β → α + δ < γ.

Theorem ord_plus_ind : ∀ α β, 0 ≠ β → is_least le (ord_plus_set α β) (α + β).
Proof.
    intros α β β_nz.
    unfold ord_plus_set.
    unfold plus at 2; cbn.
    rewrite OrdPlusDef.g_eq.
    unfold OrdPlusDef.f.
    rewrite (if_false β_nz).
    rewrite_ex_val γ [γ_le γ_least].
    split.
    -   intros δ δ_lt.
        exact (γ_le [δ|δ_lt]).
    -   intros y y_gt.
        apply γ_least.
        intros [δ δ_lt].
        exact (y_gt δ δ_lt).
Qed.

Theorem ord_plus_eq : ∀ α β γ, 0 ≠ β → is_least le (ord_plus_set α β) γ →
    γ = α + β.
Proof.
    intros α β γ β_nz γ_least.
    pose proof (ord_plus_ind α β β_nz) as αβ_least.
    apply antisym.
    -   apply γ_least.
        apply αβ_least.
    -   apply αβ_least.
        apply γ_least.
Qed.

Global Instance ord_plus_lid : PlusLid ord.
Proof.
    split.
    intros α.
    induction α as [α IHα] using transfinite_induction.
    classic_case (0 = α) as [α_z|α_nz].
    1: subst; apply plus_rid.
    symmetry; apply (ord_plus_eq _ _ _ α_nz).
    unfold ord_plus_set; split.
    -   intros δ δ_lt.
        rewrite IHα by exact δ_lt.
        exact δ_lt.
    -   intros y y_gt.
        classic_contradiction ltq.
        rewrite nle_lt in ltq.
        specialize (y_gt _ ltq).
        rewrite IHα in y_gt by exact ltq.
        contradiction (irrefl _ y_gt).
Qed.

Theorem ord_lt_lplus : ∀ {α β} γ, α < β → γ + α < γ + β.
Proof.
    intros α β γ ltq.
    apply ord_plus_ind.
    -   intros contr.
        subst β.
        rewrite <- nle_lt in ltq.
        apply ltq.
        apply ord_pos.
    -   exact ltq.
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

Theorem ord_le_self_rplus : ∀ α β, α ≤ α + β.
Proof.
    intros α β.
    rewrite <- plus_rid at 1.
    apply le_lplus.
    apply ord_pos.
Qed.

Theorem ord_le_self_lplus : ∀ α β, α ≤ β + α.
Proof.
    intros α β.
    induction α as [α IHα] using transfinite_induction.
    classic_contradiction ltq.
    rewrite nle_lt in ltq.
    specialize (IHα _ ltq).
    apply (ord_lt_lplus β) in ltq.
    pose proof (le_lt_trans IHα ltq) as contr.
    contradiction (irrefl _ contr).
Qed.

Theorem ord_le_ex : ∀ α β, α ≤ β → ∃ γ, α + γ = β.
Proof.
    intros α β leq.
    classic_case (α = β) as [eq|neq].
    {
        subst.
        exists 0.
        apply plus_rid.
    }
    pose (S γ := β ≤ α + γ).
    pose proof (well_ordered S) as γ_ex.
    prove_parts γ_ex.
    {
        exists β.
        unfold S.
        apply ord_le_self_lplus.
    }
    destruct γ_ex as [γ [γ_lt γ_least]].
    assert (0 ≠ γ) as γ_nz.
    {
        intros contr.
        subst.
        unfold S in γ_lt.
        rewrite plus_rid in γ_lt.
        pose proof (antisym leq γ_lt).
        contradiction.
    }
    exists γ.
    symmetry; apply (ord_plus_eq _ _ _ γ_nz).
    unfold ord_plus_set; split.
    -   intros δ δ_lt.
        unfold S in γ_least.
        classic_contradiction contr.
        rewrite nlt_le in contr.
        specialize (γ_least _ contr).
        contradiction (irrefl _ (le_lt_trans γ_least δ_lt)).
    -   intros x x_gt.
        unfold S in γ_lt.
        apply (trans γ_lt).
        apply (ord_plus_ind α γ γ_nz).
        exact x_gt.
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
    classic_contradiction leq.
    rewrite nlt_le in leq.
    apply (le_lplus γ) in leq.
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

Theorem ord_nz_rplus : ∀ α β, 0 ≠ β → 0 ≠ α + β.
Proof.
    intros α β β_nz contr.
    pose proof (ord_plus_ind α β β_nz) as ind.
    rewrite <- contr in ind.
    destruct ind as [ltq C0]; clear C0.
    specialize (ltq 0 (ord_pos2 _ β_nz)).
    rewrite <- nle_lt in ltq.
    contradiction (ltq (ord_pos _)).
Qed.

Theorem ord_nz_lplus : ∀ α β, 0 ≠ α → 0 ≠ α + β.
Proof.
    intros α β α_nz.
    classic_case (0 = β) as [eq|neq].
    -   subst.
        rewrite plus_rid.
        exact α_nz.
    -   apply ord_nz_rplus.
        exact neq.
Qed.

Global Instance ord_plus_assoc : PlusAssoc ord.
Proof.
    split.
    intros α β γ.
    induction γ as [γ IHγ] using transfinite_induction.
    classic_case (0 = γ) as [eq|neq].
    {
        subst.
        do 2 rewrite plus_rid.
        reflexivity.
    }
    apply (ord_plus_eq _ _ _ neq).
    unfold ord_plus_set; split.
    -   intros δ δ_lt.
        rewrite <- IHγ by exact δ_lt.
        do 2 apply lt_lplus.
        exact δ_lt.
    -   intros ε ε_gt.
        apply ord_plus_ind; [>apply (ord_nz_rplus _ _ neq)|].
        unfold ord_plus_set.
        intros δ δ_lt.
        classic_case (β ≤ δ) as [leq|ltq].
        +   apply ord_le_ex in leq as [ζ ζ_ex].
            subst δ.
            apply ord_lt_plus_lcancel in δ_lt.
            specialize (ε_gt ζ δ_lt).
            rewrite IHγ by exact δ_lt.
            exact ε_gt.
        +   rewrite nle_lt in ltq.
            apply (lt_lplus α) in ltq.
            apply (trans ltq).
            specialize (ε_gt 0).
            rewrite plus_rid in ε_gt.
            apply ε_gt.
            apply ord_pos2.
            exact neq.
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

Close Scope ord_scope.
