Require Import init.

Require Export ord2_order.
Require Import set_induction.

Require Import ord2_bounds.

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

Theorem ord_pos2 : ∀ {α}, 0 ≠ α → 0 < α.
Proof.
    intros α neq.
    split.
    -   apply ord_pos.
    -   exact neq.
Qed.

Theorem ord_neg_eq : ∀ {α}, α ≤ 0 → 0 = α.
Proof.
    intros α leq.
    apply antisym.
    -   apply ord_pos.
    -   exact leq.
Qed.

Theorem ord_neg : ∀ {α}, ¬(α < 0).
Proof.
    intros α.
    rewrite nlt_le.
    apply ord_pos.
Qed.

Theorem ord_lsub_f_zero : ∀ β f, 0 = ord_lsub β f → 0 = β.
Proof.
    intros β f f_z.
    classic_contradiction neq.
    pose proof (ord_lsub_gt β f [0|ord_pos2 neq]) as ltq.
    rewrite <- f_z in ltq.
    contradiction (ord_neg ltq).
Qed.

Theorem ord_lub_f_zero : ∀ β f, 0 = ord_lub β f → ∀ α, 0 = f α.
Proof.
    intros β f f_z α.
    apply ord_neg_eq.
    rewrite f_z.
    apply ord_lub_ge.
Qed.

Theorem ord_lub_constant : ∀ α β, 0 ≠ β → ord_lub β (λ _, α) = α.
Proof.
    intros α β β_nz.
    apply ord_lub_eq.
    -   intros γ.
        apply refl.
    -   intros ε ε_ge.
        exact (ε_ge [0|ord_pos2 β_nz]).
Qed.

Module OrdPlusDef.
Section OrdPlusDef.

Context (α : ord).

Definition f (β : ord) (g : set_type (λ x, x < β) → ord) :=
    If 0 = β then α else (ord_lsub β g).

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
    rewrite (if_true Logic.eq_refl).
    reflexivity.
Qed.

Theorem ord_plus_lsub : ∀ α β, 0 ≠ β → α + β = ord_lsub β (λ δ, α + [δ|]).
Proof.
    intros α β β_nz.
    unfold plus; cbn.
    rewrite OrdPlusDef.g_eq at 1.
    unfold OrdPlusDef.f.
    rewrite (if_false β_nz).
    reflexivity.
Qed.

Global Instance ord_plus_lid : PlusLid ord.
Proof.
    split.
    intros α.
    induction α as [α IHα] using transfinite_induction.
    classic_case (0 = α) as [α_z|α_nz].
    1: subst; apply plus_rid.
    rewrite ord_plus_lsub by exact α_nz.
    rewrite <- ord_lsub_self_eq.
    apply ord_lsub_f_eq.
    intros [δ δ_lt]; cbn.
    apply IHα.
    exact δ_lt.
Qed.

Theorem ord_lt_lplus : ∀ {α β} γ, α < β → γ + α < γ + β.
Proof.
    intros α β γ ltq.
    rewrite (ord_plus_lsub γ β).
    -   exact (ord_lsub_gt β (λ δ, γ + [δ|]) [α|ltq]).
    -   intros contr.
        subst β.
        contradiction (ord_neg ltq).
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
    order_contradiction ltq.
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
    pose proof (well_ordered (λ γ, β ≤ α + γ)) as γ_ex.
    prove_parts γ_ex.
    {
        exists β.
        apply ord_le_self_lplus.
    }
    destruct γ_ex as [γ [γ_lt γ_least]].
    assert (0 ≠ γ) as γ_nz.
    {
        intros contr.
        subst.
        rewrite plus_rid in γ_lt.
        pose proof (antisym leq γ_lt).
        contradiction.
    }
    exists γ.
    rewrite ord_plus_lsub by exact γ_nz.
    apply ord_lsub_eq.
    -   intros [δ δ_lt]; cbn.
        order_contradiction contr.
        specialize (γ_least _ contr).
        contradiction (irrefl _ (le_lt_trans γ_least δ_lt)).
    -   intros x x_gt.
        apply (trans γ_lt).
        rewrite ord_plus_lsub by exact γ_nz.
        apply ord_lsub_least.
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
    order_contradiction leq.
    apply (le_lplus γ) in leq.
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

Theorem ord_nz_rplus : ∀ α β, 0 ≠ β → 0 ≠ α + β.
Proof.
    intros α β β_nz contr.
    rewrite ord_plus_lsub in contr by exact β_nz.
    pose proof (ord_lsub_gt β (λ δ, α + [δ|])) as ltq.
    rewrite <- contr in ltq.
    specialize (ltq [0|ord_pos2 β_nz]).
    contradiction (ord_neg ltq).
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

Theorem ord_lsub_plus : ∀ α β f, 0 ≠ β →
    α + ord_lsub β f = ord_lsub β (λ x, α + f x).
Proof.
    intros α β f β_nz.
    pose proof (contrapositive (ord_lsub_f_zero β f) β_nz) as f_nz.
    apply antisym.
    -   rewrite ord_plus_lsub by exact f_nz.
        apply ord_lsub_least.
        intros [δ δ_lt]; cbn.
        pose proof (ord_lsub_in _ _ _ δ_lt) as [γ γ_ge].
        apply (le_lplus α) in γ_ge.
        apply (le_lt_trans γ_ge).
        apply (ord_lsub_gt β (λ x, α + f x)).
    -   apply ord_lsub_least.
        intros δ.
        apply ord_lt_lplus.
        apply ord_lsub_gt.
Qed.

Theorem ord_lub_plus : ∀ α β f, 0 ≠ β →
    α + ord_lub β f = ord_lub β (λ x, α + f x).
Proof.
    intros α β f β_nz.
    classic_case (0 = ord_lub β f) as [f_z|f_nz].
    {
        rewrite <- f_z.
        rewrite plus_rid.
        rewrite <- (ord_lub_constant α β) at 1 by exact β_nz.
        apply ord_lub_f_eq.
        intros x.
        rewrite <- (ord_lub_f_zero _ _ f_z).
        symmetry; apply plus_rid.
    }
    apply antisym.
    -   rewrite ord_plus_lsub by exact f_nz.
        apply ord_lsub_least.
        intros [δ δ_lt]; cbn.
        pose proof (ord_lub_in _ _ _ δ_lt) as [γ γ_ge].
        apply (lt_lplus α) in γ_ge.
        apply (lt_le_trans γ_ge).
        apply (ord_lub_ge β (λ x, α + f x)).
    -   apply ord_lub_least.
        intros δ.
        apply le_lplus.
        apply ord_lub_ge.
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
    rewrite (ord_plus_lsub β γ) by exact neq.
    rewrite ord_lsub_plus by exact neq.
    rewrite ord_plus_lsub by exact neq.
    apply ord_lsub_f_eq.
    intros [δ δ_lt]; cbn.
    apply IHγ.
    exact δ_lt.
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
    order_contradiction contr.
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
