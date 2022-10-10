Require Import init.

Require Export ord_order.
Require Import ord_plus.
Require Import ord_mult.
Require Import set.
Require Import nat.

Theorem transfinite_induction :
    ∀ S : ord → Prop, (∀ α, (∀ β, β < α → S β) → S α) → ∀ α, S α.
Proof.
    intros S S_all α.
    classic_contradiction contr.
    pose (S' α := ¬S α).
    assert (∃ β, S' β) as S'_nempty by (exists α; exact contr).
    pose proof (well_ordered S' S'_nempty) as [β [S'β β_min]].
    apply S'β.
    apply S_all.
    intros γ γ_lt.
    classic_contradiction S'γ.
    specialize (β_min _ S'γ).
    destruct (lt_le_trans γ_lt β_min); contradiction.
Qed.

Definition suc_ord α := ∃ β, α = β + 1.
Definition lim_ord α := 0 ≠ α ∧ ¬suc_ord α.

Theorem transfinite_induction2 :
    ∀ S : ord → Prop,
    (∀ α, suc_ord α → (∀ β, β < α → S β) → S α) →
    (∀ α, ¬suc_ord α → (∀ β, β < α → S β) → S α) →
    ∀ α, S α.
Proof.
    intros S sucs lims α.
    induction α using transfinite_induction.
    classic_case (suc_ord α).
    -   apply sucs; assumption.
    -   apply lims; assumption.
Qed.

Theorem transfinite_induction3 :
    ∀ S : ord → Prop,
    S 0 →
    (∀ α, suc_ord α → (∀ β, β < α → S β) → S α) →
    (∀ α, lim_ord α → (∀ β, β < α → S β) → S α) →
    ∀ α, S α.
Proof.
    intros S S0 sucs lims α.
    induction α using transfinite_induction2.
    -   apply sucs; assumption.
    -   classic_case (0 = α) as [eq|neq].
        +   rewrite <- eq.
            exact S0.
        +   apply lims; try assumption.
            split; assumption.
Qed.

Theorem ord_lt_plus1 : ∀ α, α < α + 1.
Proof.
    intros α.
    apply ord_lt_self_rplus.
    apply ord_not_trivial.
Qed.
