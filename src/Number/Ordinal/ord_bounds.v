Require Import init.

Require Export ord_order.
Require Import card_large.

Section OrdBounds.

Context (β : ord) (f : set_type (λ α, α < β) → ord).

Definition ord_lub := ex_val (well_ordered _ (ord_initial_small_le β f)).

Definition ord_lsub := ex_val (well_ordered _ (ord_initial_small β f)).

Theorem ord_lub_ge : ∀ α, f α ≤ ord_lub.
Proof.
    apply (ex_proof (well_ordered _ (ord_initial_small_le β f))).
Qed.

Theorem ord_lub_least : ∀ γ, (∀ α, f α ≤ γ) → ord_lub ≤ γ.
    apply (ex_proof (well_ordered _ (ord_initial_small_le β f))).
Qed.

Theorem ord_lub_other_leq : ∀ γ, (∀ ε, (∀ α, f α ≤ ε) → γ ≤ ε) → γ ≤ ord_lub.
Proof.
    intros γ γ_least.
    apply γ_least.
    apply ord_lub_ge.
Qed.

Theorem ord_lub_eq : ∀ γ,
    (∀ α, f α ≤ γ) →
    (∀ ε, (∀ α, f α ≤ ε) → γ ≤ ε) →
    ord_lub = γ.
Proof.
    intros γ γ_ge γ_least.
    apply antisym.
    -   exact (ord_lub_least _ γ_ge).
    -   exact (ord_lub_other_leq _ γ_least).
Qed.

Theorem ord_lsub_gt : ∀ α, f α < ord_lsub.
Proof.
    apply (ex_proof (well_ordered _ (ord_initial_small β f))).
Qed.

Theorem ord_lsub_least : ∀ γ, (∀ α, f α < γ) → ord_lsub ≤ γ.
    apply (ex_proof (well_ordered _ (ord_initial_small β f))).
Qed.

Theorem ord_lsub_other_leq : ∀ γ, (∀ ε, (∀ α, f α < ε) → γ ≤ ε) → γ ≤ ord_lsub.
Proof.
    intros γ γ_least.
    apply γ_least.
    apply ord_lsub_gt.
Qed.

Theorem ord_lsub_eq : ∀ γ,
    (∀ α, f α < γ) →
    (∀ ε, (∀ α, f α < ε) → γ ≤ ε) →
    ord_lsub = γ.
Proof.
    intros γ γ_ge γ_least.
    apply antisym.
    -   exact (ord_lsub_least _ γ_ge).
    -   exact (ord_lsub_other_leq _ γ_least).
Qed.

End OrdBounds.

Theorem ord_lsub_self_eq : ∀ β : ord, ord_lsub β (λ α, [α|]) = β.
Proof.
    intros β.
    apply ord_lsub_eq.
    -   intros α.
        exact [|α].
    -   intros ε ε_ge.
        order_contradiction contr.
        contradiction (irrefl _ (ε_ge [ε|contr])).
Qed.

Theorem ord_lub_f_eq : ∀ β f g, (∀ x, f x = g x) → ord_lub β f = ord_lub β g.
Proof.
    intros β f g eq.
    apply f_equal.
    apply functional_ext.
    exact eq.
Qed.

Theorem ord_lsub_f_eq : ∀ β f g, (∀ x, f x = g x) → ord_lsub β f = ord_lsub β g.
Proof.
    intros β f g eq.
    apply f_equal.
    apply functional_ext.
    exact eq.
Qed.

Theorem ord_lsub_in : ∀ α β f, α < ord_lsub β f → ∃ γ, α ≤ f γ.
Proof.
    intros α β f ltq.
    classic_contradiction contr.
    rewrite not_ex in contr.
    pose proof (ord_lsub_least _ f α) as leq.
    prove_parts leq.
    {
        intros δ.
        rewrite <- nle_lt.
        apply contr.
    }
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

Theorem ord_lub_in : ∀ α β f, α < ord_lub β f → ∃ γ, α < f γ.
Proof.
    intros α β f ltq.
    classic_contradiction contr.
    rewrite not_ex in contr.
    pose proof (ord_lub_least _ f α) as leq.
    prove_parts leq.
    {
        intros δ.
        rewrite <- nlt_le.
        apply contr.
    }
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.
