Require Import init.

Require Export ord_order.
Require Import card_large.

Section OrdBounds.

Context (β : ord) (f : set_type (λ α, α < β) → ord).

Definition ord_sup := ex_val (well_ordered _ (ord_initial_small_le β f)).

Theorem ord_sup_ge : ∀ α, f α ≤ ord_sup.
Proof.
    apply (ex_proof (well_ordered _ (ord_initial_small_le β f))).
Qed.

Theorem ord_sup_least : ∀ γ, (∀ α, f α ≤ γ) → ord_sup ≤ γ.
    apply (ex_proof (well_ordered _ (ord_initial_small_le β f))).
Qed.

Theorem ord_sup_other_leq : ∀ γ, (∀ ε, (∀ α, f α ≤ ε) → γ ≤ ε) → γ ≤ ord_sup.
Proof.
    intros γ γ_least.
    apply γ_least.
    apply ord_sup_ge.
Qed.

Theorem ord_sup_eq : ∀ γ,
    (∀ α, f α ≤ γ) →
    (∀ ε, (∀ α, f α ≤ ε) → γ ≤ ε) →
    ord_sup = γ.
Proof.
    intros γ γ_ge γ_least.
    apply antisym.
    -   exact (ord_sup_least _ γ_ge).
    -   exact (ord_sup_other_leq _ γ_least).
Qed.

End OrdBounds.

Theorem ord_sup_f_eq : ∀ β f g, (∀ x, f x = g x) → ord_sup β f = ord_sup β g.
Proof.
    intros β f g eq.
    apply f_equal.
    apply functional_ext.
    exact eq.
Qed.

Theorem ord_sup_in : ∀ α β f, α < ord_sup β f → ∃ γ, α < f γ.
Proof.
    intros α β f ltq.
    classic_contradiction contr.
    rewrite not_ex in contr.
    pose proof (ord_sup_least _ f α) as leq.
    prove_parts leq.
    {
        intros δ.
        rewrite <- nlt_le.
        apply contr.
    }
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

Theorem ord_sup_leq_sup : ∀ β f g,
    (∀ α, ∃ α', f α ≤ g α') → ord_sup β f ≤ ord_sup β g.
Proof.
    intros β f g ge_ex.
    apply ord_sup_least.
    intros α.
    apply ord_sup_other_leq.
    intros ε ε_ge.
    specialize (ge_ex α) as [α' leq].
    exact (trans leq (ε_ge α')).
Qed.
