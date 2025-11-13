Require Import init.

Require Export ord_order.
Require Import card_large.

Section OrdBounds.

Context (S : ord → Prop) (S_small : small S).

Definition ord_sup := ex_val (well_ordered _ (ord_small_bounded_le S S_small)).

Theorem ord_sup_ge : ∀ α, S α → α ≤ ord_sup.
Proof.
    apply (ex_proof (well_ordered _ (ord_small_bounded_le S S_small))).
Qed.

Theorem ord_sup_least : ∀ γ, (∀ α, S α → α ≤ γ) → ord_sup ≤ γ.
    apply (ex_proof (well_ordered _ (ord_small_bounded_le S S_small))).
Qed.

Theorem ord_sup_other_leq :
    ∀ γ, (∀ ε, (∀ α, S α → α ≤ ε) → γ ≤ ε) → γ ≤ ord_sup.
Proof.
    intros γ γ_least.
    apply γ_least.
    apply ord_sup_ge.
Qed.

Theorem ord_sup_eq : ∀ γ,
    (∀ α, S α → α ≤ γ) →
    (∀ ε, (∀ α, S α → α ≤ ε) → γ ≤ ε) →
    ord_sup = γ.
Proof.
    intros γ γ_ge γ_least.
    apply antisym.
    -   exact (ord_sup_least _ γ_ge).
    -   exact (ord_sup_other_leq _ γ_least).
Qed.

End OrdBounds.

Theorem ord_sup_set_eq : ∀ S T Ss Ts,
    (∀ x, S x ↔ T x) → ord_sup S Ss = ord_sup T Ts.
Proof.
    intros S T Ss Ts eq.
    apply predicate_ext in eq.
    subst.
    rewrite (proof_irrelevance Ss Ts).
    reflexivity.
Qed.

Theorem ord_sup_in : ∀ α S Ss, α < ord_sup S Ss → ∃ γ, S γ ∧ α < γ.
Proof.
    intros α S Ss ltq.
    classic_contradiction contr.
    rewrite not_ex in contr.
    pose proof (ord_sup_least S Ss α) as leq.
    prove_parts leq.
    {
        intros δ Sδ.
        specialize (contr δ).
        rewrite not_and_impl in contr.
        rewrite <- nlt_le.
        exact (contr Sδ).
    }
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

Theorem ord_sup_leq_sup : ∀ S T Ss Ts,
    (∀ α, S α → ∃ α', T α' ∧ α ≤ α') → ord_sup S Ss ≤ ord_sup T Ts.
Proof.
    intros S T Ss Ts ge_ex.
    apply ord_sup_least.
    intros α Sα.
    apply ord_sup_other_leq.
    intros ε ε_ge.
    specialize (ge_ex α Sα) as [α' [Tα' leq]].
    exact (trans leq (ε_ge α' Tα')).
Qed.

Theorem ord_sup_constant : ∀ S Ss α,
    S α → (∀ γ, S γ → γ = α) → ord_sup S Ss = α.
Proof.
    intros S Ss α Sα α_eq.
    apply ord_sup_eq.
    -   intros γ Sγ.
        apply α_eq in Sγ.
        subst; apply refl.
    -   intros ε ε_ge.
        apply (ε_ge α Sα).
Qed.

Theorem ord_sup_union : ∀ S Ss,
    initial_segment (ord_sup S Ss) = ⋃ (image_under initial_segment S).
Proof.
    intros S Ss.
    unfold initial_segment in *.
    apply antisym.
    -   intros β β_lt.
        apply ord_sup_in in β_lt as [γ [Sγ β_lt]].
        exists (initial_segment γ).
        split.
        +   exists γ.
            split; [>exact Sγ|reflexivity].
        +   exact β_lt.
    -   intros β [T [[γ [Sγ T_eq]] Tγ]]; subst T.
        apply (lt_le_trans Tγ).
        apply ord_sup_ge.
        exact Sγ.
Qed.

Definition ord_f_sup (β : ord) (f : set_type (λ δ, δ < β) → ord) :=
    ord_sup _ (ord_initial_image_small β f).

Theorem ord_f_sup_f_eq : ∀ β f g, (∀ x, f x = g x) →
    ord_f_sup β f = ord_f_sup β g.
Proof.
    intros β f g eq.
    apply functional_ext in eq.
    subst g.
    reflexivity.
Qed.

Theorem ord_f_sup_ge β f : ∀ α, f α ≤ ord_f_sup β f.
Proof.
    intros α.
    apply ord_sup_ge.
    exists α; reflexivity.
Qed.

Theorem ord_f_sup_least β f : ∀ γ, (∀ α, f α ≤ γ) → ord_f_sup β f ≤ γ.
    intros γ γ_ge.
    apply ord_sup_least.
    intros α' [α α_eq]; subst α'.
    apply γ_ge.
Qed.

Theorem ord_f_sup_other_leq β f :
    ∀ γ, (∀ ε, (∀ α, f α ≤ ε) → γ ≤ ε) → γ ≤ ord_f_sup β f.
Proof.
    intros γ γ_least.
    apply γ_least.
    apply ord_f_sup_ge.
Qed.

Theorem ord_f_sup_eq β f : ∀ γ,
    (∀ α, f α ≤ γ) →
    (∀ ε, (∀ α, f α ≤ ε) → γ ≤ ε) →
    ord_f_sup β f = γ.
Proof.
    intros γ γ_ge γ_least.
    apply antisym.
    -   exact (ord_f_sup_least _ _ _ γ_ge).
    -   exact (ord_f_sup_other_leq _ _ _ γ_least).
Qed.

Theorem ord_f_sup_in β f : ∀ α, α < ord_f_sup β f → ∃ γ, α < f γ.
Proof.
    intros α ltq.
    pose proof (ord_sup_in α _ (ord_initial_image_small β f) ltq)
        as [γ' [[γ γ_eq] γ_gt]]; subst γ'.
    exists γ.
    exact γ_gt.
Qed.

Theorem ord_f_sup_leq_sup : ∀ β1 β2 f g,
    (∀ α, ∃ α', f α ≤ g α') → ord_f_sup β1 f ≤ ord_f_sup β2 g.
Proof.
    intros β1 β2 f g ge_ex.
    apply ord_sup_leq_sup.
    intros α' [α α_eq]; subst α'.
    specialize (ge_ex α) as [α' leq].
    exists (g α').
    split; [>exists α'; reflexivity | exact leq].
Qed.
