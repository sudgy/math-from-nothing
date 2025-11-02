Require Import init.

Require Export ord_nat.
Require Import set_induction.

Lemma ord_family_derivative_ex :
    ∀ (α : ord) (f : set_type (λ δ, δ < α) → OrdNormalFunction) (β : ord)
    (g : set_type (λ δ, δ < β) → ord),
    ∃ γ, (∀ δ, f δ γ = γ) ∧ (∀ δ, g δ < γ).
Proof.
    intros α f β g.
    pose proof (ord_normal_family_fixed α f (ord_suc (ord_sup β g)))
        as [γ [γ_geq γ_eq]].
    exists γ.
    split; [>exact γ_eq|].
    rewrite ord_le_suc_lt in γ_geq.
    intros δ.
    apply (le_lt_trans2 γ_geq).
    apply ord_sup_ge.
Qed.

Definition ord_family_derivative_base
    (α : ord) (f : set_type (λ δ, δ < α) → OrdNormalFunction) : ord → ord :=
    ex_val (transfinite_recursion ord
    (λ β g, ex_val (well_ordered _ (ord_family_derivative_ex α f β g)))).

Lemma ord_family_derivative_base_fixed :
    ∀ α (f : set_type (λ δ, δ < α) → OrdNormalFunction) δ β,
    f δ (ord_family_derivative_base α f β) = ord_family_derivative_base α f β.
Proof.
    intros α f δ β.
    unfold ord_family_derivative_base.
    rewrite_ex_val g g_eq.
    specialize (g_eq β).
    rewrite_ex_val γ [[γ_eq γ_gt] γ_least].
    rewrite g_eq.
    apply γ_eq.
Qed.

Lemma ord_family_derivative_base_gt :
    ∀ α (f : set_type (λ δ, δ < α) → OrdNormalFunction) β,
    ∀ δ, δ < β →
    ord_family_derivative_base α f δ < ord_family_derivative_base α f β.
Proof.
    intros α f β δ ltq.
    unfold ord_family_derivative_base.
    rewrite_ex_val g g_eq.
    specialize (g_eq β).
    rewrite_ex_val γ [[γ_eq γ_gt] γ_least].
    rewrite g_eq.
    exact (γ_gt [δ|ltq]).
Qed.

Lemma ord_family_derivative_base_least :
    ∀ α (f : set_type (λ δ, δ < α) → OrdNormalFunction) β,
    ∀ γ, (∀ δ, f δ γ = γ) → (∀ δ, δ < β → ord_family_derivative_base α f δ < γ)→
    ord_family_derivative_base α f β ≤ γ.
Proof.
    intros α f β γ γ_eq γ_gt.
    unfold ord_family_derivative_base in *.
    rewrite_ex_val g g_eq.
    specialize (g_eq β).
    rewrite_ex_val δ [[δ_eq δ_gt] δ_least].
    rewrite g_eq.
    apply δ_least.
    split; [>exact γ_eq|].
    intros ε.
    apply γ_gt.
    exact [|ε].
Qed.

Lemma ord_family_derivative_normal :
    ∀ α f, OrdNormal (ord_family_derivative_base α f).
Proof.
    intros α f.
    split.
    intros γ γ_lim.
    apply antisym.
    -   apply ord_family_derivative_base_least.
        +   intros δ.
            rewrite (ord_normal_sup (f δ)) by apply γ_lim.
            apply ord_sup_f_eq.
            intros x.
            apply ord_family_derivative_base_fixed.
        +   intros δ δ_lt.
            pose proof (ord_lt_suc δ) as ltq.
            apply (ord_family_derivative_base_gt α f) in ltq.
            apply (lt_le_trans ltq).
            apply (ord_lim_suc _ _ γ_lim) in δ_lt.
            apply (trans2 (ord_sup_ge _ _ [ord_suc δ|δ_lt])).
            apply refl.
    -   apply ord_sup_least.
        intros [β β_lt]; cbn.
        apply ord_family_derivative_base_gt.
        exact β_lt.
Qed.

Lemma ord_family_derivative_le : ∀ α f,
    HomomorphismLe (ord_family_derivative_base α f).
Proof.
    intros α f.
    split.
    intros a b leq.
    classic_case (a = b) as [eq|neq].
    -   subst; apply refl.
    -   apply ord_family_derivative_base_gt.
        split; assumption.
Qed.

Lemma ord_family_derivative_inj : ∀ α f,
    Injective (ord_family_derivative_base α f).
Proof.
    intros α f.
    split.
    intros a b eq.
    destruct (trichotomy a b) as [[ltq|eq']|ltq].
    -   apply (ord_family_derivative_base_gt α f) in ltq.
        rewrite eq in ltq; contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply (ord_family_derivative_base_gt α f) in ltq.
        rewrite eq in ltq; contradiction (irrefl _ ltq).
Qed.

Definition ord_family_derivative
    (α : ord) (f : set_type (λ δ, δ < α) → OrdNormalFunction)
    : OrdNormalFunction :=
    make_ord_normal_function
        (ord_family_derivative_base α f)
        (ord_family_derivative_normal α f)
        (ord_family_derivative_le α f)
        (ord_family_derivative_inj α f).
Arguments ord_family_derivative : simpl never.

Theorem ord_family_derivative_fixed :
    ∀ α (f : set_type (λ δ, δ < α) → OrdNormalFunction) δ β,
    f δ (ord_family_derivative α f β) = ord_family_derivative α f β.
Proof.
    apply ord_family_derivative_base_fixed.
Qed.

Theorem ord_family_derivative_least :
    ∀ α (f : set_type (λ δ, δ < α) → OrdNormalFunction) β,
    ∀ γ, (∀ δ, f δ γ = γ) → (∀ δ, δ < β → ord_family_derivative α f δ < γ) →
    ord_family_derivative α f β ≤ γ.
Proof.
    apply ord_family_derivative_base_least.
Qed.

Definition ord_derivative (f : OrdNormalFunction) :=
    ord_family_derivative 1 (λ _, f).
Arguments ord_derivative : simpl never.

Theorem ord_derivative_fixed : ∀ (f : OrdNormalFunction) α,
    f (ord_derivative f α) = ord_derivative f α.
Proof.
    intros f α.
    unfold ord_derivative.
    rewrite <- (ord_family_derivative_fixed) at 2; [>reflexivity|].
    exists 0.
    apply ord_one_pos.
Qed.

Theorem ord_derivative_least : ∀ (f : OrdNormalFunction) α,
    ∀ β, f β = β → (∀ δ, δ < α → ord_derivative f δ < β) →
    ord_derivative f α ≤ β.
Proof.
    intros f α β β_eq β_gt.
    apply ord_family_derivative_least.
    -   intro; exact β_eq.
    -   intros δ δ_lt.
        apply β_gt.
        exact δ_lt.
Qed.
