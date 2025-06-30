Require Import init.

Require Export card_order.
Require Import ord_order.
Require Import set_induction.

Open Scope card_scope.

Section CardLarge.

Context (S : card → Prop) (X : Type)
    (f : X → set_type S) (f_sur : Surjective f).

Record card_large_val := make_card_large_val {
    S_X : X;
    S_x : ex_val (to_equiv_ex [f S_X|]);
}.

Lemma card_large_val_eq1 : ∀ A B, A = B → S_X A = S_X B.
Proof.
    intros A B eq.
    subst; reflexivity.
Qed.

Definition card_large_cast {A B} (H : A = B) (a : ex_val (to_equiv_ex [f A|]))
    : ex_val (to_equiv_ex [f B|]).
Proof.
    destruct H.
    exact a.
Defined.

Lemma card_large_val_eq2 : ∀ A B (H : A = B),
    card_large_cast (card_large_val_eq1 A B H) (S_x A) = S_x B.
Proof.
    intros A B eq.
    unfold card_large_cast; cbn.
    destruct eq.
    rewrite (proof_irrelevance _ Logic.eq_refl).
    reflexivity.
Qed.

Lemma card_large_val_eq : ∀ A x y,
    make_card_large_val A x = make_card_large_val A y → x = y.
Proof.
    intros A x y eq.
    pose proof (card_large_val_eq2 _ _ eq) as eq2.
    cbn in eq2.
    unfold card_large_cast in eq2.
    rewrite (proof_irrelevance _ Logic.eq_refl) in eq2.
    exact eq2.
Qed.

Lemma card_large_f_eq : ∀ x, |ex_val (to_equiv_ex [f x|])| = [f x|].
Proof.
    intros x.
    exact (ex_proof (to_equiv_ex [f x|])).
Qed.

Theorem card_large_set : ∃ B, ∀ a, S a → a < B.
Proof.
    exists (|card_large_val → Prop|).
    intros A SA.
    apply (le_lt_trans2 (power_set_bigger _)).
    equiv_get_value A.
    unfold le; equiv_simpl.
    pose proof (sur f [(|A|)|SA]) as [x fx].
    symmetry in fx.
    apply set_type_eq in fx; cbn in fx.
    rewrite <- card_large_f_eq in fx.
    equiv_simpl in fx.
    destruct fx as [g g_bij].
    exists (λ a, make_card_large_val x (g a)).
    split.
    intros a b eq.
    apply card_large_val_eq in eq.
    apply inj in eq.
    exact eq.
Qed.

End CardLarge.

Theorem card_large : ∀ X (f : X → card), ∃ B, ∀ x, f x < B.
Proof.
    intros X f.
    pose proof (card_large_set (λ A, ∃ x, f x = A) X
        (λ x, [f x|ex_intro _ _ Logic.eq_refl])) as B_ex.
    prove_parts B_ex.
    {
        split.
        intros [y [x]]; subst y.
        exists x.
        reflexivity.
    }
    destruct B_ex as [B B_gt].
    exists B.
    intros x.
    apply B_gt.
    exists x.
    reflexivity.
Qed.

Theorem ord_large : ∀ X (f : X → ord), ∃ B, ∀ x, f x < B.
Proof.
    intros X f.
    pose proof (card_large X (λ x, ord_to_card (f x))) as [B B_gt].
    exists (card_to_initial_ord B).
    intros x.
    specialize (B_gt x).
    apply ord_to_card_lt.
    rewrite card_to_initial_ord_to_card_eq.
    exact B_gt.
Qed.

Theorem ord_initial_small :
    ∀ (β : ord) (f : set_type (initial_segment β) → ord), ∃ γ, ∀ α, f α < γ.
Proof.
    intros B f.
    equiv_get_value B.
    pose proof (ord_large _ (λ b, f (ord_type_init_ord B b))) as [β β_gt].
    exists β.
    intros α.
    pose proof (ord_type_init_ord_bij B).
    pose proof (sur _ α) as [a a_eq]; subst α.
    apply β_gt.
Qed.

Theorem ord_initial_small_le :
    ∀ (β : ord) (f : set_type (initial_segment β) → ord), ∃ γ, ∀ α, f α ≤ γ.
Proof.
    intros β f.
    destruct (ord_initial_small β f) as [γ γ_ltq].
    exists γ.
    intros α.
    apply γ_ltq.
Qed.

Theorem ord_card_large : ∀ (β : ord) (f : set_type (initial_segment β) → card),
    ∃ μ, ∀ α, f α < μ.
Proof.
    intros β f.
    pose proof (ord_initial_small β (λ α, card_to_initial_ord (f α)))
        as [γ γ_gt].
    pose proof (card_unbounded (ord_to_card γ)) as [μ μ_gt].
    exists μ.
    intros α.
    apply (homo_lt2 (f := card_to_initial_ord)).
    rewrite <- card_to_initial_ord_to_card_eq in μ_gt.
    apply ord_to_card_lt in μ_gt.
    exact (trans (γ_gt α) μ_gt).
Qed.

Definition aleph'_base (β : ord) (g : set_type (λ x, x < β) → card) :=
    ex_val (well_ordered _ (ord_card_large _ g)).

Definition aleph' := ex_val (transfinite_recursion _ aleph'_base).

Theorem aleph'_eq : ∀ α : ord,
    aleph' α = aleph'_base α (λ β : set_type (λ β, β < α), aleph' [β|]).
Proof.
    exact (ex_proof (transfinite_recursion _ aleph'_base)).
Qed.

Theorem aleph'_gt : ∀ α β, α < β → aleph' α < aleph' β.
Proof.
    intros α β ltq.
    rewrite (aleph'_eq β).
    unfold aleph'_base.
    rewrite_ex_val μ [μ_gt μ_least].
    exact (μ_gt [α|ltq]).
Qed.

Theorem aleph'_least : ∀ α μ, (∀ β, β < α → aleph' β < μ) → aleph' α ≤ μ.
Proof.
    intros α μ μ_gt.
    rewrite aleph'_eq.
    unfold aleph'_base.
    rewrite_ex_val κ [κ_gt κ_least].
    apply κ_least.
    intros [β β_lt].
    exact (μ_gt β β_lt).
Qed.

Global Instance aleph'_inj : Injective aleph'.
Proof.
    split.
    intros α β eq.
    destruct (trichotomy α β) as [[ltq|eq']|ltq].
    -   apply aleph'_gt in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply aleph'_gt in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

Global Instance aleph'_le : HomomorphismLe aleph'.
Proof.
    split.
    intros α β leq.
    classic_case (α = β) as [eq|neq].
    -   subst.
        apply refl.
    -   apply aleph'_gt.
        split; assumption.
Qed.

Lemma aleph'_sur1 : ∀ μ, ∃ α, μ ≤ aleph' α.
Proof.
    intros μ.
    exists (card_to_initial_ord μ).
    induction μ as [μ IHμ] using transfinite_induction.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    specialize (IHμ _ contr).
    do 2 apply homo_le2 in IHμ.
    contradiction (irrefl _ (le_lt_trans IHμ contr)).
Qed.

Global Instance aleph'_sur : Surjective aleph'.
Proof.
    split.
    intros κ.
    pose proof (well_ordered _ (aleph'_sur1 κ)) as [α [α_ge α_least]].
    exists α.
    apply antisym.
    2: exact α_ge.
    apply aleph'_least.
    intros β ltq.
    classic_contradiction leq.
    rewrite nlt_le in leq.
    specialize (α_least _ leq).
    contradiction (irrefl _ (le_lt_trans α_least ltq)).
Qed.

Close Scope card_scope.
