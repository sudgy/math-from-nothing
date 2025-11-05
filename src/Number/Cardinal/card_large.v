Require Import init.

Require Export card_order.
Require Import ord_order.
Require Import set_induction.

Open Scope card_scope.

Definition small {U} (S : U → Prop) :=
    ∃ (X : Type) (f : X → set_type S), Surjective f.

Theorem empty_small {U} : small (empty (U := U)).
Proof.
    exists False.
    exists (λ x, False_rect _ x).
    split.
    intros [y y_in].
    contradiction y_in.
Qed.

Theorem singleton_small {U} : ∀ x : U, small ❴x❵.
Proof.
    intros x.
    exists True.
    exists (λ _, [x|Logic.eq_refl]).
    split.
    intros [y y_eq].
    exists true.
    apply set_type_eq; cbn.
    exact y_eq.
Qed.

Section CardLarge.

Context (S : card → Prop) (S_small : small S).
Let X := ex_val S_small.
Let f := ex_val (ex_proof S_small) : X → set_type S.
Let f_suc := ex_proof (ex_proof S_small) : Surjective f.

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

Theorem card_small_bounded : ∃ B, ∀ a, S a → a < B.
Proof.
    exists (|card_large_val → Prop|).
    intros A SA.
    apply (le_lt_trans2 (power_set_bigger _)).
    equiv_get_value A.
    unfold le; equiv_simpl.
    pose proof f_suc.
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

Theorem small_image_under {A B} : ∀ (f : A → B) (S : A → Prop),
    small S → small (image_under f S).
Proof.
    intros f S [X [g g_sur]].
    exists X.
    exists (λ x, [f [g x|] | image_under_in [|g x]]).
    split.
    intros [y' [y [Sy y'_eq]]]; subst y'.
    pose proof (sur g [y|Sy]) as [x x_eq].
    exists x.
    apply set_type_eq; cbn.
    rewrite x_eq.
    reflexivity.
Qed.

Theorem small_image {A B} : ∀ (S : A → Prop) (S_small : small S),
    ∀ f : set_type S → B, small (image f).
Proof.
    intros S [X [g g_sur]] f.
    exists X.
    exists (λ x, [f (g x) | ex_intro _ _ Logic.eq_refl]).
    split.
    intros [y' [y y_eq]]; subst y'.
    pose proof (sur g y) as [x x_eq].
    exists x.
    apply set_type_eq; cbn.
    rewrite x_eq.
    reflexivity.
Qed.

Theorem ord_small_bounded : ∀ S : ord → Prop, small S → ∃ γ, ∀ α, S α → α < γ.
Proof.
    intros S S_small.
    apply (small_image_under ord_to_card) in S_small.
    apply card_small_bounded in S_small as [μ μ_gt].
    exists (card_to_initial_ord μ).
    intros α Sα.
    apply ord_to_card_lt.
    rewrite card_to_initial_ord_to_card_eq.
    apply μ_gt.
    exists α.
    split; [>exact Sα|reflexivity].
Qed.

Theorem ord_small_bounded_le :
    ∀ S : ord → Prop, small S → ∃ γ, ∀ α, S α → α ≤ γ.
Proof.
    intros S S_small.
    apply ord_small_bounded in S_small as [γ γ_gt].
    exists γ.
    intros α Sα.
    apply (γ_gt α Sα).
Qed.

Theorem ord_initial_small : ∀ (β : ord), small (λ δ, δ < β).
Proof.
    intros B.
    equiv_get_value B.
    exists B.
    exists (ord_type_init_ord B).
    apply ord_type_init_ord_bij.
Qed.

Theorem ord_initial_image_small {X} :
    ∀ (β : ord) (g : set_type (λ x, x < β) → X), small (image g).
Proof.
    intros β g.
    apply small_image.
    apply ord_initial_small.
Qed.

Theorem small_bij_ex {U} : ∀ S : U → Prop, small S →
    ∃ X (f : X → set_type S), Bijective f.
Proof.
    intros S [X [f f_sur]].
    pose (T (x : X) := ∃ y, x = ex_val (sur f y)).
    exists (set_type T).
    exists (λ x, f [x|]).
    split; split.
    -   intros [a' [a a'_eq]] [b' [b b'_eq]] eq; subst a' b'.
        cbn in eq.
        apply set_type_eq; cbn.
        rewrite (ex_proof (sur f a)) in eq.
        rewrite (ex_proof (sur f b)) in eq.
        subst b.
        reflexivity.
    -   intros y.
        exists [ex_val (sur f y) | ex_intro _ _ Logic.eq_refl]; cbn.
        rewrite_ex_val x x_eq.
        exact x_eq.
Qed.

Definition small_set_to_card {U} (S : U → Prop) S_small :=
    |ex_val (small_bij_ex S S_small)|.

Theorem small_set_to_card_eq {U} (S : U → Prop) S_small :
    ∀ X (f : X → set_type S), Bijective f → small_set_to_card S S_small = |X|.
Proof.
    intros X f f_bij.
    unfold small_set_to_card.
    rewrite_ex_val Y [g g_bij].
    equiv_simpl.
    exists (λ x, bij_inv f (g x)).
    apply bij_comp.
    -   exact g_bij.
    -   apply bij_inv_bij.
Qed.

Definition aleph'_base (β : ord) (g : set_type (λ x, x < β) → card) :=
    ex_val (well_ordered _
        (card_small_bounded (image g) (ord_initial_image_small β g))).

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
    apply μ_gt.
    exists [α|ltq].
    reflexivity.
Qed.

Theorem aleph'_least : ∀ α μ, (∀ β, β < α → aleph' β < μ) → aleph' α ≤ μ.
Proof.
    intros α μ μ_gt.
    rewrite aleph'_eq.
    unfold aleph'_base.
    rewrite_ex_val κ [κ_gt κ_least].
    apply κ_least.
    intros ν [[β β_lt] ν_eq]; subst ν.
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
