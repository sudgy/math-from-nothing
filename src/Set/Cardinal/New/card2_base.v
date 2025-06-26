Require Import init.

Require Export set.
Require Import well_order.

Require Import ord2_order.

Declare Scope card_scope.
Delimit Scope card_scope with card.

Section CardEquiv.

Let card_eq A B := ∃ f : A → B, Bijective f.

Local Infix "~" := card_eq.

Global Instance card_eq_reflexive_class : Reflexive card_eq.
Proof.
    split.
    intros A.
    exists identity.
    exact identity_bijective.
Qed.

Global Instance card_eq_symmetric_class : Symmetric card_eq.
Proof.
    split.
    intros A B [f f_bij].
    exists (bij_inv f).
    apply bij_inv_bij.
Qed.

Global Instance card_eq_transitive_class : Transitive card_eq.
Proof.
    split.
    intros A B C [f f_bij] [g g_bij].
    exists (λ x, g (f x)).
    apply bij_comp; assumption.
Qed.

End CardEquiv.

Definition card_equiv := make_equiv _
    card_eq_reflexive_class card_eq_symmetric_class card_eq_transitive_class.

Notation "a ~ b" := (eq_equal card_equiv a b) : card_scope.

Notation "'card'" := (equiv_type card_equiv).

Notation "| A |" := (to_equiv card_equiv A) (at level 30) : card_scope.

Open Scope card_scope.

Lemma ord_to_card_wd : ∀ A B : ord_type, (A ~ B)%ord → |ord_U A| = |ord_U B|.
Proof.
    intros A B [f].
    equiv_simpl.
    exists f.
    apply f.
Qed.

Definition ord_to_card := unary_op ord_to_card_wd.

Lemma card_to_initial_ord_ex :
    ∀ κ, ∃ α, ord_to_card α = κ ∧ ∀ β, ord_to_card β = κ → α ≤ β.
Proof.
    intros A.
    apply well_ordered.
    equiv_get_value A.
    exists (to_ord (make_ord_type A _ wo_antisym wo_wo)).
    unfold ord_to_card; equiv_simpl.
    exists identity.
    exact identity_bijective.
Qed.

Definition card_to_initial_ord κ := ex_val (card_to_initial_ord_ex κ).

Theorem card_to_initial_ord_to_card_eq :
    ∀ κ, ord_to_card (card_to_initial_ord κ) = κ.
Proof.
    intros κ.
    apply (ex_proof (card_to_initial_ord_ex κ)).
Qed.

Theorem card_to_initial_ord_least :
    ∀ κ α, ord_to_card α = κ → card_to_initial_ord κ ≤ α.
Proof.
    intros κ α eq.
    apply (ex_proof (card_to_initial_ord_ex κ)).
    exact eq.
Qed.

Global Instance card_to_initial_ord_inj : Injective card_to_initial_ord.
Proof.
    split.
    intros κ μ eq.
    apply (f_equal ord_to_card) in eq.
    do 2 rewrite card_to_initial_ord_to_card_eq in eq.
    exact eq.
Qed.

Theorem ord_to_card_to_initial_ord_le :
    ∀ α, card_to_initial_ord (ord_to_card α) ≤ α.
Proof.
    intros α.
    apply card_to_initial_ord_least.
    reflexivity.
Qed.

Theorem ord_to_card_eq1 : ∀ α B,
    (∃ f : set_type (initial_segment α) → B, Bijective f) → ord_to_card α = |B|.
Proof.
    intros A B [f f_bij].
    equiv_get_value A.
    unfold ord_to_card; equiv_simpl.
    exists (λ a, f (ord_type_init_ord A a)).
    apply bij_comp; [>|exact f_bij].
    apply ord_type_init_ord_bij.
Qed.

Theorem ord_to_card_eq2 : ∀ α B,
    (∃ f : B → set_type (initial_segment α), Bijective f) → |B| = ord_to_card α.
Proof.
    intros α B [f f_bij].
    symmetry; apply ord_to_card_eq1.
    exists (bij_inv f).
    apply bij_inv_bij.
Qed.

Theorem ord_to_card_init : ∀ A a,
    ord_to_card (ord_type_init_ord_base A a) = |set_type (initial_segment a)|.
Proof.
    intros A a.
    symmetry; apply ord_to_card_eq2.
    pose proof (ord_type_init_ord_base_le A).
    pose proof (ord_type_init_ord_base_inj A).
    pose proof (ord_type_init_ord_bij A).
    assert (∀ (x : set_type (initial_segment a)),
        ord_type_init_ord_base A [x|] < ord_type_init_ord_base A a) as lt.
    {
        intros [x x_lt]; cbn.
        rewrite <- homo_lt2.
        exact x_lt.
    }
    exists (λ x, [ord_type_init_ord_base A [x|]|lt x]).
    split; split.
    -   intros [x x_lt] [y y_lt]; cbn.
        intros eq.
        apply set_type_eq2.
        rewrite set_type_eq2 in eq.
        apply inj in eq.
        exact eq.
    -   intros [γ γ_lt].
        pose proof (ord_type_init_ord_in a) as ltq.
        unfold initial_segment in *.
        pose proof (sur (ord_type_init_ord A) [γ|trans γ_lt ltq]) as [x x_eq].
        unfold ord_type_init_ord in x_eq.
        rewrite set_type_eq2 in x_eq.
        pose proof γ_lt as x_lt.
        rewrite <- x_eq in x_lt.
        apply homo_lt2 in x_lt.
        exists [x|x_lt].
        apply set_type_eq; cbn.
        exact x_eq.
Qed.

Close Scope card_scope.
