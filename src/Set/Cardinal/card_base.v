Require Import init.

Require Import set.
Require Import function.
Require Import well_order.
Require Import nat.
Require Import ord_basic.

Declare Scope card_scope.
Delimit Scope card_scope with card.

(* begin hide *)
Section CardEquiv.

Let card_eq A B := ∃ f : A → B, bijective f.

Local Infix "~" := card_eq.

Lemma card_eq_reflexive : ∀ A, A ~ A.
Proof.
    intros A.
    exists identity.
    exact identity_bijective.
Qed.
Instance card_eq_reflexive_class : Reflexive _ := {
    refl := card_eq_reflexive
}.

Lemma card_eq_symmetric : ∀ A B, A ~ B → B ~ A.
Proof.
    intros A B [f f_bij].
    exists (bij_inv f f_bij).
    apply bij_inv_bij.
Qed.
Instance card_eq_symmetric_class : Symmetric _ := {
    sym := card_eq_symmetric
}.

Lemma card_eq_transitive : ∀ A B C, A ~ B → B ~ C → A ~ C.
Proof.
    intros A B C [f f_bij] [g g_bij].
    exists (λ x, g (f x)).
    split.
    -   intros a b eq.
        apply g_bij in eq.
        apply f_bij in eq.
        exact eq.
    -   intros c.
        pose proof (rand g_bij c) as [b b_eq].
        pose proof (rand f_bij b) as [a a_eq].
        exists a.
        subst.
        reflexivity.
Qed.
Instance card_eq_transitive_class : Transitive _ := {
    trans := card_eq_transitive
}.

End CardEquiv.
(* end hide *)
Definition card_equiv := make_equiv _
    card_eq_reflexive_class card_eq_symmetric_class card_eq_transitive_class.

Notation "a ~ b" := (eq_equal card_equiv a b) : card_scope.

Notation "'card'" := (equiv_type card_equiv).

Notation "| A |" := (to_equiv_type card_equiv A) (at level 30) : card_scope.

(* begin hide *)
Open Scope card_scope.

Lemma ord_to_card_wd : ∀ A B : ord_type,
    (eq_equal ord_equiv A B) → |ord_U A| = |ord_U B|.
Proof.
    intros A B [f [f_bij f_iso]].
    equiv_simpl.
    exists f.
    exact f_bij.
Qed.
(* end hide *)
Definition nat_to_card (n : nat) := |set_type (λ x, x < n)|.
Definition ord_to_card := unary_op ord_to_card_wd.

(* begin hide *)
Lemma card_to_initial_ord_ex :
    ∀ κ, ∃ α, ord_to_card α = κ ∧ ∀ β, ord_to_card β = κ → α ≤ β.
Proof.
    intros κ.
    assert (∃ δ, ord_to_card δ = κ) as α_ex.
    {
        rename κ into A.
        equiv_get_value A.
        exists (to_equiv_type ord_equiv (make_ord_type A _ wo_le_wo)).
        unfold ord_to_card; equiv_simpl.
        exists identity.
        exact identity_bijective.
    }
    pose proof (well_founded _ α_ex) as [α [Sα α_min]].
    exists α.
    split; try exact Sα.
    intros β eq.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    destruct contr.
    apply (α_min _ eq); assumption.
Qed.
(* end hide *)
Definition card_to_initial_ord κ := ex_val (card_to_initial_ord_ex κ).

Theorem card_to_initial_ord_to_card_eq :
    ∀ κ, ord_to_card (card_to_initial_ord κ) = κ.
Proof.
    intros κ.
    unfold card_to_initial_ord.
    rewrite_ex_val α α_eq.
    apply α_eq.
Qed.

Theorem card_to_initial_ord_le :
    ∀ κ α, ord_to_card α = κ → card_to_initial_ord κ ≤ α.
Proof.
    intros κ α eq.
    unfold card_to_initial_ord.
    rewrite_ex_val β β_eq.
    apply β_eq.
    exact eq.
Qed.

Theorem card_to_initial_ord_eq :
    ∀ κ μ, card_to_initial_ord κ = card_to_initial_ord μ → κ = μ.
Proof.
    intros κ μ eq.
    apply (f_equal ord_to_card) in eq.
    do 2 rewrite card_to_initial_ord_to_card_eq in eq.
    exact eq.
Qed.

Theorem ord_to_card_to_initial_ord_le :
    ∀ α, card_to_initial_ord (ord_to_card α) ≤ α.
Proof.
    intros α.
    apply card_to_initial_ord_le.
    reflexivity.
Qed.

Theorem card_from_set_type_eq {U} : ∀ (X : U → Prop) (B : set_type X → Prop),
    |set_type (from_set_type B)| = |set_type B|.
Proof.
    intros X B.
    equiv_simpl.
    exists (λ x : set_type (from_set_type B),
        [[[x|] | ldand [|x]] | rdand [|x]]).
    split.
    -   intros [a a_in] [b b_in] eq.
        inversion eq as [eq2]; clear eq.
        apply set_type_eq; cbn.
        exact eq2.
    -   intros [y By].
        assert (from_set_type B [y|]) as y_in.
        {
            split with [|y].
            applys_eq By.
            apply set_type_simpl.
        }
        exists [_|y_in].
        apply set_type_eq; cbn.
        apply set_type_simpl.
Qed.
(* begin hide *)
Close Scope card_scope.
(* end hide *)
