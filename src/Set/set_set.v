Require Import init.

Require Export set_base.
Require Export function.

Notation "⋃ S" := (λ x, ∃ A, S A ∧ A x) (at level 45).
Notation "⋂ S" := (λ x, ∀ A, S A → A x) (at level 45).

Definition image_under_collection {U V} (f : U → V) (S : (U → Prop) → Prop)
    := λ Y, ∃ X, S X ∧ Y = image_under f X.
Definition inverse_image_collection {U V} (f : U → V) (T : (V → Prop) → Prop)
    := λ X, ∃ Y, T Y ∧ X = inverse_image f Y.

Definition collection2 {U} (A B : U → Prop) := λ S, S = A ∨ S = B.

Theorem inverse_union {U V} : ∀ (f : U → V) S,
    inverse_image f (⋃ S) = ⋃ (inverse_image_collection f S).
Proof.
    intros f S.
    apply antisym.
    -   intros x [A [SA Afx]].
        exists (inverse_image f A).
        split.
        +   exists A.
            split; trivial.
        +   exact Afx.
    -   intros x [A [[Y [SY A_eq]] Ax]].
        rewrite A_eq in Ax.
        exists Y.
        split; assumption.
Qed.

Theorem collection2_union {U} : ∀ A B : U → Prop, A ∪ B = ⋃ (collection2 A B).
Proof.
    intros A B.
    apply antisym.
    -   intros x [Ax|Bx].
        +   exists A.
            split.
            *   left.
                reflexivity.
            *   exact Ax.
        +   exists B.
            split.
            *   right.
                reflexivity.
            *   exact Bx.
    -   intros x [S [[SA|SB] Sx]]; subst S.
        +   left; exact Sx.
        +   right; exact Sx.
Qed.

Theorem collection2_inter {U} : ∀ A B : U → Prop, A ∩ B = ⋂ (collection2 A B).
Proof.
    intros A B.
    apply antisym.
    -   intros x [Ax Bx].
        intros S [SA|SB]; subst.
        +   exact Ax.
        +   exact Bx.
    -   intros x x_in.
        split; apply x_in.
        +   left.
            reflexivity.
        +   right.
            reflexivity.
Qed.

Theorem union_empty {U} : ⋃ (empty (U := U → Prop)) = ∅.
Proof.
    apply not_ex_empty.
    intros x [A [C Ax]].
    exact C.
Qed.

Theorem union_singleton {U} : ∀ S : U → Prop, S = ⋃ singleton S.
Proof.
    intros S.
    apply predicate_ext.
    intros x; split.
    -   intros Sx.
        exists S.
        split.
        +   reflexivity.
        +   exact Sx.
    -   intros [A [AS Ax]].
        rewrite AS.
        exact Ax.
Qed.

Theorem inter_singleton {U} : ∀ S : U → Prop, S = ⋂ singleton S.
Proof.
    intros S.
    apply antisym.
    -   intros x Sx A AS.
        rewrite <- AS.
        exact Sx.
    -   intros x Ax.
        apply Ax.
        reflexivity.
Qed.

Theorem big_union_compl {U} : ∀ SS : (U → Prop) → Prop,
    complement (⋃ SS) = ⋂ (λ S, SS (complement S)).
Proof.
    intros SS.
    apply predicate_ext.
    intros x; split; intros x_in.
    -   intros A SSA.
        classic_contradiction nAx.
        apply x_in.
        exists (complement A).
        split; assumption.
    -   intros [A [SSA Ax]].
        specialize (x_in (complement A)).
        rewrite compl_compl in x_in.
        specialize (x_in SSA).
        contradiction.
Qed.

Theorem big_inter_compl {U} : ∀ SS : (U → Prop) → Prop,
    complement (⋂ SS) = ⋃ (λ S, SS (complement S)).
Proof.
    intros SS.
    apply predicate_ext.
    intros x; split; intros x_in.
    -   classic_contradiction contr.
        apply x_in.
        intros A SSA.
        classic_contradiction nAx.
        apply contr; clear contr.
        exists (complement A).
        rewrite compl_compl.
        split; assumption.
    -   intros contr.
        destruct x_in as [A [SSA Ax]].
        specialize (contr _ SSA).
        contradiction.
Qed.

Theorem empty_union {U} : ⋃ ∅ = (empty (U := U)).
Proof.
    apply antisym.
    -   intros x [A [A_in x_in]].
        contradiction A_in.
    -   intros x x_in.
        contradiction x_in.
Qed.
