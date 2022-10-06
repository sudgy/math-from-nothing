Require Import init.

Require Export set_base.
Require Export set_function.

Notation "⋃ S" := (λ x, ∃ A, S A ∧ A x) (at level 45).
Notation "⋂ S" := (λ x, ∀ A, S A → A x) (at level 45).

Definition image_under_collection {U V} (f : U → V) (S : (U → Prop) → Prop)
    := λ Y, ∃ X, S X ∧ Y = image_under f X.
Definition inverse_image_collection {U V} (f : U → V) (T : (V → Prop) → Prop)
    := λ X, ∃ Y, T Y ∧ X = inverse_image f Y.

Theorem union_empty {U} : ⋃ (empty (U := U → Prop)) = ∅.
Proof.
    apply empty_eq.
    intros x [A [C Ax]].
    exact C.
Qed.

Theorem inter_empty {U} : ⋂ (empty (U := U → Prop)) = all.
Proof.
    apply all_eq.
    intros x A A_in.
    contradiction A_in.
Qed.

Theorem union_singleton {U} : ∀ S : U → Prop, ⋃ ❴S❵ = S.
Proof.
    intros S.
    apply antisym.
    -   intros x [A [AS Ax]].
        rewrite AS.
        exact Ax.
    -   intros x Sx.
        exists S.
        split.
        +   reflexivity.
        +   exact Sx.
Qed.

Theorem inter_singleton {U} : ∀ S : U → Prop, ⋂ ❴S❵ = S.
Proof.
    intros S.
    apply antisym.
    -   intros x Ax.
        apply Ax.
        reflexivity.
    -   intros x Sx A AS.
        rewrite <- AS.
        exact Sx.
Qed.

Theorem union_pair {U} : ∀ A B : U → Prop, ⋃ ❴A, B❵ = A ∪ B.
Proof.
    intros A B.
    apply antisym.
    -   intros x [S [[SA|SB] Sx]]; subst S.
        +   left; exact Sx.
        +   right; exact Sx.
    -   intros x [Ax|Bx].
        +   exists A.
            split; [>|exact Ax].
            left.
            reflexivity.
        +   exists B.
            split; [>|exact Bx].
            right.
            reflexivity.
Qed.

Theorem inter_pair {U} : ∀ A B : U → Prop, ⋂ ❴A, B❵ = A ∩ B.
Proof.
    intros A B.
    apply antisym.
    -   intros x x_in.
        split; apply x_in.
        +   left.
            reflexivity.
        +   right.
            reflexivity.
    -   intros x [Ax Bx].
        intros S [SA|SB]; subst.
        +   exact Ax.
        +   exact Bx.
Qed.

Theorem big_union_compl {U} : ∀ SS : (U → Prop) → Prop,
    𝐂 (⋃ SS) = ⋂ (λ S, SS (𝐂 S)).
Proof.
    intros SS.
    apply predicate_ext.
    intros x; split; intros x_in.
    -   intros A SSA.
        classic_contradiction nAx.
        apply x_in.
        exists (𝐂 A).
        split; assumption.
    -   intros [A [SSA Ax]].
        specialize (x_in (𝐂 A)).
        rewrite compl_compl in x_in.
        exact (x_in SSA Ax).
Qed.

Theorem big_inter_compl {U} : ∀ SS : (U → Prop) → Prop,
    𝐂 (⋂ SS) = ⋃ (λ S, SS (𝐂 S)).
Proof.
    intros SS.
    apply predicate_ext.
    intros x; split; intros x_in.
    -   unfold 𝐂 in x_in.
        rewrite not_all in x_in.
        destruct x_in as [A x_in].
        rewrite not_impl in x_in.
        destruct x_in as [SSa nAx].
        exists (𝐂 A).
        rewrite compl_compl.
        split; assumption.
    -   intros contr.
        destruct x_in as [A [SSA Ax]].
        specialize (contr _ SSA).
        contradiction.
Qed.

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
