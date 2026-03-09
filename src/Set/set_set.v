Require Import init.

Require Export set_base.
Require Export set_function.

Notation "⋃ S" := (λ x, ∃ A, S A ∧ A x) (at level 45).
Notation "⋂ S" := (λ x, ∀ A, S A → A x) (at level 45).

Definition image_under_collection {U V} (f : U → V) (S : (U → Prop) → Prop)
    := λ Y, ∃ X, S X ∧ Y = image_under f X.
Definition inverse_image_collection {U V} (f : U → V) (T : (V → Prop) → Prop)
    := λ X, ∃ Y, T Y ∧ X = inverse_image f Y.

Theorem union_sub {U} : ∀ SS : (U → Prop) → Prop, ∀ S, SS S → S ⊆ ⋃ SS.
Proof.
    intros SS S SS_S x Sx.
    exists S.
    split; assumption.
Qed.

Theorem inter_sub {U} : ∀ SS : (U → Prop) → Prop, ∀ S, SS S → ⋂ SS ⊆ S.
Proof.
    intros SS S SS_S.
    intros x Sx.
    apply Sx.
    exact SS_S.
Qed.

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

Theorem union_rec {U} : ∀ (A : U → Prop) (S : (U → Prop) → Prop),
    ⋃ (❴A❵ ∪ S) = A ∪ (⋃ S).
Proof.
    intros A S.
    apply antisym.
    -   intros x [B [B_in Bx]].
        destruct B_in as [AB|SB].
        +   left.
            rewrite AB.
            exact Bx.
        +   right.
            exists B.
            split; assumption.
    -   intros x [Ax|[B [SB Bx]]].
        +   exists A.
            split; [>|exact Ax].
            left.
            reflexivity.
        +   exists B.
            split; [>|exact Bx].
            right.
            exact SB.
Qed.

Theorem inter_rec {U} : ∀ (A : U → Prop) (S : (U → Prop) → Prop),
    ⋂ (❴A❵ ∪ S) = A ∩ (⋂ S).
Proof.
    intros A S.
    apply antisym.
    -   intros x x_in.
        split.
        +   apply x_in.
            left.
            reflexivity.
        +   intros B SB.
            apply x_in.
            right.
            exact SB.
    -   intros x [Ax x_in] B [AB|SB].
        +   rewrite <- AB.
            exact Ax.
        +   apply x_in.
            exact SB.
Qed.

Theorem union_singleton {U} : ∀ S : U → Prop, ⋃ ❴S❵ = S.
Proof.
    intros S.
    rewrite <- (union_rid ❴S❵).
    rewrite union_rec.
    rewrite union_empty.
    apply union_rid.
Qed.

Theorem inter_singleton {U} : ∀ S : U → Prop, ⋂ ❴S❵ = S.
Proof.
    intros S.
    rewrite <- (union_rid ❴S❵).
    rewrite inter_rec.
    rewrite inter_empty.
    apply inter_rid.
Qed.

Theorem union_pair {U} : ∀ A B : U → Prop, ⋃ ❴A, B❵ = A ∪ B.
Proof.
    intros A B.
    rewrite pair_union.
    rewrite union_rec.
    rewrite union_singleton.
    reflexivity.
Qed.

Theorem inter_pair {U} : ∀ A B : U → Prop, ⋂ ❴A, B❵ = A ∩ B.
Proof.
    intros A B.
    rewrite pair_union.
    rewrite inter_rec.
    rewrite inter_singleton.
    reflexivity.
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

Theorem big_union_union {U} : ∀ SS TT : (U → Prop) → Prop,
    (⋃ SS) ∪ (⋃ TT) = ⋃ (SS ∪ TT).
Proof.
    intros SS TT.
    apply antisym.
    -   intros x [SSx|TTx].
        +   destruct SSx as [S [SS_S Sx]].
            exists S.
            split; [>|exact Sx].
            left.
            exact SS_S.
        +   destruct TTx as [T [TT_T Tx]].
            exists T.
            split; [>|exact Tx].
            right.
            exact TT_T.
    -   intros x [S [S_in Sx]].
        destruct S_in as [SS_S|TT_S].
        +   left.
            exists S.
            split; assumption.
        +   right.
            exists S.
            split; assumption.
Qed.

Theorem big_inter_inter {U} : ∀ SS TT : (U → Prop) → Prop,
    (⋂ SS) ∩ (⋂ TT) = ⋂ (SS ∪ TT).
Proof.
    intros SS TT.
    apply antisym.
    -   intros x [SS_x TT_x] A A_in.
        destruct A_in as [SS_A|TT_A].
        +   exact (SS_x A SS_A).
        +   exact (TT_x A TT_A).
    -   intros x x_in.
        split.
        +   intros A SS_A.
            apply x_in.
            left.
            exact SS_A.
        +   intros A TT_A.
            apply x_in.
            right.
            exact TT_A.
Qed.
