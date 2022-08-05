(** This file contains several basic logical theorems such as De Morgan's laws.
*)

Require Export base_logic.
Require Export ext_rewrite.

Theorem not_not : ∀ P, (¬¬P) = P.
    intro P.
    apply propositional_ext.
    split; intro PH.
    -   classic_case P as [PH'|PH'].
        +   exact PH'.
        +   contradiction (PH PH').
    -   intro PH'.
        contradiction (PH' PH).
Qed.
Theorem not_not_impl : ∀ P, ¬¬P → P.
    intros P.
    rewrite not_not.
    trivial.
Qed.
Theorem not_not_impl2 : ∀ P : Prop, P → ¬¬P.
    intros P.
    rewrite not_not.
    trivial.
Qed.
Ltac classic_contradiction_prop H := apply not_not_impl; intros H.

Theorem not_impl : ∀ A B : Prop, (¬(A → B)) = (A ∧ ¬B).
    intros A B.
    apply propositional_ext.
    split.
    -   intros n.
        classic_case B.
        +   assert (A → B) by (intro; exact b).
            contradiction.
        +   split; try exact n0.
            classic_case A; try assumption.
            assert (A → B) by (intro; contradiction).
            contradiction.
    -   intros [a b] ab.
        specialize (ab a).
        contradiction.
Qed.
Theorem not_and : ∀ A B, (¬(A ∧ B)) = (¬A ∨ ¬B).
    intros A B.
    apply propositional_ext.
    split.
    -   intros n.
        classic_case A.
        +   classic_case B.
            *   assert (A ∧ B) by (split; assumption).
                contradiction.
            *   right; exact n0.
        +   left; exact n0.
    -   intros [na|nb] [a b]; contradiction.
Qed.
Theorem not_or : ∀ A B, (¬(A ∨ B)) = (¬A ∧ ¬B).
    intros A B.
    apply propositional_ext.
    split.
    -   intro n.
        split; intro.
        +   assert (A ∨ B) by (left; assumption).
            contradiction.
        +   assert (A ∨ B) by (right; assumption).
            contradiction.
    -   intros [na nb] [a|b]; contradiction.
Qed.
Theorem not_ex : ∀ {U} (P : U → Prop), (¬(∃ a, P a)) = (∀ a, ¬P a).
    intros U P.
    apply propositional_ext.
    split.
    -   intros not_ex a Pa.
        apply not_ex.
        exists a.
        exact Pa.
    -   intros all [a Pa].
        specialize (all a).
        contradiction.
Qed.

Theorem not_all : ∀ {U} (P : U → Prop), equal (¬(∀ a, P a)) (∃ a, ¬P a).
    intros U P.
    apply propositional_ext.
    split.
    -   intro not_all.
        classic_contradiction_prop H.
        rewrite not_ex in H.
        setoid_rewrite not_not in H.
        contradiction.
    -   intros [a a_not] all.
        specialize (all a).
        contradiction.
Qed.

Theorem not_and_impl : ∀ A B, (¬(A ∧ B)) = (A → ¬B).
    intros A B.
    rewrite <- (not_not (A → ¬B)).
    rewrite not_impl.
    rewrite not_not.
    reflexivity.
Qed.

Theorem and_comm : ∀ A B, (A ∧ B) = (B ∧ A).
    intros A B.
    apply propositional_ext; split.
    all: intros [P1 P2].
    all: split; assumption.
Qed.

Theorem or_comm : ∀ A B, (A ∨ B) = (B ∨ A).
    intros A B.
    apply propositional_ext; split.
    all: intros [P1|P2].
    -   right; exact P1.
    -   left; exact P2.
    -   right; exact P1.
    -   left; exact P2.
Qed.

Theorem and_or_ldist : ∀ A B C, (A ∧ (B ∨ C)) = ((A ∧ B) ∨ (A ∧ C)).
    intros A B C.
    apply propositional_ext; split.
    -   intros [PA [PB|PC]].
        +   left; split; assumption.
        +   right; split; assumption.
    -   intros [[PA PB]|[PA PC]].
        all: split; try assumption.
        +   left; exact PB.
        +   right; exact PC.
Qed.
Theorem and_or_rdist : ∀ A B C, ((A ∨ B) ∧ C) = ((A ∧ C) ∨ (B ∧ C)).
    intros A B C.
    do 3 rewrite (and_comm _ C).
    apply and_or_ldist.
Qed.

Theorem or_and_ldist : ∀ A B C, (A ∨ (B ∧ C)) = ((A ∨ B) ∧ (A ∨ C)).
    intros A B C.
    apply propositional_ext; split.
    -   intros [PA|[PB PC]].
        +   split; left; exact PA.
        +   split; right; assumption.
    -   intros [[PA|PB] [PA2|PC]].
        all: try (left; assumption).
        right; split; assumption.
Qed.
Theorem or_and_rdist : ∀ A B C, ((A ∧ B) ∨ C) = ((A ∨ C) ∧ (B ∨ C)).
    intros A B C.
    do 3 rewrite (or_comm _ C).
    apply or_and_ldist.
Qed.

Theorem or_to_strong : ∀ P Q, P ∨ Q → {P} + {Q}.
    intros P Q PQ.
    apply indefinite_description.
    destruct PQ as [PQ|PQ].
    -   split; left.
        exact PQ.
    -   split; right.
        exact PQ.
Qed.

Theorem not_true : (¬True) = False.
    apply propositional_ext; split.
    -   intro H; apply H; exact true.
    -   contradiction.
Qed.

Theorem not_false : (¬False) = True.
    apply propositional_ext; split.
    -   intro H; exact true.
    -   intros H H2; contradiction.
Qed.

Theorem not_not_type : ∀ P : Type, ((P → False) → False) → P.
    intros P Ps.
    assert (∃ p : P, True).
    {
        rewrite <- (not_not (∃ _ : P, True)).
        intros contr.
        rewrite not_ex in contr.
        rewrite not_true in contr.
        exact (Ps contr).
    }
    destruct (ex_to_type H).
    exact x.
Qed.
Ltac classic_contradiction H :=
    classic_contradiction_prop H ||
    (apply not_not_type; intros H).

Theorem prop_eq_true : ∀ P : Prop, P = (P = True).
    intros P.
    apply propositional_ext; split.
    -   intro p.
        apply propositional_ext; split; trivial.
    -   intros P_eq.
        rewrite P_eq.
        exact true.
Qed.
Theorem prop_eq_false : ∀ P, (¬P) = (P = False).
    intros P.
    apply propositional_ext; split.
    -   intros nP.
        apply propositional_ext; split; contradiction.
    -   intro eq.
        rewrite eq.
        rewrite not_false.
        exact true.
Qed.

Theorem neq_true_false : ∀ P, (P ≠ True) = (P = False).
    intros P.
    rewrite <- prop_eq_true.
    rewrite prop_eq_false.
    reflexivity.
Qed.
Theorem neq_false_true : ∀ P, (P ≠ False) = (P = True).
    intros P.
    rewrite <- prop_eq_false.
    rewrite not_not.
    apply prop_eq_true.
Qed.

Theorem prop_split : ∀ P, {P = True} + {P = False}.
    intros P.
    classic_case (P = True) as [eq|neq]; try (left; exact eq).
    right.
    rewrite neq_true_false in neq.
    exact neq.
Qed.

Theorem prop_neq : True ≠ False.
    intros eq.
    rewrite <- eq.
    exact true.
Qed.

Theorem any_prop_neq : ∀ P, P ≠ (¬P).
    intros P eq.
    destruct (prop_split P); subst.
    -   rewrite not_true in eq.
        rewrite <- eq.
        exact true.
    -   rewrite eq.
        intro contr.
        contradiction.
Qed.

Theorem not_eq_eq : ∀ A B, (¬A) = (¬B) → A = B.
    intros A B eq.
    apply (f_equal not) in eq.
    do 2 rewrite not_not in eq.
    exact eq.
Qed.
