(** This file contains several basic logical theorems such as De Morgan's laws.
*)

Require Export base_logic.

Ltac exfalso := elimtype False.

Theorem not_not : ∀ P, (¬¬P) ↔ P.
Proof.
    intro P.
    split; intro PH.
    -   classic_case P as [PH'|PH'].
        +   exact PH'.
        +   contradiction (PH PH').
    -   intro PH'.
        contradiction (PH' PH).
Qed.
Ltac classic_contradiction_prop H := apply (land (not_not _)); intros H.

Theorem not_impl : ∀ A B : Prop, (¬(A → B)) ↔ (A ∧ ¬B).
Proof.
    intros A B.
    split.
    -   intros n.
        classic_case B as [BH|nBH].
        +   assert (A → B) by (intro; exact BH).
            contradiction.
        +   split; [>|exact nBH].
            classic_case A as [AH|nAH]; [>exact AH|].
            exfalso.
            apply n.
            intro; contradiction.
    -   intros [a b] ab.
        specialize (ab a).
        contradiction.
Qed.
Theorem not_and : ∀ A B, (¬(A ∧ B)) ↔ (¬A ∨ ¬B).
Proof.
    intros A B.
    split.
    -   intros n.
        classic_case A as [AH|nAH].
        +   right.
            intros b.
            apply n.
            split; assumption.
        +   left; exact nAH.
    -   intros [na|nb] [a b]; contradiction.
Qed.
Theorem not_or : ∀ A B, (¬(A ∨ B)) ↔ (¬A ∧ ¬B).
Proof.
    intros A B.
    rewrite <- (not_not (¬A ∧ ¬B)).
    rewrite not_and.
    do 2 rewrite not_not.
    reflexivity.
Qed.
Theorem not_ex : ∀ {U} (P : U → Prop), (¬(∃ a, P a)) ↔ (∀ a, ¬P a).
Proof.
    intros U P.
    split.
    -   intros not_ex a Pa.
        apply not_ex.
        exists a.
        exact Pa.
    -   intros all [a Pa].
        specialize (all a).
        contradiction.
Qed.

Theorem not_all : ∀ {U} (P : U → Prop), (¬(∀ a, P a)) ↔ (∃ a, ¬P a).
Proof.
    intros U P.
    rewrite <- (not_not (∃ a, ¬P a)).
    rewrite not_ex.
    split.
    all: intros not_all all.
    all: apply not_all.
    all: intros a.
    -   rewrite <- not_not.
        apply all.
    -   rewrite not_not.
        apply all.
Qed.

Theorem not_and_impl : ∀ A B, (¬(A ∧ B)) ↔ (A → ¬B).
Proof.
    intros A B.
    rewrite <- (not_not (A → ¬B)).
    rewrite not_impl.
    rewrite not_not.
    reflexivity.
Qed.

Theorem and_assoc : ∀ A B C, A ∧ (B ∧ C) ↔ (A ∧ B) ∧ C.
Proof.
    intros A B C.
    split.
    -   intros [P1 [P2 P3]].
        split; [>split|]; assumption.
    -   intros [[P1 P2] P3].
        split; [>|split]; assumption.
Qed.

Theorem or_assoc : ∀ A B C, A ∨ (B ∨ C) ↔ (A ∨ B) ∨ C.
Proof.
    intros A B C.
    split.
    -   intros [P1|[P2|P3]].
        +   left; left; exact P1.
        +   left; right; exact P2.
        +   right; exact P3.
    -   intros [[P1|P2]|P3].
        +   left; exact P1.
        +   right; left; exact P2.
        +   right; right; exact P3.
Qed.

Theorem and_comm : ∀ A B, (A ∧ B) ↔ (B ∧ A).
Proof.
    intros A B.
    split.
    all: intros [P1 P2].
    all: split; assumption.
Qed.

Theorem or_comm : ∀ A B, (A ∨ B) ↔ (B ∨ A).
Proof.
    intros A B.
    split.
    all: intros [P1|P2].
    -   right; exact P1.
    -   left; exact P2.
    -   right; exact P1.
    -   left; exact P2.
Qed.

Theorem and_or_ldist : ∀ A B C, (A ∧ (B ∨ C)) ↔ ((A ∧ B) ∨ (A ∧ C)).
Proof.
    intros A B C.
    split.
    -   intros [PA [PB|PC]].
        +   left; split; assumption.
        +   right; split; assumption.
    -   intros [[PA PB]|[PA PC]].
        all: split; try assumption.
        +   left; exact PB.
        +   right; exact PC.
Qed.
Theorem and_or_rdist : ∀ A B C, ((A ∨ B) ∧ C) ↔ ((A ∧ C) ∨ (B ∧ C)).
Proof.
    intros A B C.
    do 3 rewrite (and_comm _ C).
    apply and_or_ldist.
Qed.

Theorem or_and_ldist : ∀ A B C, (A ∨ (B ∧ C)) ↔ ((A ∨ B) ∧ (A ∨ C)).
Proof.
    intros A B C.
    split.
    -   intros [PA|[PB PC]].
        +   split; left; exact PA.
        +   split; right; assumption.
    -   intros [[PA|PB] [PA2|PC]].
        all: try (left; assumption).
        right; split; assumption.
Qed.
Theorem or_and_rdist : ∀ A B C, ((A ∧ B) ∨ C) ↔ ((A ∨ C) ∧ (B ∨ C)).
Proof.
    intros A B C.
    do 3 rewrite (or_comm _ C).
    apply or_and_ldist.
Qed.

Theorem or_to_strong : ∀ P Q, P ∨ Q → {P} + {Q}.
Proof.
    intros P Q PQ.
    apply indefinite_description.
    destruct PQ as [PQ|PQ].
    -   split; left.
        exact PQ.
    -   split; right.
        exact PQ.
Qed.
Theorem or_from_strong : ∀ P Q, {P} + {Q} → P ∨ Q.
Proof.
    intros P Q [PQ|PQ].
    -   left; exact PQ.
    -   right; exact PQ.
Qed.

Theorem or_lfalse : ∀ P, False ∨ P ↔ P.
Proof.
    intros P.
    split.
    -   intros [H|H].
        +   contradiction H.
        +   exact H.
    -   intros H.
        right.
        exact H.
Qed.

Theorem or_rfalse : ∀ P, P ∨ False ↔ P.
Proof.
    intros P.
    rewrite or_comm.
    apply or_lfalse.
Qed.

Theorem or_ltrue : ∀ P, True ∨ P ↔ True.
Proof.
    intros P.
    split.
    -   intro; exact true.
    -   intros; left; exact true.
Qed.

Theorem or_rtrue : ∀ P, P ∨ True ↔ True.
Proof.
    intros P.
    rewrite or_comm.
    apply or_ltrue.
Qed.

Theorem and_lfalse : ∀ P, False ∧ P ↔ False.
Proof.
    intros P.
    split.
    -   intros [H PH].
        exact H.
    -   intros H.
        contradiction H.
Qed.

Theorem and_rfalse : ∀ P, P ∧ False ↔ False.
Proof.
    intros P.
    rewrite and_comm.
    apply and_lfalse.
Qed.

Theorem and_ltrue : ∀ P, True ∧ P ↔ P.
Proof.
    intros P.
    split.
    -   intros [H PH].
        exact PH.
    -   intros H.
        split.
        +   exact true.
        +   exact H.
Qed.

Theorem and_rtrue : ∀ P, P ∧ True ↔ P.
Proof.
    intros P.
    rewrite and_comm.
    apply and_ltrue.
Qed.

Theorem or_idemp : ∀ P, P ∨ P ↔ P.
Proof.
    intros P.
    split.
    -   intros [H|H]; exact H.
    -   intros H.
        left; exact H.
Qed.

Theorem and_idemp : ∀ P, P ∧ P ↔ P.
Proof.
    intros P.
    split.
    -   intros [H H'].
        exact H.
    -   intros H.
        split; exact H.
Qed.

Theorem or_both : ∀ P, (P ∨ ¬P) ↔ True.
Proof.
    intros P.
    split; [>intro; exact true|].
    intros I.
    apply excluded_middle.
Qed.

Theorem and_both : ∀ P, (P ∧ ¬P) ↔ False.
Proof.
    intros P.
    split; [>|intro; contradiction].
    intros [H nH].
    contradiction.
Qed.

Theorem not_true : (¬True) = False.
Proof.
    apply propositional_ext; split.
    -   intro H; apply H; exact true.
    -   contradiction.
Qed.

Theorem not_false : (¬False) = True.
Proof.
    apply propositional_ext; split.
    -   intro H; exact true.
    -   intros H H2; contradiction.
Qed.

Theorem not_not_type : ∀ P : Type, ((P → False) → False) → P.
Proof.
    intros P Ps.
    assert (∃ p : P, True).
    {
        rewrite <- (not_not (∃ _ : P, True)).
        intros contr.
        rewrite not_ex in contr.
        rewrite not_true in contr.
        exact (Ps contr).
    }
    destruct (ex_to_type H) as [p pH].
    exact p.
Qed.
Ltac classic_contradiction H :=
    classic_contradiction_prop H ||
    (apply not_not_type; intros H).

Theorem prop_eq_true : ∀ P : Prop, P = (P = True).
Proof.
    intros P.
    apply propositional_ext; split.
    -   intro p.
        apply propositional_ext; split; trivial.
    -   intros P_eq.
        rewrite P_eq.
        exact true.
Qed.
Theorem prop_eq_false : ∀ P, (¬P) = (P = False).
Proof.
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
Proof.
    intros P.
    rewrite <- prop_eq_true.
    rewrite prop_eq_false.
    reflexivity.
Qed.
Theorem neq_false_true : ∀ P, (P ≠ False) = (P = True).
Proof.
    intros P.
    rewrite <- prop_eq_false.
    rewrite not_not.
    apply prop_eq_true.
Qed.

Theorem prop_split : ∀ P, {P = True} + {P = False}.
Proof.
    intros P.
    rewrite <- prop_eq_true.
    rewrite <- prop_eq_false.
    apply strong_excluded_middle.
Qed.

Theorem prop_neq : True ≠ False.
Proof.
    intros eq.
    rewrite <- eq.
    exact true.
Qed.

Theorem any_prop_neq : ∀ P, P ≠ (¬P).
Proof.
    intros P eq.
    destruct (prop_split P); subst.
    -   rewrite not_true in eq.
        rewrite <- eq.
        exact true.
    -   rewrite eq.
        rewrite not_false.
        exact true.
Qed.

Theorem not_eq_eq : ∀ A B, (¬A) = (¬B) → A = B.
Proof.
    intros A B eq.
    apply (f_equal not) in eq.
    do 2 rewrite not_not in eq.
    exact eq.
Qed.

Theorem not_eq_iff : ∀ A B, (A ↔ B) ↔ (¬A ↔ ¬B).
Proof.
    intros A B.
    split.
    -   intros AB.
        apply propositional_ext in AB.
        rewrite AB.
        reflexivity.
    -   intros AB.
        apply propositional_ext in AB.
        apply not_eq_eq in AB.
        rewrite AB.
        reflexivity.
Qed.

Theorem eq_iff {U} : ∀ a b : U, a = b ↔ b = a.
    intros a b.
    split; intro eq; symmetry; exact eq.
Qed.

Theorem or_left : ∀ A B : Prop, (¬B → A) → A ∨ B.
    intros A B H.
    classic_case B as [BH|BH].
    -   right; exact BH.
    -   left; exact (H BH).
Qed.

Theorem or_right : ∀ A B : Prop, (¬A → B) → A ∨ B.
    intros A B H.
    classic_case A as [AH|AH].
    -   left; exact AH.
    -   right; exact (H AH).
Qed.
