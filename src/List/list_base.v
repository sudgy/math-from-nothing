Require Import init.

Set Implicit Arguments.

#[universes(template)]
Inductive list (A : Type) : Type :=
 | list_end : list A
 | list_add : A → list A → list A.

Arguments list_end {A}.
Arguments list_add {A} a l.

Infix "::" := list_add (at level 60, right associativity) : list_scope.
Open Scope list_scope.

Fixpoint list_conc {U : Type} (al bl : list U) : list U :=
  match al with
   | list_end => bl
   | a :: al' => a :: list_conc al' bl
  end.

Infix "++" := list_conc (right associativity, at level 60) : list_scope.

Fixpoint list_reverse {U : Type} (l : list U) : list U :=
    match l with
    | list_end => list_end
    | a :: l1 => list_reverse l1 ++ (a :: list_end)
    end.

Theorem list_end_neq {U} : ∀ (a : U) l, a :: l ≠ list_end.
Proof.
    intros a l eq.
    inversion eq.
Qed.

Theorem list_inversion {U} : ∀ (a b : U) al bl, a :: al = b :: bl →
    a = b ∧ al = bl.
Proof.
    intros a b al bl eq.
    inversion eq.
    split; reflexivity.
Qed.

Theorem list_single_eq {U} : ∀ (a b : U), a :: list_end = b :: list_end → a = b.
Proof.
    intros a b eq.
    apply list_inversion in eq.
    apply eq.
Qed.

Theorem list_conc_eq {U} : ∀ (x : U) al bl, x :: al = x :: bl → al = bl.
Proof.
    intros x al bl eq.
    apply list_inversion in eq.
    apply eq.
Qed.

Theorem list_add_conc_add {U} : ∀ (a : U) l1 l2,
    a :: (l1 ++ l2) = (a :: l1) ++ l2.
Proof.
    intros a l1 l2.
    cbn.
    reflexivity.
Qed.

Theorem list_add_conc {U} : ∀ (a : U) l, a :: l = (a :: list_end) ++ l.
Proof.
    intros a l.
    cbn.
    reflexivity.
Qed.

Theorem list_conc_end {U} : ∀ l : list U, l ++ list_end = l.
Proof.
    intros l.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite IHl.
        reflexivity.
Qed.

Theorem list_conc_assoc {U} :
    ∀ l1 l2 l3 : list U, l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
    intros l1 l2 l3.
    induction l1.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite IHl1.
        reflexivity.
Qed.

Theorem list_conc_add_assoc {U} :
    ∀ (a : U) l1 l2, a :: (l1 ++ l2) = (a :: l1) ++ l2.
Proof.
    intros a l1 l2.
    cbn.
    reflexivity.
Qed.

Theorem list_reverse_conc {U : Type} : ∀ l1 l2 : list U,
    list_reverse (l1 ++ l2) = list_reverse l2 ++ list_reverse l1.
Proof.
    intros l1 l2.
    induction l1.
    -   cbn.
        rewrite list_conc_end.
        reflexivity.
    -   cbn.
        rewrite IHl1.
        rewrite list_conc_assoc.
        reflexivity.
Qed.

Theorem list_reverse_end {U : Type} : ∀ l : list U,
    list_end = list_reverse l → list_end = l.
Proof.
    intros l eq.
    destruct l; [>reflexivity|].
    cbn in eq.
    destruct (list_reverse l).
    -   cbn in eq.
        symmetry in eq.
        apply list_end_neq in eq.
        contradiction.
    -   cbn in eq.
        symmetry in eq.
        apply list_end_neq in eq.
        contradiction.
Qed.

Theorem list_reverse_reverse {U : Type} : ∀ l : list U,
    list_reverse (list_reverse l) = l.
Proof.
    intros l.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite list_reverse_conc.
        rewrite IHl.
        cbn.
        reflexivity.
Qed.

Theorem list_reverse_eq {U : Type} : ∀ l1 l2 : list U,
    l1 = l2 ↔ list_reverse l1 = list_reverse l2.
Proof.
    intros l1 l2.
    split; [>intros; subst; reflexivity|].
    intros l_eq.
    rewrite <- (list_reverse_reverse l1).
    rewrite <- (list_reverse_reverse l2).
    rewrite l_eq.
    reflexivity.
Qed.
