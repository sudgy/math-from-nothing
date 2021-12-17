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

Definition list_conc (A : Type) : list A → list A → list A :=
  fix list_app l m :=
  match l with
   | list_end => m
   | a :: l1 => a :: list_app l1 m
  end.

Infix "++" := list_conc (right associativity, at level 60) : list_scope.

Fixpoint list_reverse (A : Type) (l : list A) : list A :=
    match l with
    | list_end => list_end
    | a :: l1 => list_reverse l1 ++ (a :: list_end)
    end.

Theorem list_add_conc {U} : ∀ (a : U) l, a :: l = (a :: list_end) ++ l.
    intros a l.
    cbn.
    reflexivity.
Qed.

Theorem list_conc_end {U} : ∀ l : list U, l ++ list_end = l.
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
    intros a l1 l2.
    rewrite list_add_conc.
    rewrite (list_add_conc a l1).
    apply list_conc_assoc.
Qed.

Theorem list_reverse_conc {U : Type} : ∀ l1 l2 : list U,
        list_reverse (l1 ++ l2) = list_reverse l2 ++ list_reverse l1.
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
    intros l eq.
    destruct l.
    1: reflexivity.
    cbn in eq.
    destruct (list_reverse l).
    -   inversion eq.
    -   inversion eq.
Qed.

Theorem list_reverse_reverse {U : Type} : ∀ l : list U,
        list_reverse (list_reverse l) = l.
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
    intros l1 l2.
    split.
    1: intros; subst; reflexivity.
    intros l_eq.
    rewrite <- (list_reverse_reverse l1).
    rewrite <- (list_reverse_reverse l2).
    rewrite l_eq.
    reflexivity.
Qed.
