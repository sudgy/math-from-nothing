Require Import init.

Require Export plus_group.

#[universes(template)]
Inductive list (A : Type) : Type :=
 | list_end : list A
 | list_add : A → list A → list A.

Arguments list_end {A}.
Arguments list_add {A} a l.

(** At the risk of being confusing, this is NOT a colon!  It is actually U+A789,
modifier letter colon.  I have it mapped to \ladd in ibus. *)
Infix "꞉" := list_add (at level 49, right associativity) : list_scope.
Open Scope list_scope.
Notation "[]" := list_end : list_scope.
Notation "[ a ]" := (a ꞉ []) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=
    (x ꞉ (y ꞉ .. (z ꞉ []) ..))
    (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : list_scope.

Fixpoint list_conc {U : Type} (al bl : list U) : list U :=
  match al with
   | [] => bl
   | a ꞉ al' => a ꞉ list_conc al' bl
  end.

Global Instance list_plus U : Plus (list U) := {
    plus := list_conc
}.
Arguments list_conc : simpl never.

Fixpoint list_reverse {U : Type} (l : list U) : list U :=
    match l with
    | [] => []
    | a ꞉ l1 => list_reverse l1 + [a]
    end.
Arguments list_reverse : simpl never.

Fixpoint list_image {A B : Type} (f : A → B) (l : list A) :=
    match l with
    | [] => []
    | a ꞉ l' => f a ꞉ list_image f l'
    end.
Arguments list_image : simpl never.

Theorem list_end_neq {U} : ∀ (a : U) l, a ꞉ l ≠ [].
Proof.
    intros a l eq.
    inversion eq.
Qed.

Theorem list_inversion {U} : ∀ (a b : U) al bl, a ꞉ al = b ꞉ bl →
    a = b ∧ al = bl.
Proof.
    intros a b al bl eq.
    inversion eq.
    split; reflexivity.
Qed.

Theorem list_single_eq {U} : ∀ (a b : U), [a] = [b] → a = b.
Proof.
    intros a b eq.
    apply list_inversion in eq.
    apply eq.
Qed.

Theorem list_add_eq {U} : ∀ (x : U) al bl, x ꞉ al = x ꞉ bl → al = bl.
Proof.
    intros x al bl eq.
    apply list_inversion in eq.
    apply eq.
Qed.

Theorem list_conc_add {U} : ∀ a (l1 l2 : list U), (a ꞉ l1) + l2 = a ꞉ (l1 + l2).
Proof.
    reflexivity.
Qed.

Theorem list_conc_single {U} : ∀ (a : U) l, [a] + l = a ꞉ l.
Proof.
    reflexivity.
Qed.

Global Instance list_zero U : Zero (list U) := {
    zero := []
}.

Global Instance list_plus_lid U : PlusLid (list U).
Proof.
    split.
    reflexivity.
Qed.
Theorem list_conc_lid {U} : ∀ l : list U, [] + l = l.
Proof.
    exact plus_lid.
Qed.

Global Instance list_plus_rid U : PlusRid (list U).
Proof.
    split.
    intros l.
    induction l.
    -   reflexivity.
    -   rewrite list_conc_add.
        rewrite IHl.
        reflexivity.
Qed.
Theorem list_conc_rid {U} : ∀ l : list U, l + [] = l.
Proof.
    exact plus_rid.
Qed.

Global Instance list_plus_assoc U : PlusAssoc (list U).
Proof.
    split.
    intros l1 l2 l3.
    induction l1.
    -   do 2 rewrite list_conc_lid.
        reflexivity.
    -   do 3 rewrite list_conc_add.
        rewrite IHl1.
        reflexivity.
Qed.

Theorem list_reverse_end {U} : list_reverse (U := U) [] = [].
Proof.
    reflexivity.
Qed.

Theorem list_reverse_add {U} : ∀ (a : U) l,
    list_reverse (a ꞉ l) = list_reverse l + [a].
Proof.
    reflexivity.
Qed.

Global Arguments list_reverse : simpl never.

Theorem list_reverse_single {U} : ∀ (a : U), list_reverse [a] = [a].
Proof.
    reflexivity.
Qed.

Theorem list_reverse_conc {U : Type} : ∀ l1 l2 : list U,
    list_reverse (l1 + l2) = list_reverse l2 + list_reverse l1.
Proof.
    intros l1 l2.
    induction l1.
    -   rewrite list_reverse_end.
        rewrite list_conc_lid, list_conc_rid.
        reflexivity.
    -   rewrite list_conc_add, list_reverse_add.
        rewrite IHl1.
        rewrite list_reverse_add.
        rewrite plus_assoc.
        reflexivity.
Qed.

Theorem list_reverse_reverse {U : Type} : ∀ l : list U,
    list_reverse (list_reverse l) = l.
Proof.
    intros l.
    induction l.
    -   rewrite list_reverse_end.
        reflexivity.
    -   rewrite list_reverse_add.
        rewrite list_reverse_conc.
        rewrite IHl.
        rewrite list_reverse_single.
        apply list_conc_single.
Qed.

Theorem list_reverse_eq {U : Type} : ∀ l1 l2 : list U,
    list_reverse l1 = list_reverse l2 → l1 = l2.
Proof.
    intros l1 l2 l_eq.
    rewrite <- (list_reverse_reverse l1).
    rewrite <- (list_reverse_reverse l2).
    rewrite l_eq.
    reflexivity.
Qed.

Theorem list_reverse_end_eq {U : Type} : ∀ l : list U,
    [] = list_reverse l → [] = l.
Proof.
    intros l eq.
    rewrite <- list_reverse_end in eq.
    apply list_reverse_eq in eq.
    exact eq.
Qed.

Theorem list_image_end {A B : Type} : ∀ (f : A → B), list_image f [] = [].
Proof.
    reflexivity.
Qed.

Theorem list_image_add {A B : Type} : ∀ a l (f : A → B),
    list_image f (a ꞉ l) = f a ꞉ list_image f l.
Proof.
    reflexivity.
Qed.

Theorem list_image_single {A B : Type} : ∀ a (f : A → B),
    list_image f [a] = [f a].
Proof.
    reflexivity.
Qed.

Theorem list_image_conc {A B : Type} : ∀ (l1 l2 : list A) (f : A → B),
    list_image f (l1 + l2) = list_image f l1 + list_image f l2.
Proof.
    intros l1 l2 f.
    induction l1.
    -   rewrite list_image_end.
        do 2 rewrite list_conc_lid.
        reflexivity.
    -   rewrite list_conc_add.
        do 2 rewrite list_image_add.
        rewrite IHl1.
        rewrite list_conc_add.
        reflexivity.
Qed.

Theorem list_image_comp {A B C : Type} : ∀ (l : list A) (f : A → B) (g : B → C),
    list_image g (list_image f l) = list_image (λ x, g (f x)) l.
Proof.
    intros l f g.
    induction l.
    -   do 2 rewrite list_image_end.
        reflexivity.
    -   do 3 rewrite list_image_add.
        rewrite IHl.
        reflexivity.
Qed.
