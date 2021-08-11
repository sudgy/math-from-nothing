Require Import init.

Require Import nat.

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

Fixpoint list_reverse (A : Type) (l : list A) : list A :=
    match l with
    | list_end => list_end
    | a :: l1 => list_reverse l1 ++ (a :: list_end)
    end.

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

Fixpoint list_image (A B : Type) (l : list A) (f : A → B) :=
    match l with
    | list_end => list_end
    | a :: l' => f a :: list_image l' f
    end.

Theorem list_image_conc {A B : Type} : ∀ (l1 l2 : list A) (f : A → B),
        list_image (l1 ++ l2) f = list_image l1 f ++ list_image l2 f.
    intros l1 l2 f.
    induction l1.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite IHl1.
        reflexivity.
Qed.

Fixpoint in_list (A : Type) (l : list A) (x : A) :=
    match l with
    | list_end => False
    | a :: l' => a = x ∨ in_list l' x
    end.

Theorem in_list_conc (A : Type) : ∀ (l1 l2 : list A) (x : A),
        in_list (l1 ++ l2) x → in_list l1 x ∨ in_list l2 x.
    intros l1 l2 x in12.
    induction l1.
    -   right.
        cbn in in12.
        exact in12.
    -   cbn in in12.
        destruct in12 as [ax|in12].
        +   left.
            left.
            exact ax.
        +   specialize (IHl1 in12) as [in1|in2].
            *   left; right.
                exact in1.
            *   right.
                exact in2.
Qed.

Fixpoint list_prod2_base {A B : Type} (op : A → A → B) (l : list A) (b : A) :=
    match l with
    | list_end => list_end
    | a :: l' => op a b :: list_prod2_base op l' b
    end.

Fixpoint list_prod2 {A B : Type} (op : A → A → B) (l1 l2 : list A) :=
    match l2 with
    | list_end => list_end
    | b :: l2' => list_prod2_base op l1 b ++ list_prod2 op l1 l2'
    end.

Theorem list_prod2_lend {A B : Type} (op : A → A → B) (l : list A) :
        list_prod2 op list_end l = list_end.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        exact IHl.
Qed.

Theorem list_prod2_rend {A B : Type} (op : A → A → B) (l : list A) :
        list_prod2 op l list_end = list_end.
    cbn.
    reflexivity.
Qed.

Fixpoint list_zip {A B : Type} (l1 : list A) (l2 : list B) :=
    match l1, l2 with
    | a :: l1', b :: l2' => (a, b) :: list_zip l1' l2'
    | _, _ => list_end
    end.

Fixpoint list_size {A : Type} (l : list A) :=
    match l with
    | a :: l' => nat_suc (list_size l')
    | list_end => 0
    end.

Fixpoint list_unique {A : Type} (l : list A) :=
    match l with
    | a :: l' => ¬in_list l' a ∧ list_unique l'
    | _ => True
    end.

Fixpoint func_to_list {A : Type} (f : nat → A) n :=
    match n with
    | nat_zero => list_end
    | nat_suc n' => f n' :: func_to_list f n'
    end.

Theorem func_to_list_eq {A : Type} (f g : nat → A) n :
        (∀ m, m < n → f m = g m) → func_to_list f n = func_to_list g n.
    intros all_eq.
    revert f g all_eq.
    nat_induction n.
    -   intros.
        unfold zero; cbn.
        reflexivity.
    -   intros.
        assert (∀ m, m < n → f m = g m) as all_eq2.
        {
            intros m m_lt.
            apply all_eq.
            exact (trans m_lt (nat_lt_suc n)).
        }
        specialize (IHn f g all_eq2).
        cbn.
        rewrite IHn.
        apply f_equal2.
        2: reflexivity.
        apply all_eq.
        apply nat_lt_suc.
Qed.
