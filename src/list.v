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

Theorem list_image_comp {A B C : Type} : ∀ (l : list A) (f : A → B) (g : B → C),
        list_image (list_image l f) g = list_image l (λ x, g (f x)).
    intros l f g.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite IHl.
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

Theorem list_prod2_base_image {A B} (op : A → A → B) : ∀ l b,
        list_prod2_base op l b = list_image l (λ x, op x b).
    intros l b.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite IHl.
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

Fixpoint func_to_list_base {A : Type} (f : nat → A) n :=
    match n with
    | nat_zero => list_end
    | nat_suc n' => f n' :: func_to_list_base f n'
    end.

Definition func_to_list {A : Type} (f : nat → A) n :=
    list_reverse (func_to_list_base f n).

Theorem func_to_list_eq {A : Type} (f g : nat → A) n :
        (∀ m, m < n → f m = g m) → func_to_list f n = func_to_list g n.
    intros all_eq.
    unfold func_to_list.
    rewrite <- list_reverse_eq.
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

Fixpoint func_to_list2_base {A : Type} (f : nat → A) m n :=
    match n with
    | nat_zero => list_end
    | nat_suc n' => f m :: func_to_list2_base f (nat_suc m) n'
    end.

Definition func_to_list2 {A : Type} (f : nat → A) n := func_to_list2_base f 0 n.

Lemma func_to_list2_base_eq {A} : ∀ (f : nat → A) m n,
        func_to_list2_base f (nat_suc m) n =
        func_to_list2_base (λ x, f (nat_suc x)) m n.
    intros f m n.
    revert m.
    nat_induction n.
    +   unfold zero; cbn.
        reflexivity.
    +   cbn.
        intros.
        rewrite IHn.
        reflexivity.
Qed.

Theorem func_to_list2_eq {A : Type} : ∀ (f : nat → A) n,
        func_to_list f n = func_to_list2 f n.
    intros f n.
    unfold func_to_list, func_to_list2.
    nat_induction n.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        unfold func_to_list, func_to_list2 in IHn.
        rewrite IHn.
        clear IHn.
        revert f.
        nat_induction n.
        +   unfold zero, one; cbn.
            reflexivity.
        +   intros.
            cbn.
            specialize (IHn (λ x, f (nat_suc x))).
            cbn in IHn.
            apply f_equal.
            rewrite <- func_to_list2_base_eq in IHn.
            rewrite <- func_to_list2_base_eq in IHn.
            exact IHn.
Qed.

Fixpoint list_nth {A} (l : list A) (n : nat) (default : A) :=
    match n, l with
    | nat_zero, x :: _ => x
    | nat_suc n', x :: l' => list_nth l' n' default
    | _, _ => default
    end.

Theorem func_to_list_nth_lt {A} : ∀ f m n (a : A), m < n →
        list_nth (func_to_list f n) m a = f m.
    intros f m n a ltq.
    rewrite func_to_list2_eq.
    apply nat_lt_ex in ltq as [c [c_nz c_eq]].
    subst n.
    nat_destruct c.
    1: contradiction.
    clear c_nz.
    rewrite nat_plus_rsuc.
    cbn.
    revert f c a.
    nat_induction m.
    -   reflexivity.
    -   intros.
        rewrite nat_plus_lsuc.
        cbn.
        specialize (IHm (λ x, f (nat_suc x)) c a).
        cbn in IHm.
        rewrite <- IHm.
        nat_destruct m.
        1: reflexivity.
        apply f_equal3; try reflexivity.
        apply func_to_list2_base_eq.
Qed.

Theorem func_to_list_nth_ge {A} : ∀ f m n (a : A), n <= m →
        list_nth (func_to_list f n) m a = a.
    intros f m n a leq.
    rewrite func_to_list2_eq.
    apply nat_le_ex in leq as [c c_eq].
    subst m.
    revert f c.
    nat_induction n.
    -   intros.
        rewrite plus_lid.
        unfold zero; cbn.
        destruct c; reflexivity.
    -   intros.
        rewrite nat_plus_lsuc.
        cbn.
        specialize (IHn (λ x, f (nat_suc x)) c).
        unfold func_to_list2 in IHn.
        rewrite <- func_to_list2_base_eq in IHn.
        exact IHn.
Qed.

Theorem func_to_list_image {A B} : ∀ (f : nat → A) (g : A → B) n,
        list_image (func_to_list f n) g = func_to_list (λ m, g (f m)) n.
    intros f g n.
    do 2 rewrite func_to_list2_eq.
    revert f.
    nat_induction n.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        intros f.
        specialize (IHn (λ m, f (nat_suc m))).
        unfold func_to_list2 in IHn.
        rewrite <- func_to_list2_base_eq in IHn.
        rewrite IHn.
        rewrite func_to_list2_base_eq.
        reflexivity.
Qed.

Theorem func_to_list2_base_conc {A} : ∀ (f : nat → A) a b c,
        func_to_list2_base f a (b + c) =
        func_to_list2_base f a c ++ func_to_list2_base f (a + c) b.
    intros f a b c.
    revert a b f.
    nat_induction c.
    -   intros.
        do 2 rewrite plus_rid.
        unfold zero; cbn.
        reflexivity.
    -   intros.
        rewrite nat_plus_rsuc.
        cbn.
        specialize (IHc (nat_suc a) b f).
        rewrite IHc.
        rewrite nat_plus_lrsuc.
        reflexivity.
Qed.

Inductive list_permutation {U} : list U → list U → Prop :=
| list_perm_nil: list_permutation list_end list_end
| list_perm_skip x l l' : list_permutation l l' → list_permutation (x::l) (x::l')
| list_perm_swap x y l : list_permutation (y::x::l) (x::y::l)
| list_perm_trans l l' l'' :
    list_permutation l l' → list_permutation l' l'' → list_permutation l l''.

Theorem list_perm_refl {U} : ∀ l : list U, list_permutation l l.
    intros l.
    induction l.
    -   exact list_perm_nil.
    -   apply list_perm_skip.
        exact IHl.
Qed.

Theorem list_perm_sym {U} : ∀ al bl : list U,
        list_permutation al bl → list_permutation bl al.
    intros al bl perm.
    induction perm.
    -   exact list_perm_nil.
    -   apply list_perm_skip.
        exact IHperm.
    -   apply list_perm_swap.
    -   exact (list_perm_trans IHperm2 IHperm1).
Qed.

Theorem list_perm_nil_eq {U} : ∀ l : list U,
        list_permutation list_end l → list_end = l.
    intros l l_end.
    remember (list_end) as m in l_end.
    induction l_end.
    -   reflexivity.
    -   inversion Heqm.
    -   inversion Heqm.
    -   apply IHl_end1 in Heqm.
        symmetry in Heqm.
        apply IHl_end2 in Heqm.
        exact Heqm.
Qed.
