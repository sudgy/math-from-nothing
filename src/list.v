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

Theorem in_list_rconc {U : Type} : ∀ (l1 l2 : list U) (x : U),
        in_list l2 x → in_list (l1 ++ l2) x.
    intros l1 l2 x x_in.
    induction l1.
    -   cbn.
        exact x_in.
    -   right.
        exact IHl1.
Qed.

Theorem in_list_lconc {U : Type} : ∀ (l1 l2 : list U) (x : U),
        in_list l1 x → in_list (l1 ++ l2) x.
    intros l1 l2 x x_in.
    induction l1.
    -   contradiction x_in.
    -   destruct x_in as [x_eq|x_in].
        +   left.
            exact x_eq.
        +   right.
            exact (IHl1 x_in).
Qed.

Theorem in_list_split {U : Type} :
        ∀ l (x : U), in_list l x → ∃ l1 l2, l = l1 ++ x :: l2.
    intros l x x_in.
    induction l.
    -   contradiction x_in.
    -   destruct x_in as [x_eq|x_in].
        +   subst a.
            exists list_end, l.
            cbn.
            reflexivity.
        +   specialize (IHl x_in).
            destruct IHl as [l1 [l2 l_eq]].
            rewrite l_eq; clear l_eq.
            exists (a :: l1), l2.
            cbn.
            reflexivity.
Qed.

Theorem in_list_image {U V} : ∀ l a (f : U → V),
        in_list l a → in_list (list_image l f) (f a).
    intros l a f a_in.
    induction l as [|b l].
    -   contradiction a_in.
    -   cbn.
        cbn in a_in.
        destruct a_in as [eq|a_in].
        +   left.
            rewrite eq.
            reflexivity.
        +   right.
            exact (IHl a_in).
Qed.

Theorem image_in_list {U V} : ∀ l y (f : U → V),
        in_list (list_image l f) y → ∃ x, f x = y ∧ in_list l x.
    intros l y f y_in.
    induction l.
    -   contradiction y_in.
    -   destruct y_in as [y_eq|y_in].
        +   exists a.
            split.
            *   exact y_eq.
            *   left.
                reflexivity.
        +   specialize (IHl y_in) as [x [x_eq x_in]].
            exists x.
            split.
            *   exact x_eq.
            *   right.
                exact x_in.
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

Theorem list_in_not_unique {U} : ∀ l1 l2 (x : U), in_list l1 x → in_list l2 x →
        ¬list_unique (l1 ++ l2).
    intros l1 l2 x l1_x l2_x l_uni.
    induction l1.
    -   contradiction l1_x.
    -   destruct l1_x as [ax|l1_x].
        +   subst x.
            destruct l_uni.
            apply (in_list_rconc l1) in l2_x.
            contradiction.
        +   apply IHl1.
            *   exact l1_x.
            *   apply l_uni.
Qed.

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

Theorem list_nth_eq {U} : ∀ l n (a b : U), n < list_size l →
        list_nth l n a = list_nth l n b.
    intros l n a b n_lt.
    revert n n_lt.
    induction l.
    -   intros n n_lt.
        cbn in n_lt.
        apply nat_lt_zero in n_lt.
        contradiction.
    -   intros n n_lt.
        cbn in *.
        nat_destruct n.
        +   reflexivity.
        +   rewrite nat_sucs_lt in n_lt.
            apply IHl.
            exact n_lt.
Qed.

Theorem in_list_nth {U} : ∀ l (x : U), in_list l x →
        ∃ n, n < list_size l ∧ x = list_nth l n x.
    intros l x x_in.
    induction l.
    -   contradiction x_in.
    -   destruct x_in as [x_eq|x_in].
        +   subst a.
            exists 0.
            split.
            *   cbn.
                apply nat_zero_lt_suc.
            *   unfold zero; cbn.
                reflexivity.
        +   specialize (IHl x_in) as [n [n_lt x_eq]].
            exists (nat_suc n).
            split.
            *   cbn.
                rewrite nat_sucs_lt.
                exact n_lt.
            *   cbn.
                exact x_eq.
Qed.

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

Theorem list_perm_trans2 {U} (l l' l'' : list U) :
        list_permutation l' l'' → list_permutation l l' →
        list_permutation l l''.
    intros eq1 eq2.
    apply (list_perm_trans eq2 eq1).
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

Theorem list_perm_lpart {U} : ∀ (al bl cl : list U),
        list_permutation al bl → list_permutation (al ++ cl) (bl ++ cl).
    intros al bl cl albl.
    induction albl.
    -   cbn.
        apply list_perm_refl.
    -   cbn.
        apply list_perm_skip.
        exact IHalbl.
    -   cbn.
        apply list_perm_swap.
    -   apply (list_perm_trans IHalbl1 IHalbl2).
Qed.

Theorem list_perm_add {U} : ∀ (l : list U) a,
        list_permutation (a :: l) (l ++ a :: list_end).
    intros l a.
    induction l.
    -   cbn.
        apply list_perm_refl.
    -   remember (a :: l) as l1.
        remember (l ++ a :: list_end) as l2.
        induction IHl.
        +   inversion Heql1.
        +   inversion Heql1.
            subst x l0.
            rewrite (list_add_conc a0 l) at 2.
            rewrite <- list_conc_assoc.
            rewrite <- Heql2.
            apply (list_perm_skip a0) in IHl.
            apply (list_perm_skip a) in IHl.
            apply (list_perm_trans IHl).
            apply list_perm_swap.
        +   inversion Heql1.
            subst y l.
            clear Heql1.
            rewrite (list_add_conc a0 _) at 2.
            rewrite <- list_conc_assoc.
            rewrite <- Heql2.
            cbn.
            pose (list_perm_swap a0 a (x :: l0)) as eq.
            apply (list_perm_trans eq).
            apply list_perm_skip.
            apply list_perm_swap.
        +   rewrite (list_add_conc a0 l) at 2.
            rewrite <- list_conc_assoc.
            rewrite <- Heql2.
            apply (list_perm_trans (list_perm_swap a0 a l)).
            apply list_perm_skip.
            rewrite <- Heql1.
            apply (list_perm_trans IHl1 IHl2).
Qed.

Theorem list_perm_conc {U} : ∀ al bl : list U,
        list_permutation (al ++ bl) (bl ++ al).
    intros al bl.
    induction al.
    -   cbn.
        rewrite list_conc_end.
        apply list_perm_refl.
    -   remember (al ++ bl) as l1.
        remember (bl ++ al) as l2.
        induction IHal.
        +   assert (al = list_end) as al_end.
            {
                destruct al; try reflexivity.
                inversion Heql1.
            }
            subst al.
            cbn in *.
            rewrite list_conc_end in Heql2.
            subst bl.
            cbn.
            apply list_perm_refl.
        +   clear IHIHal.
            destruct al.
            *   cbn in *.
                destruct bl.
                1: inversion Heql1.
                inversion Heql1 as [[eq Heql1']].
                subst u l.
                apply list_perm_add.
            *   remember (u :: al) as al'.
                pose proof (list_perm_add bl a) as eq.
                pose proof (list_perm_lpart al' eq) as eq2.
                rewrite <- list_conc_assoc in eq2.
                cbn in eq2.
                apply (list_perm_trans2 eq2).
                rewrite (list_add_conc a).
                rewrite (list_add_conc a (bl ++ al')).
                rewrite <- list_conc_assoc.
                rewrite <- Heql1, <- Heql2.
                cbn.
                do 2 apply list_perm_skip.
                exact IHal.
        +   pose proof (list_perm_add bl a) as eq.
            pose proof (list_perm_lpart al eq) as eq2.
            rewrite <- list_conc_assoc in eq2.
            cbn in eq2.
            apply (list_perm_trans2 eq2).
            cbn.
            rewrite <- Heql1, <- Heql2.
            apply list_perm_skip.
            apply list_perm_swap.
        +   pose proof (list_perm_add bl a) as eq.
            pose proof (list_perm_lpart al eq) as eq2.
            rewrite <- list_conc_assoc in eq2.
            cbn in eq2.
            apply (list_perm_trans2 eq2).
            cbn.
            rewrite <- Heql1, <- Heql2.
            apply list_perm_skip.
            apply (list_perm_trans IHal1 IHal2).
Qed.

Theorem list_perm_rpart {U} : ∀ (al bl cl : list U),
        list_permutation bl cl → list_permutation (al ++ bl) (al ++ cl).
    intros al bl cl blcl.
    apply (list_perm_trans (list_perm_conc al bl)).
    apply (list_perm_trans2 (list_perm_conc cl al)).
    apply list_perm_lpart.
    exact blcl.
Qed.

Theorem list_in_unique_perm {U} : ∀ al bl : list U,
        list_unique al → list_unique bl → (∀ x, in_list al x ↔ in_list bl x) →
        list_permutation al bl.
    intros al bl al_uni bl_uni l_in.
    revert bl bl_uni l_in.
    induction al; intros.
    -   destruct bl.
        1: exact list_perm_nil.
        specialize (l_in u) as [l_in1 l_in2].
        exfalso; apply l_in2.
        left; reflexivity.
    -   assert (in_list bl a) as bl_a.
        {
            apply l_in.
            left.
            reflexivity.
        }
        pose proof (in_list_split _ _ bl_a) as [bl1 [bl2 bl_eq]].
        pose (bl' := bl1 ++ bl2).
        assert (∀ x, in_list al x ↔ in_list bl' x) as l_in'.
        {
            intros x.
            unfold bl'.
            split.
            -   intros x_in.
                assert (in_list bl x) as bl_x.
                {
                    apply l_in.
                    right.
                    exact x_in.
                }
                rewrite bl_eq in bl_x.
                apply in_list_conc in bl_x as [bl_x|[bl_x|bl_x]].
                +   apply in_list_lconc.
                    exact bl_x.
                +   subst x.
                    destruct al_uni.
                    contradiction.
                +   apply in_list_rconc.
                    exact bl_x.
            -   intros x_in.
                assert (in_list bl x) as bl_x.
                {
                    rewrite bl_eq.
                    apply in_list_conc in x_in.
                    destruct x_in as [x_in|x_in].
                    -   apply in_list_lconc.
                        exact x_in.
                    -   apply in_list_rconc.
                        right.
                        exact x_in.
                }
                apply l_in in bl_x.
                destruct bl_x as [ax|al_x].
                +   subst x.
                    rewrite bl_eq in bl_uni.
                    exfalso; clear - bl_uni x_in.
                    apply in_list_conc in x_in.
                    destruct x_in as [x_in|x_in].
                    *   apply (list_in_not_unique bl1 (a :: bl2) a);
                            try assumption.
                        left.
                        reflexivity.
                    *   apply (list_in_not_unique (bl1 ++ a :: list_end) bl2 a);
                            try assumption.
                        --  apply in_list_rconc.
                            left.
                            reflexivity.
                        --  rewrite <- list_conc_assoc.
                            cbn.
                            exact bl_uni.
                +   exact al_x.
        }
        assert (list_unique bl') as bl'_uni.
        {
            subst bl; unfold bl'.
            clear - bl_uni.
            induction bl1.
            -   cbn in *.
                apply bl_uni.
            -   cbn in *.
                split.
                +   intros contr.
                    apply bl_uni.
                    apply in_list_conc in contr as [contr|contr].
                    *   apply in_list_lconc.
                        exact contr.
                    *   apply in_list_rconc.
                        right.
                        exact contr.
                +   apply IHbl1.
                    apply bl_uni.
        }
        specialize (IHal (rand al_uni) bl' bl'_uni l_in').
        rewrite bl_eq.
        pose proof (list_perm_conc (a :: bl2) bl1) as eq.
        apply (list_perm_trans2 eq).
        cbn.
        apply list_perm_skip.
        apply (list_perm_trans IHal).
        apply list_perm_conc.
Qed.

Lemma list_perm_in_wlog {U} : ∀ al bl : list U,
        list_permutation al bl → (∀ x, in_list al x → in_list bl x).
    intros al bl albl x al_x.
    induction albl.
    -   contradiction al_x.
    -   destruct al_x as [eq|al_x].
        +   left.
            exact eq.
        +   right.
            exact (IHalbl al_x).
    -   destruct al_x as [eq|[eq|al_x]].
        +   right; left.
            exact eq.
        +   left.
            exact eq.
        +   right; right.
            exact al_x.
    -   apply IHalbl2.
        apply IHalbl1.
        exact al_x.
Qed.

Theorem list_perm_in {U} : ∀ al bl : list U,
        list_permutation al bl → (∀ x, in_list al x ↔ in_list bl x).
    intros al bl albl x.
    split; apply list_perm_in_wlog.
    -   exact albl.
    -   apply list_perm_sym.
        exact albl.
Qed.

Theorem list_perm_unique {U} : ∀ al bl : list U,
        list_permutation al bl → list_unique al → list_unique bl.
    intros al bl albl al_uni.
    induction albl.
    -   exact al_uni.
    -   cbn in *.
        split.
        +   intros contr.
            apply al_uni.
            apply (list_perm_in albl).
            exact contr.
        +   apply IHalbl.
            apply al_uni.
    -   cbn in *.
        rewrite not_or.
        rewrite not_or in al_uni.
        destruct al_uni as [[neq y_in] [x_in l_uni]].
        repeat split; try assumption.
        rewrite neq_sym.
        exact neq.
    -   apply IHalbl2.
        apply IHalbl1.
        exact al_uni.
Qed.

Theorem list_image_perm {U V} : ∀ al bl (f : U → V),
        list_permutation al bl →
        list_permutation (list_image al f) (list_image bl f).
    intros al bl f albl.
    induction albl.
    -   cbn.
        exact list_perm_nil.
    -   cbn.
        apply list_perm_skip.
        exact IHalbl.
    -   cbn.
        apply list_perm_swap.
    -   apply (list_perm_trans IHalbl1 IHalbl2).
Qed.

Theorem list_perm_split {U} : ∀ l1 l2 (x : U),
        list_permutation (l1 ++ x :: l2) (x :: l1 ++ l2).
    intros l1 l2 x.
    rewrite (list_add_conc).
    rewrite list_conc_assoc.
    change (x :: l1 ++ l2) with ((x :: l1) ++ l2).
    apply list_perm_lpart.
    apply list_perm_sym.
    apply list_perm_add.
Qed.

Theorem list_perm_single {U} : ∀ (x : U) l, list_permutation (x :: list_end) l →
        l = x :: list_end.
    intros x l l_perm.
    remember (x :: list_end) as m in l_perm.
    induction l_perm.
    -   inversion Heqm.
    -   inversion Heqm.
        subst x0 l.
        apply list_perm_nil_eq in l_perm.
        rewrite <- l_perm.
        reflexivity.
    -   inversion Heqm.
    -   subst l.
        apply IHl_perm2.
        apply IHl_perm1.
        reflexivity.
Qed.

Theorem list_perm_eq {U} : ∀ l1 l2 : list U, l1 = l2 → list_permutation l1 l2.
    intros l1 l2 eq.
    rewrite eq.
    apply list_perm_refl.
Qed.

Theorem list_unique_conc {U} : ∀ l1 l2 : list U,
        list_unique (l1 ++ l2) → list_unique (l2 ++ l1).
    intros l1 l2.
    apply list_perm_unique.
    apply list_perm_conc.
Qed.

Theorem list_size_conc {U} : ∀ l1 l2 : list U,
        list_size (l1 ++ l2) = list_size (l2 ++ l1).
    induction l1; intros l2.
    -   cbn.
        rewrite list_conc_end.
        reflexivity.
    -   cbn.
        rewrite IHl1; clear IHl1.
        induction l2.
        +   cbn.
            reflexivity.
        +   cbn.
            rewrite IHl2.
            reflexivity.
Qed.

Theorem func_to_list_size {U} : ∀ (f : nat → U) n,
        list_size (func_to_list f n) = n.
    intros f n.
    nat_induction n.
    -   unfold zero at 1; cbn.
        reflexivity.
    -   cbn.
        rewrite list_size_conc.
        cbn.
        unfold func_to_list in IHn.
        rewrite IHn.
        reflexivity.
Qed.

Theorem func_to_list_unique {U} : ∀ (f : nat → U) n,
        (∀ m1 m2, m1 < n → m2 < n → f m1 = f m2 → m1 = m2) →
        list_unique (func_to_list f n).
    intros f n f_inj.
    nat_induction n.
    -   unfold zero; cbn.
        exact true.
    -   cbn.
        apply list_unique_conc.
        cbn.
        split.
        +   clear IHn.
            change (list_reverse _) with (func_to_list f n).
            intros contr.
            apply in_list_nth in contr as [m [m_lt fn_eq]].
            rewrite func_to_list_size in m_lt.
            rewrite func_to_list_nth_lt in fn_eq by exact m_lt.
            apply f_inj in fn_eq.
            *   subst.
                destruct m_lt; contradiction.
            *   apply nat_lt_suc.
            *   exact (trans m_lt (nat_lt_suc n)).
        +   apply IHn.
            intros m1 m2 m1_lt m2_lt eq.
            apply f_inj.
            *   exact (trans m1_lt (nat_lt_suc n)).
            *   exact (trans m2_lt (nat_lt_suc n)).
            *   exact eq.
Qed.

Fixpoint list_filter {U} (S : U → Prop) (l : list U) :=
    match l with
    | list_end => list_end
    | x :: l' => If S x then x :: list_filter S l' else list_filter S l'
    end.

Theorem list_filter_in_S {U} : ∀ S (l : list U) x,
        in_list (list_filter S l) x → S x.
    intros S l x x_in.
    induction l.
    -   contradiction x_in.
    -   cbn in x_in.
        case_if.
        +   destruct x_in as [eq|x_in].
            *   subst.
                exact s.
            *   exact (IHl x_in).
        +   exact (IHl x_in).
Qed.

Theorem list_filter_in {U} : ∀ S (l : list U) x,
        in_list (list_filter S l) x → in_list l x.
    intros S l x x_in.
    induction l.
    -   contradiction x_in.
    -   cbn in x_in.
        case_if.
        +   cbn in x_in.
            destruct x_in as [x_eq|x_in].
            *   subst a.
                left.
                reflexivity.
            *   right.
                exact (IHl x_in).
        +   right.
            exact (IHl x_in).
Qed.

Theorem list_filter_unique {U} : ∀ S (l : list U),
        list_unique l → list_unique (list_filter S l).
    intros S l l_uni.
    induction l.
    -   cbn.
        exact true.
    -   cbn in *.
        case_if.
        +   cbn.
            split.
            *   intros contr.
                apply l_uni.
                apply list_filter_in with S.
                exact contr.
            *   apply IHl.
                apply l_uni.
        +   apply IHl.
            apply l_uni.
Qed.

Theorem list_filter_image_in {U V} : ∀ S (f : U → V) (l : list U) x,
        in_list (list_image (list_filter S l) f) x → in_list (list_image l f) x.
    intros S f l x x_in.
    induction l.
    -   contradiction x_in.
    -   cbn in x_in.
        case_if.
        +   cbn in x_in.
            destruct x_in as [x_eq|x_in].
            *   subst x.
                left.
                reflexivity.
            *   right.
                exact (IHl x_in).
        +   right.
            exact (IHl x_in).
Qed.

Theorem list_filter_image_unique {U V} : ∀ S (f : U → V) (l : list U),
        list_unique (list_image l f) →
        list_unique (list_image (list_filter S l) f).
    intros S f l l_uni.
    induction l.
    -   cbn.
        exact true.
    -   cbn in *.
        case_if.
        +   cbn.
            split.
            *   intros contr.
                apply l_uni.
                apply list_filter_image_in with S.
                exact contr.
            *   apply IHl.
                apply l_uni.
        +   apply IHl.
            apply l_uni.
Qed.

Theorem list_filter_filter {U} : ∀ S (l : list U),
        list_filter S l = list_filter S (list_filter S l).
    intros S l.
    induction l.
    -   cbn.
        reflexivity.
    -   cbn.
        case_if.
        +   cbn.
            case_if.
            *   rewrite IHl at 1.
                reflexivity.
            *   contradiction.
        +   exact IHl.
Qed.

Theorem list_image_unique {U V} : ∀ (l : list U) (f : U → V),
        list_unique (list_image l f) → list_unique l.
    intros l f l_uni.
    induction l.
    -   exact true.
    -   cbn in *.
        split.
        +   intros contr.
            apply l_uni.
            clear l_uni IHl.
            apply in_list_image.
            exact contr.
        +   apply IHl.
            apply l_uni.
Qed.
