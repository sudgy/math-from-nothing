Require Import init.

Require Export list_base.
Require Export list_func.
Require Export list_prop.

Require Import nat.

Set Implicit Arguments.

Fixpoint list_size {A : Type} (l : list A) :=
    match l with
    | a :: l' => nat_suc (list_size l')
    | list_end => 0
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

Theorem list_size_plus {U} : ∀ l1 l2 : list U,
        list_size (l1 ++ l2) = list_size l1 + list_size l2.
    intros l1 l2.
    induction l1.
    -   cbn.
        rewrite plus_lid.
        reflexivity.
    -   cbn.
        rewrite IHl1.
        rewrite nat_plus_lsuc.
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
