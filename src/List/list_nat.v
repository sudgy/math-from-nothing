Require Import init.

Require Export list_base.
Require Export list_func.
Require Export list_prop.

Require Export nat.

Set Implicit Arguments.

Fixpoint list_size {A : Type} (l : list A) :=
    match l with
    | a :: l' => nat_suc (list_size l')
    | list_end => 0
    end.

Fixpoint list_nth {A} (l : list A) (n : nat) (default : A) :=
    match n, l with
    | nat_zero, x :: _ => x
    | nat_suc n', x :: l' => list_nth l' n' default
    | _, _ => default
    end.

Theorem list_nth_eq {U} : ∀ l n (a b : U), n < list_size l →
    list_nth l n a = list_nth l n b.
Proof.
    intros l n a b n_lt.
    revert n n_lt.
    induction l.
    -   intros n n_lt.
        cbn in n_lt.
        apply nat_neg2 in n_lt.
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
Proof.
    intros l x x_in.
    induction l.
    -   contradiction x_in.
    -   destruct x_in as [x_eq|x_in].
        +   subst a.
            exists 0.
            split.
            *   cbn.
                apply nat_pos2.
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
Proof.
    intros f m n a ltq.
    rewrite func_to_list2_eq.
    apply nat_lt_ex in ltq as [c c_eq].
    subst n.
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

Theorem func_to_list_nth_ge {A} : ∀ f m n (a : A), n ≤ m →
    list_nth (func_to_list f n) m a = a.
Proof.
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
Proof.
    intros f g n.
    do 2 rewrite func_to_list2_eq.
    revert f.
    nat_induction n.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        intros f.
        rewrite list_image_add.
        specialize (IHn (λ m, f (nat_suc m))).
        unfold func_to_list2 in IHn.
        rewrite <- func_to_list2_base_eq in IHn.
        rewrite IHn.
        rewrite func_to_list2_base_eq.
        reflexivity.
Qed.

Theorem list_size_conc {U} : ∀ l1 l2 : list U,
    list_size (l1 ++ l2) = list_size (l2 ++ l1).
Proof.
    induction l1; intros l2.
    -   rewrite list_conc_lid, list_conc_rid.
        reflexivity.
    -   rewrite list_conc_add.
        cbn.
        rewrite IHl1; clear IHl1.
        induction l2.
        +   cbn.
            reflexivity.
        +   rewrite list_conc_add.
            cbn.
            rewrite IHl2.
            reflexivity.
Qed.

Theorem list_size_plus {U} : ∀ l1 l2 : list U,
    list_size (l1 ++ l2) = list_size l1 + list_size l2.
Proof.
    intros l1 l2.
    induction l1.
    -   cbn.
        rewrite plus_lid.
        reflexivity.
    -   rewrite list_conc_add.
        cbn.
        rewrite IHl1.
        rewrite nat_plus_lsuc.
        reflexivity.
Qed.

Theorem func_to_list_size {U} : ∀ (f : nat → U) n,
    list_size (func_to_list f n) = n.
Proof.
    intros f n.
    nat_induction n.
    -   unfold zero at 1; cbn.
        reflexivity.
    -   unfold func_to_list; cbn.
        rewrite list_reverse_add.
        rewrite list_size_conc.
        rewrite list_conc_add, list_conc_lid.
        cbn.
        unfold func_to_list in IHn.
        rewrite IHn.
        reflexivity.
Qed.

Theorem func_to_list_unique {U} : ∀ (f : nat → U) n,
    (∀ m1 m2, m1 < n → m2 < n → f m1 = f m2 → m1 = m2) →
    list_unique (func_to_list f n).
Proof.
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

Theorem list_size_neq {U} : ∀ l1 l2 : list U, list_size l1 ≠ list_size l2 →
    l1 ≠ l2.
Proof.
    intros l1 l2 eq contr.
    subst.
    contradiction.
Qed.

Theorem list_image_size {A B} : ∀ l (f : A → B),
    list_size (list_image l f) = list_size l.
Proof.
    intros l f.
    induction l.
    -   cbn.
        reflexivity.
    -   rewrite list_image_add; cbn.
        rewrite IHl.
        reflexivity.
Qed.

Fixpoint list_count {U} (l : list U) (a : U) : nat :=
    match l with
    | [] => 0
    | x :: l' => (If x = a then 1 else 0) + list_count l' a
end.

Theorem list_count_conc {U} : ∀ l1 l2 (a : U),
    list_count (l1 ++ l2) a = list_count l1 a + list_count l2 a.
Proof.
    intros l1 l2 a.
    induction l1.
    -   cbn.
        rewrite plus_lid, list_conc_lid.
        reflexivity.
    -   rewrite list_conc_add.
        cbn.
        rewrite IHl1.
        apply plus_assoc.
Qed.

Theorem list_count_in {U} : ∀ l (a : U), in_list l a ↔ 0 ≠ list_count l a.
Proof.
    intros l a.
    split.
    -   intros a_in contr.
        induction l as [|x l].
        +   contradiction a_in.
        +   cbn in *.
            case_if [eq|neq].
            *   inversion contr.
            *   destruct a_in as [|a_in]; [>contradiction|].
                rewrite plus_lid in contr.
                exact (IHl a_in contr).
    -   intros neq.
        induction l as [|x l].
        +   contradiction.
        +   cbn in *.
            case_if [eq|neq'].
            *   left; assumption.
            *   right.
                rewrite plus_lid in neq.
                exact (IHl neq).
Qed.

Theorem list_count_nin {U} : ∀ l (a : U), ¬in_list l a ↔ 0 = list_count l a.
Proof.
    intros l a.
    rewrite list_count_in.
    apply not_not.
Qed.

Theorem list_count_unique {U} : ∀ l (a : U), list_unique l → list_count l a ≤ 1.
Proof.
    intros l x l_uni.
    induction l as [|a l].
    -   apply nat_pos.
    -   cbn in *.
        destruct l_uni as [a_nin l_uni].
        case_if [eq|neq].
        +   subst x.
            apply list_count_nin in a_nin.
            rewrite <- a_nin.
            rewrite plus_rid.
            apply refl.
        +   rewrite plus_lid.
            exact (IHl l_uni).
Qed.

Theorem list_count_in_unique {U} : ∀ l (a : U), list_unique l → in_list l a →
    list_count l a = 1.
Proof.
    intros l a l_uni a_in.
    apply antisym.
    -   apply list_count_unique.
        exact l_uni.
    -   apply list_count_in in a_in.
        remember (list_count l a) as n.
        clear - a_in.
        nat_destruct n.
        +   contradiction.
        +   exact true.
Qed.

Theorem list_count_reverse {U} : ∀ l (a : U),
    list_count l a = list_count (list_reverse l) a.
Proof.
    intros l a.
    induction l as [|b l].
    -   rewrite list_reverse_end.
        reflexivity.
    -   rewrite list_reverse_add.
        rewrite list_count_conc.
        cbn.
        rewrite plus_rid.
        rewrite plus_comm.
        apply rplus.
        exact IHl.
Qed.
