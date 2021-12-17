Require Import init.

Require Export list_base.
Require Export list_func.
Require Export list_prop.
Require Export list_nat.
Require Export list_perm.

Require Import nat.

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

Fixpoint list_prop {U} (S : U → Prop) (l : list U) :=
    match l with
    | list_end => True
    | a :: l' => S a ∧ list_prop S l'
    end.

Theorem list_prop_perm {U} : ∀ (S : U → Prop) (l1 l2 : list U),
        list_permutation l1 l2 → list_prop S l1 → list_prop S l2.
    intros S l1 l2 eq Sl1.
    induction eq.
    -   exact Sl1.
    -   cbn.
        split.
        +   apply Sl1.
        +   apply IHeq.
            apply Sl1.
    -   repeat split; apply Sl1.
    -   exact (IHeq2 (IHeq1 Sl1)).
Qed.
