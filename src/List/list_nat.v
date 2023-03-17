Require Import init.

Require Export list_base.
Require Export list_prop.

Require Export nat.

Fixpoint list_size {A : Type} (l : list A) :=
    match l with
    | a ꞉ l' => nat_suc (list_size l')
    | list_end => 0
    end.

Theorem list_size_conc {U} : ∀ l1 l2 : list U,
    list_size (l1 + l2) = list_size (l2 + l1).
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
    list_size (l1 + l2) = list_size l1 + list_size l2.
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

Theorem list_image_size {A B} : ∀ l (f : A → B),
    list_size (list_image f l) = list_size l.
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
    | x ꞉ l' => (If x = a then 1 else 0) + list_count l' a
end.

Theorem list_count_conc {U} : ∀ l1 l2 (a : U),
    list_count (l1 + l2) a = list_count l1 a + list_count l2 a.
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
