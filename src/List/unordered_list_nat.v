Require Import init.

Require Import list.
Require Import unordered_list_base.
Require Import unordered_list_func.
Require Import unordered_list_prop.

Require Import nat.
Require Import equivalence.

Lemma ulist_size_wd U : ∀ l1 l2 : list U, list_permutation l1 l2 →
    list_size l1 = list_size l2.
Proof.
    intros l1 l2 eq.
    induction eq.
    -   reflexivity.
    -   cbn.
        rewrite IHeq.
        reflexivity.
    -   cbn.
        reflexivity.
    -   rewrite IHeq1.
        exact IHeq2.
Qed.
Definition ulist_size {U} := unary_op (E := ulist_equiv U) (ulist_size_wd U).

Definition func_to_ulist {U} (f : nat → U) n :=
    to_equiv (ulist_equiv U) (func_to_list_base f n).

Theorem func_to_list_ulist {U} : ∀ (f : nat → U) n,
    func_to_ulist f n = to_equiv (ulist_equiv U) (func_to_list f n).
Proof.
    intros f n.
    unfold func_to_ulist; equiv_simpl.
    unfold func_to_list.
    apply list_perm_reverse.
Qed.

Theorem func_to_ulist_zero {U} : ∀ (f : nat → U), func_to_ulist f 0 = ulist_end.
Proof.
    intros f.
    unfold func_to_ulist, ulist_end; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem func_to_ulist_in {U} : ∀ (f : nat → U) n m, m < n →
    in_ulist (func_to_ulist f n) (f m).
Proof.
    intros f n m ltq.
    apply nat_lt_ex in ltq as [c eq].
    subst n.
    unfold in_ulist, func_to_ulist; equiv_simpl.
    nat_induction c.
    -   change 1 with (nat_suc 0).
        rewrite nat_plus_rsuc.
        rewrite plus_rid.
        cbn.
        left.
        reflexivity.
    -   rewrite nat_plus_rsuc.
        cbn.
        right.
        exact IHc.
Qed.

Theorem func_to_ulist_eq {A : Type} (f g : nat → A) n :
    (∀ m, m < n → f m = g m) → func_to_ulist f n = func_to_ulist g n.
Proof.
    intros eq.
    do 2 rewrite func_to_list_ulist.
    equiv_simpl.
    rewrite (func_to_list_eq _ _ eq).
    apply list_perm_refl.
Qed.

Theorem func_to_ulist_image {A B} : ∀ (f : nat → A) (g : A → B) n,
    ulist_image (func_to_ulist f n) g = func_to_ulist (λ m, g (f m)) n.
Proof.
    intros f g n.
    do 2 rewrite func_to_list_ulist.
    unfold ulist_image; equiv_simpl.
    rewrite func_to_list_image.
    apply list_perm_refl.
Qed.

Theorem ulist_size_end {U} : ulist_size (@ulist_end U) = 0.
Proof.
    unfold ulist_size, ulist_end; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_size_add {U} : ∀ (a : U) l,
    ulist_size (a ::: l) = nat_suc (ulist_size l).
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_size, ulist_add; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_size_plus {U} : ∀ l1 l2 : ulist U,
    ulist_size (l1 +++ l2) = ulist_size l1 + ulist_size l2.
Proof.
    intros l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_size, ulist_conc; equiv_simpl.
    apply list_size_plus.
Qed.

Theorem func_to_ulist_size {U} : ∀ (f : nat → U) n,
    ulist_size (func_to_ulist f n) = n.
Proof.
    intros f n.
    rewrite func_to_list_ulist.
    unfold ulist_size; equiv_simpl.
    apply func_to_list_size.
Qed.

Theorem func_to_ulist_unique {U} : ∀ (f : nat → U) n,
    (∀ m1 m2, m1 < n → m2 < n → f m1 = f m2 → m1 = m2) →
    ulist_unique (func_to_ulist f n).
Proof.
    intros f n.
    rewrite func_to_list_ulist.
    unfold ulist_unique; equiv_simpl.
    apply func_to_list_unique.
Qed.

Theorem func_to_ulist_suc {U} : ∀ (f : nat → U) n,
    func_to_ulist f (nat_suc n) = f n ::: func_to_ulist f n.
Proof.
    intros f n.
    rewrite ulist_add_conc.
    rewrite ulist_conc_comm.
    do 2 rewrite func_to_list_ulist.
    unfold ulist_add, ulist_conc, ulist_end; equiv_simpl.
    cbn.
    change (list_reverse (func_to_list_base f n)) with (func_to_list f n).
    apply list_perm_refl.
Qed.

Theorem ulist_size_neq {U} : ∀ l1 l2 : ulist U, ulist_size l1 ≠ ulist_size l2 →
    l1 ≠ l2.
Proof.
    intros l1 l2 eq contr.
    subst.
    contradiction.
Qed.
