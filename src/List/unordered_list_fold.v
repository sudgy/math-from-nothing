
Require Import init.

Require Export mult_ring.
Require Export list.
Require Export unordered_list_base.
Require Export unordered_list_nat.

Require Import equivalence.

Section Fold.

Context {U} `{CRingClass U}.

Theorem ulist_sum_wd : ∀ l1 l2, list_permutation l1 l2 →
    list_sum l1 = list_sum l2.
Proof.
    induction l1 as [|a l1]; intros l2 eq.
    -   apply list_perm_nil_eq in eq.
        subst l2.
        reflexivity.
    -   apply list_perm_split_eq in eq as [l3 [l4 [l_eq eq]]]; subst l2.
        rewrite list_sum_conc.
        do 2 rewrite list_sum_add.
        rewrite (IHl1 _ eq).
        rewrite list_sum_conc.
        apply plus_3.
Qed.
Definition ulist_sum := unary_op (E := ulist_equiv U) ulist_sum_wd.

Theorem ulist_sum_end : ulist_sum ⟦⟧ = 0.
Proof.
    unfold ulist_sum, ulist_end; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_sum_add : ∀ a l, ulist_sum (a ː l) = a + ulist_sum l.
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_sum, ulist_add; equiv_simpl.
    apply list_sum_add.
Qed.

Theorem list_sum_single : ∀ x, ulist_sum ⟦x⟧ = x.
Proof.
    intros x.
    rewrite ulist_sum_add, ulist_sum_end.
    apply plus_rid.
Qed.

Theorem ulist_sum_conc : ∀ a b, ulist_sum (a + b) = ulist_sum a + ulist_sum b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold ulist_sum, plus at 1; equiv_simpl.
    apply list_sum_conc.
Qed.

Theorem ulist_sum_neg : ∀ l, ulist_sum (ulist_image neg l) = -ulist_sum l.
Proof.
    intros l.
    equiv_get_value l.
    unfold ulist_sum, ulist_image; equiv_simpl.
    apply list_sum_neg.
Qed.

Theorem ulist_sum_minus : ∀ a b,
    ulist_sum (a + (ulist_image neg b)) = ulist_sum a - ulist_sum b.
Proof.
    intros a b.
    rewrite ulist_sum_conc.
    rewrite ulist_sum_neg.
    reflexivity.
Qed.

Theorem list_prod_perm : ∀ l1 l2, list_permutation l1 l2 →
    list_prod l1 = list_prod l2.
Proof.
    induction l1 as [|a l1]; intros l2 eq.
    -   apply list_perm_nil_eq in eq.
        subst l2.
        reflexivity.
    -   apply list_perm_split_eq in eq as [l3 [l4 [l_eq eq]]]; subst l2.
        rewrite list_prod_conc.
        do 2 rewrite list_prod_add.
        rewrite (IHl1 _ eq).
        rewrite list_prod_conc.
        do 2 rewrite mult_assoc.
        apply rmult.
        apply mult_comm.
Qed.
Definition ulist_prod := unary_op (E := ulist_equiv U) list_prod_perm.

Theorem ulist_prod_end : ulist_prod ulist_end = 1.
Proof.
    unfold ulist_prod, ulist_end; equiv_simpl.
    apply list_prod_end.
Qed.

Theorem ulist_prod_add : ∀ a l, ulist_prod (a ː l) = a * ulist_prod l.
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_prod, ulist_add; equiv_simpl.
    apply list_prod_add.
Qed.

Theorem ulist_prod_single : ∀ x, ulist_prod ⟦x⟧ = x.
Proof.
    intros x.
    rewrite ulist_prod_add, ulist_prod_end.
    apply mult_rid.
Qed.

Theorem ulist_prod_conc :
    ∀ a b, ulist_prod (a + b) = ulist_prod a * ulist_prod b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold ulist_prod, plus; equiv_simpl.
    apply list_prod_conc.
Qed.

End Fold.
