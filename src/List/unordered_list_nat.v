Require Import init.

Require Import list.
Require Import unordered_list_base.
Require Import unordered_list_prop.

Require Import nat.
Require Import equivalence.

Lemma ulist_size_wd U : ∀ l1 l2 : list U, list_permutation l1 l2 →
    list_size l1 = list_size l2.
Proof.
    intros l1 l2 eq.
    revert l2 eq.
    induction l1 as [|a l1]; intros.
    -   apply list_perm_nil_eq in eq.
        destruct eq.
        reflexivity.
    -   assert (in_list (a ꞉ l1) a) as a_in by (left; reflexivity).
        apply (list_perm_in eq) in a_in.
        apply in_list_split in a_in as [l3 [l4 l2_eq]]; subst l2.
        apply (list_perm_trans2 (list_perm_split l3 l4 a)) in eq.
        apply list_perm_add_eq in eq.
        specialize (IHl1 _ eq).
        rewrite list_size_conc.
        rewrite list_conc_add.
        cbn.
        rewrite IHl1.
        rewrite list_size_conc.
        reflexivity.
Qed.
Definition ulist_size {U} := unary_op (E := ulist_equiv U) (ulist_size_wd U).

Theorem ulist_size_end {U} : ulist_size (@ulist_end U) = 0.
Proof.
    unfold ulist_size, ulist_end; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_size_add {U} : ∀ (a : U) l,
    ulist_size (a ː l) = nat_suc (ulist_size l).
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_size, ulist_add; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_size_plus {U} : ∀ l1 l2 : ulist U,
    ulist_size (l1 + l2) = ulist_size l1 + ulist_size l2.
Proof.
    intros l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_size, plus; equiv_simpl.
    apply list_size_plus.
Qed.
