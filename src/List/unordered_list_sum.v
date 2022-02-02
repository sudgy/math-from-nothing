Require Import init.

Require Export plus_sum.
Require Export list.
Require Export unordered_list_base.
Require Export unordered_list_func.
Require Export unordered_list_nat.

Require Import equivalence.

(* begin hide *)
Unset Keyed Unification.

Section Sum.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN
}.

(* end hide *)
Lemma ulist_sum_wd : ∀ l1 l2 : list U, list_permutation l1 l2 →
        list_sum l1 = list_sum l2.
    intros l1 l2 eq.
    induction eq.
    -   reflexivity.
    -   cbn.
        rewrite IHeq.
        reflexivity.
    -   cbn.
        do 2 rewrite plus_assoc.
        rewrite (plus_comm x y).
        reflexivity.
    -   rewrite IHeq1.
        exact IHeq2.
Qed.
Definition ulist_sum := unary_op (E := ulist_equiv U) ulist_sum_wd.

Theorem ulist_sum_end : ulist_sum ulist_end = 0.
    unfold ulist_sum, ulist_end; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_sum_add : ∀ a l, ulist_sum (a ::: l) = a + ulist_sum l.
    intros a l.
    equiv_get_value l.
    unfold ulist_sum, ulist_add; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_sum_plus : ∀ a b, ulist_sum (a +++ b) = ulist_sum a + ulist_sum b.
    intros a b.
    equiv_get_value a b.
    unfold ulist_sum, ulist_conc; equiv_simpl.
    apply list_sum_plus.
Qed.

Theorem ulist_sum_neg : ∀ l, -ulist_sum l = ulist_sum (ulist_image l neg).
    intros l.
    equiv_get_value l.
    unfold ulist_sum, ulist_image; equiv_simpl.
    apply list_sum_neg.
Qed.

Theorem ulist_sum_minus : ∀ a b,
        ulist_sum a - ulist_sum b = ulist_sum (a +++ (ulist_image b neg)).
    intros a b.
    rewrite ulist_sum_plus.
    rewrite ulist_sum_neg.
    reflexivity.
Qed.

Theorem ulist_sum_sum_eq : ∀ f n, ulist_sum (func_to_ulist f n) = sum f 0 n.
    intros f n.
    rewrite func_to_list_ulist.
    unfold ulist_sum; equiv_simpl.
    apply list_sum_sum_eq.
Qed.

Theorem ulist_sum_func_single : ∀ a m n, m < n →
        ulist_sum (func_to_ulist (λ x, If x = m then a else 0) n) = a.
    intros a m n ltq.
    rewrite func_to_list_ulist.
    unfold ulist_sum; equiv_simpl.
    apply list_sum_func_single.
    exact ltq.
Qed.
(* begin hide *)

End Sum.
(* end hide *)
