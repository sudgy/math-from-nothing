
Require Import init.

Require Export mult_ring.
Require Export list.
Require Export unordered_list_base.
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

Theorem ulist_sum_wd : ∀ l1 l2, list_permutation l1 l2 →
    list_sum l1 = list_sum l2.
Proof.
    induction l1 as [|a l1]; intros l2 eq.
    -   apply list_perm_nil_eq in eq.
        subst l2.
        reflexivity.
    -   assert (in_list (a ꞉ l1) a) as a_in by (left; reflexivity).
        apply (list_perm_in eq) in a_in.
        apply in_list_split in a_in as [l3 [l4 l2_eq]]; subst l2.
        rewrite list_sum_plus.
        do 2 rewrite list_sum_add.
        pose proof (list_perm_split l3 l4 a) as eq2.
        pose proof (list_perm_trans eq eq2) as eq3.
        apply list_perm_add_eq in eq3.
        rewrite (IHl1 _ eq3).
        rewrite list_sum_plus.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.
Definition ulist_sum := unary_op (E := ulist_equiv U) ulist_sum_wd.

Theorem ulist_sum_end : ulist_sum ulist_end = 0.
Proof.
    unfold ulist_sum, ulist_end; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_sum_add : ∀ a l, ulist_sum (a ː l) = a + ulist_sum l.
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_sum, ulist_add; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_sum_plus : ∀ a b, ulist_sum (a + b) = ulist_sum a + ulist_sum b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold ulist_sum, plus; equiv_simpl.
    apply list_sum_plus.
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
    rewrite ulist_sum_plus.
    rewrite ulist_sum_neg.
    reflexivity.
Qed.
(* begin hide *)

End Sum.
(* end hide *)

(* begin hide *)
Section Product.

Context {U} `{
    UM : Mult U,
    UO : One U,
    @MultAssoc U UM,
    @MultComm U UM,
    @MultLid U UM UO
}.

(* end hide *)
Theorem list_prod_perm : ∀ l1 l2, list_permutation l1 l2 →
    list_prod l1 = list_prod l2.
Proof.
    induction l1 as [|a l1]; intros l2 eq.
    -   apply list_perm_nil_eq in eq.
        subst l2.
        reflexivity.
    -   assert (in_list (a ꞉ l1) a) as a_in by (left; reflexivity).
        apply (list_perm_in eq) in a_in.
        apply in_list_split in a_in as [l3 [l4 l2_eq]]; subst l2.
        rewrite list_prod_mult.
        do 2 rewrite list_prod_add.
        pose proof (list_perm_split l3 l4 a) as eq2.
        pose proof (list_perm_trans eq eq2) as eq3.
        apply list_perm_add_eq in eq3.
        rewrite (IHl1 _ eq3).
        rewrite list_prod_mult.
        do 2 rewrite mult_assoc.
        apply rmult.
        apply mult_comm.
Qed.
Definition ulist_prod := unary_op (E := ulist_equiv U) list_prod_perm.

Theorem ulist_prod_end : ulist_prod ulist_end = 1.
Proof.
    unfold ulist_prod, ulist_end; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_prod_add : ∀ a l, ulist_prod (a ː l) = a * ulist_prod l.
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_prod, ulist_add; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_prod_mult :
    ∀ a b, ulist_prod (a + b) = ulist_prod a * ulist_prod b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold ulist_prod, plus; equiv_simpl.
    apply list_prod_mult.
Qed.
(* begin hide *)
End Product.
(* end hide *)
