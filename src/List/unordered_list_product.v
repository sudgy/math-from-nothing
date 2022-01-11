Require Import init.

Require Import mult_product.
Require Import list.
Require Export unordered_list_base.

Require Import equivalence.

Section Product.

Context {U} `{
    UM : Mult U,
    UO : One U,
    @MultAssoc U UM,
    @MultComm U UM,
    @MultLid U UM UO
}.

Definition ulist_prod := unary_op (E := ulist_equiv U) list_prod_perm.

Theorem ulist_prod_end : ulist_prod ulist_end = 1.
    unfold ulist_prod, ulist_end; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_prod_add : ∀ a l, ulist_prod (a ::: l) = a * ulist_prod l.
    intros a l.
    equiv_get_value l.
    unfold ulist_prod, ulist_add; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_prod_mult :
        ∀ a b, ulist_prod (a +++ b) = ulist_prod a * ulist_prod b.
    intros a b.
    equiv_get_value a b.
    unfold ulist_prod, ulist_conc; equiv_simpl.
    apply list_prod_mult.
Qed.

End Product.
