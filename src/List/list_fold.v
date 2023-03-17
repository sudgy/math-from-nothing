Require Import init.

Require Export list_base.
Require Import mult_ring.

Fixpoint rfold {U} (op : U → U → U) (init : U) (l : list U) :=
    match l with
    | [] => init
    | a ꞉ l' => op a (rfold op init l')
    end.
Arguments rfold : simpl never.

Theorem rfold_end {U} (op : U → U → U) init : rfold op init [] = init.
Proof.
    reflexivity.
Qed.

Theorem rfold_add {U} (op : U → U → U) init : ∀ a l,
    rfold op init (a ꞉ l) = op a (rfold op init l).
Proof.
    reflexivity.
Qed.

Fixpoint list_sum {U} `{Plus U, Zero U} (l : list U) :=
    match l with
    | list_end => zero
    | a ꞉ l' => a + list_sum l'
    end.

Fixpoint list_prod {U} `{Mult U, One U} (l : list U) :=
    match l with
    | list_end => one
    | a ꞉ l' => a * list_prod l'
    end.

Section Sum.

Context {U} `{AllPlus U}.

Theorem list_sum_plus :
    ∀ l1 l2, list_sum (l1 + l2) = list_sum l1 + list_sum l2.
Proof.
    intros l1 l2.
    induction l1.
    -   cbn.
        rewrite plus_lid.
        reflexivity.
    -   rewrite list_conc_add.
        cbn.
        rewrite IHl1.
        apply plus_assoc.
Qed.

Theorem list_sum_neg : ∀ l, -list_sum l = list_sum (list_image neg l).
Proof.
    induction l.
    -   cbn.
        apply neg_zero.
    -   cbn.
        rewrite neg_plus.
        rewrite IHl.
        reflexivity.
Qed.

Theorem list_sum_minus : ∀ al bl,
    list_sum al - list_sum bl = list_sum (al + (list_image neg bl)).
Proof.
    intros al bl.
    rewrite list_sum_neg.
    rewrite list_sum_plus.
    reflexivity.
Qed.

(* begin hide *)
End Sum.

Section Product.

Context {U} `{AllMult U}.

(* end hide *)
Theorem list_prod_mult :
    ∀ l1 l2, list_prod (l1 + l2) = list_prod l1 * list_prod l2.
Proof.
    intros l1 l2.
    induction l1.
    -   cbn.
        symmetry; apply mult_lid.
    -   rewrite list_conc_add.
        cbn.
        rewrite IHl1.
        apply mult_assoc.
Qed.
(* begin hide *)

End Product.
(* end hide *)
