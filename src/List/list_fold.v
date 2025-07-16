Require Import init.

Require Export list_base.
Require Import mult_ring.

Fixpoint rfold {U} (op : U → U → U) (init : U) (l : list U) :=
    match l with
    | [] => init
    | a ꞉ l' => op a (rfold op init l')
    end.
Arguments rfold : simpl never.

(** I recognize that there are many more theorems that could be proven for
well-behaved binary operations, but really I only care about sums and products
at the moment, and products have a grand total of one theorem that would need to
be repeated.  Thus, I'm barely proving anything about rfold itself.
*)
Section Fold.

Context {U} (op : U → U → U) (init : U).

Theorem rfold_end : rfold op init [] = init.
Proof.
    reflexivity.
Qed.

Theorem rfold_add : ∀ a l, rfold op init (a ꞉ l) = op a (rfold op init l).
Proof.
    reflexivity.
Qed.

End Fold.

Definition list_sum {U} `{Plus U, Zero U} (l : list U) := rfold plus zero l.
Arguments list_sum : simpl never.

Definition list_prod {U} `{Mult U, One U} (l : list U) := rfold mult one l.
Arguments list_prod : simpl never.

Section Fold.

Context {U} `{RingClass U}.

Theorem list_sum_end : list_sum [] = 0.
Proof.
    reflexivity.
Qed.

Theorem list_sum_add : ∀ x a, list_sum (x ꞉ a) = x + list_sum a.
Proof.
    reflexivity.
Qed.

Theorem list_sum_single : ∀ x, list_sum [x] = x.
Proof.
    intros x.
    rewrite list_sum_add, list_sum_end.
    apply plus_rid.
Qed.

Theorem list_sum_conc :
    ∀ l1 l2, list_sum (l1 + l2) = list_sum l1 + list_sum l2.
Proof.
    intros l1 l2.
    induction l1.
    -   rewrite list_conc_lid.
        rewrite list_sum_end.
        rewrite plus_lid.
        reflexivity.
    -   rewrite list_conc_add.
        do 2 rewrite list_sum_add.
        rewrite IHl1.
        apply plus_assoc.
Qed.

Theorem list_sum_neg : ∀ l, list_sum (list_image neg l) = -list_sum l.
Proof.
    induction l.
    -   rewrite list_image_end.
        rewrite list_sum_end.
        rewrite neg_zero.
        reflexivity.
    -   rewrite list_image_add.
        do 2 rewrite list_sum_add.
        rewrite neg_plus.
        rewrite IHl.
        reflexivity.
Qed.

Theorem list_sum_minus : ∀ al bl,
    list_sum (al + (list_image neg bl)) = list_sum al - list_sum bl.
Proof.
    intros al bl.
    rewrite list_sum_conc.
    rewrite list_sum_neg.
    reflexivity.
Qed.

Theorem list_sum_lmult : ∀ a l,
    a * list_sum l = list_sum (list_image (λ x, a * x) l).
Proof.
    intros a l.
    induction l as [|b l].
    -   rewrite list_image_end, list_sum_end.
        apply mult_ranni.
    -   rewrite list_image_add.
        do 2 rewrite list_sum_add.
        rewrite ldist.
        apply lplus.
        exact IHl.
Qed.

Theorem list_sum_rmult : ∀ a l,
    list_sum l * a = list_sum (list_image (λ x, x * a) l).
Proof.
    intros a l.
    induction l as [|b l].
    -   rewrite list_image_end, list_sum_end.
        apply mult_lanni.
    -   rewrite list_image_add.
        do 2 rewrite list_sum_add.
        rewrite rdist.
        apply lplus.
        exact IHl.
Qed.

Theorem list_prod_end : list_prod [] = 1.
Proof.
    reflexivity.
Qed.

Theorem list_prod_add : ∀ x a, list_prod (x ꞉ a) = x * list_prod a.
Proof.
    reflexivity.
Qed.

Theorem list_prod_single : ∀ x, list_prod [x] = x.
Proof.
    intros x.
    rewrite list_prod_add, list_prod_end.
    apply mult_rid.
Qed.

Theorem list_prod_conc :
    ∀ l1 l2, list_prod (l1 + l2) = list_prod l1 * list_prod l2.
Proof.
    intros l1 l2.
    induction l1.
    -   rewrite list_conc_lid.
        rewrite list_prod_end.
        rewrite mult_lid.
        reflexivity.
    -   rewrite list_conc_add.
        do 2 rewrite list_prod_add.
        rewrite IHl1.
        apply mult_assoc.
Qed.

End Fold.

Section FoldHomo.

Context {U V} `{RingClass U, RingClass V}.
Context (f : U → V)
    `{@HomomorphismZero _ _ _ _ f, @HomomorphismPlus _ _ _ _ f}
    `{@HomomorphismOne _ _ _ _ f, @HomomorphismMult _ _ _ _ f}.

Theorem list_sum_homo : ∀ l, f (list_sum l) = list_sum (list_image f l).
Proof.
    intros l.
    induction l as [|a l IHl].
    -   rewrite list_image_end.
        do 2 rewrite list_sum_end.
        apply homo_zero.
    -   rewrite list_image_add.
        do 2 rewrite list_sum_add.
        rewrite <- IHl.
        apply homo_plus.
Qed.

Theorem list_prod_homo : ∀ l, f (list_prod l) = list_prod (list_image f l).
Proof.
    intros l.
    induction l as [|a l IHl].
    -   rewrite list_image_end.
        do 2 rewrite list_prod_end.
        apply homo_one.
    -   rewrite list_image_add.
        do 2 rewrite list_prod_add.
        rewrite <- IHl.
        apply homo_mult.
Qed.

End FoldHomo.
