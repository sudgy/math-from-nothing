Require Import init.

Require Export mult_ring.
Require Export list.

Fixpoint list_prod {U} `{Mult U, One U} (l : list U) :=
    match l with
    | list_end => one
    | a :: l' => a * list_prod l'
    end.

(* begin hide *)
Section Product.

Context {U} `{AllMult U}.

(* end hide *)
Theorem list_prod_mult :
    ∀ l1 l2, list_prod (l1 ++ l2) = list_prod l1 * list_prod l2.
Proof.
    intros l1 l2.
    induction l1.
    -   cbn.
        symmetry; apply mult_lid.
    -   cbn.
        rewrite IHl1.
        apply mult_assoc.
Qed.

Theorem list_prod_perm : ∀ l1 l2, list_permutation l1 l2 →
    list_prod l1 = list_prod l2.
Proof.
    intros l1 l2 eq.
    induction eq.
    -   reflexivity.
    -   cbn.
        rewrite IHeq.
        reflexivity.
    -   cbn.
        do 2 rewrite mult_assoc.
        rewrite (mult_comm y x).
        reflexivity.
    -   rewrite IHeq1.
        exact IHeq2.
Qed.
(* begin hide *)

End Product.
(* end hide *)
