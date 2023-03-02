Require Import init.

Require Export list_base.
Require Import list_nat.
Require Import mult_ring.

Fixpoint rfold {U} (op : U → U → U) (init : U) (l : list U) :=
    match l with
    | [] => init
    | a :: l' => op a (rfold op init l')
    end.
Arguments rfold : simpl never.

Theorem rfold_end {U} (op : U → U → U) init : rfold op init [] = init.
Proof.
    reflexivity.
Qed.

Theorem rfold_add {U} (op : U → U → U) init : ∀ a l,
    rfold op init (a :: l) = op a (rfold op init l).
Proof.
    reflexivity.
Qed.

Fixpoint list_sum {U} `{Plus U, Zero U} (l : list U) :=
    match l with
    | list_end => zero
    | a :: l' => a + list_sum l'
    end.

Fixpoint list_prod {U} `{Mult U, One U} (l : list U) :=
    match l with
    | list_end => one
    | a :: l' => a * list_prod l'
    end.

Section Sum.

Context {U} `{AllPlus U}.

Theorem list_sum_plus :
    ∀ l1 l2, list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
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

Theorem list_sum_sum_eq : ∀ f n, list_sum (func_to_list f n) = sum f 0 n.
Proof.
    intros f n.
    nat_induction n.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        rewrite list_sum_plus.
        unfold func_to_list in IHn.
        rewrite IHn.
        cbn.
        rewrite plus_lid, plus_rid.
        reflexivity.
Qed.

Theorem list_sum_neg : ∀ l, -list_sum l = list_sum (list_image l neg).
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
    list_sum al - list_sum bl = list_sum (al ++ (list_image bl neg)).
Proof.
    intros al bl.
    rewrite list_sum_neg.
    rewrite list_sum_plus.
    reflexivity.
Qed.

(* begin hide *)
End Sum.

Section Sum2.

Context {U} `{AllPlus U}.
(* end hide *)

Lemma list_sum_func_single_zero : ∀ a n,
    list_sum (func_to_list (λ x, If x = n then a else 0) n) = 0.
Proof.
    intros a n.
    remember n as m.
    rewrite Heqm at 1.
    assert (m ≤ m) as leq by apply refl.
    rewrite Heqm in leq at 1.
    clear Heqm.
    nat_induction n.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        rewrite list_sum_plus.
        unfold func_to_list in IHn.
        rewrite IHn.
        +   cbn.
            rewrite plus_lid.
            rewrite plus_rid.
            case_if.
            2: reflexivity.
            subst.
            rewrite <- nlt_le in leq.
            exfalso; apply leq.
            apply nat_lt_suc.
        +   apply (trans (nat_le_suc n)).
            exact leq.
Qed.

Theorem list_sum_func_single : ∀ a m n, m < n →
    list_sum (func_to_list (λ x, If x = m then a else 0) n) = a.
Proof.
    intros a m n ltq.
    rewrite func_to_list2_eq.
    apply nat_lt_ex in ltq as [c n_eq].
    subst n.
    unfold func_to_list2.
    rewrite plus_comm.
    rewrite func_to_list2_base_conc.
    rewrite plus_lid.
    rewrite list_sum_plus.
    pose proof (list_sum_func_single_zero a m) as eq.
    rewrite func_to_list2_eq in eq.
    unfold func_to_list2 in eq.
    rewrite eq; clear eq.
    rewrite plus_lid.
    cbn.
    case_if.
    2: contradiction.
    apply plus_0_a_ba_b.
    clear e.
    remember (nat_suc m) as m'.
    assert (m < m') as ltq.
    {
        rewrite Heqm'.
        apply nat_lt_suc.
    }
    clear Heqm'.
    revert m' ltq.
    nat_induction c.
    -   unfold zero; cbn.
        reflexivity.
    -   intros.
        cbn.
        rewrite <- (IHc (nat_suc m')).
        +   rewrite plus_rid.
            case_if.
            *   subst.
                destruct ltq; contradiction.
            *   reflexivity.
        +   apply (trans ltq).
            apply nat_lt_suc.
Qed.
(* begin hide *)
End Sum2.
(* end hide *)

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
    -   rewrite list_conc_add.
        cbn.
        rewrite IHl1.
        apply mult_assoc.
Qed.
(* begin hide *)

End Product.
(* end hide *)
