Require Import init.

Require Export plus_group.
Require Import nat.
Require Import list.
Require Import set.

(* This will sum all of the terms in the range [m, m + n) *)
Fixpoint sum {U} `{Plus U, Zero U} (a : nat → U) (m n : nat) :=
    match n with
    |   nat_zero => zero
    |   nat_suc n' => sum a m n' + a (m + n')
    end.

Fixpoint list_sum {U} `{Plus U, Zero U} (l : list U) :=
    match l with
    | list_end => zero
    | a :: l' => a + list_sum l'
    end.

(* begin hide *)
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
Theorem sum_eq : ∀ f g m n, (∀ a, a < n → f (m + a) = g (m + a)) →
        sum f m n = sum g m n.
    intros f g m n all_eq.
    revert all_eq.
    nat_induction n.
    -   intros all_eq.
        unfold zero; cbn.
        reflexivity.
    -   intros all_eq.
        cbn.
        rewrite IHn.
        rewrite all_eq.
        +   reflexivity.
        +   apply nat_lt_suc.
        +   intros a a_ltq.
            rewrite all_eq.
            *   reflexivity.
            *   exact (trans a_ltq (nat_lt_suc _)).
Qed.

Theorem sum_minus : ∀ f a b c, sum f a (b + c) - sum f a b = sum f (a + b) c.
    intros f a b c.
    nat_induction c.
    -   rewrite plus_rid.
        rewrite plus_rinv.
        unfold zero at 2; cbn.
        reflexivity.
    -   rewrite nat_plus_rsuc.
        cbn.
        rewrite <- plus_assoc.
        rewrite (plus_comm (f (a + (b + c)))).
        rewrite plus_assoc.
        rewrite IHc.
        rewrite plus_assoc.
        reflexivity.
Qed.

Theorem list_sum_plus :
        ∀ l1 l2, list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
    intros l1 l2.
    induction l1.
    -   cbn.
        rewrite plus_lid.
        reflexivity.
    -   cbn.
        rewrite IHl1.
        apply plus_assoc.
Qed.

Theorem list_sum_perm : ∀ l1 l2, list_permutation l1 l2 →
        list_sum l1 = list_sum l2.
    intros l1 l2 perm.
    induction perm.
    -   reflexivity.
    -   cbn.
        rewrite IHperm.
        reflexivity.
    -   cbn.
        do 2 rewrite plus_assoc.
        rewrite (plus_comm y x).
        reflexivity.
    -   rewrite IHperm1, IHperm2.
        reflexivity.
Qed.

(* begin hide *)
End Sum.

Section Sum2.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN
}.
Context {V} `{
    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusAssoc V VP,
    @PlusComm V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN
}.
(* end hide *)
Theorem list_prod2_lconc (op : U → U → V) : ∀ (l1 l2 : list U) a,
        list_sum (list_prod2 op (a :: l1) l2) =
        list_sum (list_prod2 op l1 l2) + list_sum (list_image l2 (λ x, op a x)).
    intros l1 l2 a.
    induction l2.
    -   cbn.
        rewrite plus_lid.
        reflexivity.
    -   cbn.
        do 2 rewrite list_sum_plus.
        rewrite IHl2.
        plus_bring_left (op a a0).
        reflexivity.
Qed.

Theorem list_prod2_lconc' (op : U → U → V) : ∀ (l1 l2 : list U) a,
        list_sum (list_prod2 op (a :: l1) l2) =
        list_sum (list_prod2 op l1 l2) +
        list_sum (list_prod2 op (a :: list_end) l2).
    intros l1 l2 a.
    rewrite list_prod2_lconc.
    rewrite list_prod2_lconc.
    rewrite list_prod2_lend.
    cbn.
    rewrite plus_lid.
    reflexivity.
Qed.

Theorem list_prod2_rconc (op : U → U → V) : ∀ (l1 l2 : list U) a,
        list_sum (list_prod2 op l1 (a :: l2)) =
        list_sum (list_prod2 op l1 l2) + list_sum (list_image l1 (λ x, op x a)).
    intros l1 l2 a.
    cbn.
    rewrite list_sum_plus.
    rewrite plus_comm.
    apply lplus.
    induction l1.
    -   cbn.
        reflexivity.
    -   cbn.
        rewrite IHl1.
        reflexivity.
Qed.

Theorem list_prod2_rconc' (op : U → U → V) : ∀ (l1 l2 : list U) a,
        list_sum (list_prod2 op l1 (a :: l2)) =
        list_sum (list_prod2 op l1 l2) +
        list_sum (list_prod2 op l1 (a :: list_end)).
    intros l1 l2 a.
    rewrite list_prod2_rconc.
    rewrite list_prod2_rconc.
    rewrite list_prod2_rend.
    cbn.
    rewrite plus_lid.
    reflexivity.
Qed.

Lemma list_sum_func_single_zero : ∀ a n,
        list_sum (func_to_list (λ x, If x = n then a else 0) n) = 0.
    intros a n.
    remember n as m.
    rewrite Heqm at 1.
    assert (m <= m) as leq by apply refl.
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
    intros a m n ltq.
    rewrite func_to_list2_eq.
    apply nat_lt_ex in ltq as [c [c_nz n_eq]].
    subst n.
    nat_destruct c.
    1: contradiction.
    clear c_nz.
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
