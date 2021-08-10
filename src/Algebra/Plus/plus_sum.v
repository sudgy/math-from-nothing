Require Import init.

Require Export plus_group.
Require Import nat0.
Require Import list.
Require Import set.

(* This will sum all of the terms in the range [m, m + n) *)
Fixpoint sum {U} `{Plus U, Zero U} (a : nat0 → U) (m n : nat0) :=
    match n with
    |   nat0_zero => zero
    |   nat0_suc n' => sum a m n' + a (m + n')
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
    nat0_induction n.
    -   intros all_eq.
        unfold zero; cbn.
        reflexivity.
    -   intros all_eq.
        cbn.
        rewrite IHn.
        rewrite all_eq.
        +   reflexivity.
        +   apply nat0_lt_suc.
        +   intros a a_ltq.
            rewrite all_eq.
            *   reflexivity.
            *   exact (trans a_ltq (nat0_lt_suc _)).
Qed.

Theorem sum_minus : ∀ f a b c, sum f a (b + c) - sum f a b = sum f (a + b) c.
    intros f a b c.
    nat0_induction c.
    -   rewrite plus_rid.
        rewrite plus_rinv.
        unfold zero at 2; cbn.
        reflexivity.
    -   rewrite nat0_plus_rsuc.
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

(* begin hide *)
End Sum.

Section Sum2.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ
}.
Context {V} `{
    VP : Plus V,
    VZ : Zero V,
    @PlusAssoc V VP,
    @PlusComm V VP,
    @PlusLid V VP VZ
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
(* begin hide *)
End Sum2.
(* end hide *)
