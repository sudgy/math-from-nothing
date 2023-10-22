Require Import init.

Require Import nat_abstract.

Require Export int_base.
Require Export int_plus.
Require Export int_mult.
Require Export int_order.
Require Export int_abstract.
Require Import set.
Require Import nat.
Require Import category_initterm.

Section IntAbstract.

Context {U} `{
    OrderedFieldClass U,
    @CharacteristicZero U UP UZ UE
}.

Definition from_int_base (x : nat * nat) : U
    := from_nat (fst x) - from_nat (snd x).

Local Open Scope int_scope.

Theorem from_int_wd : ∀ a b, a ~ b →
    from_int_base a = from_int_base b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    cbn in eq.
    unfold from_int_base; cbn.
    rewrite <- plus_rrmove.
    rewrite (plus_comm (_ b1)).
    rewrite <- plus_assoc.
    rewrite <- plus_llmove.
    do 2 rewrite <- homo_plus.
    rewrite plus_comm.
    rewrite eq.
    reflexivity.
Qed.

Definition from_int := unary_op from_int_wd : int → U.

Global Instance from_int_eq : Injective from_int.
Proof.
    split.
    intros a b eq.
    equiv_get_value a b.
    unfold from_int in eq.
    equiv_simpl in eq.
    equiv_simpl.
    unfold from_int_base in eq.
    rewrite plus_comm in eq.
    rewrite <- plus_lrmove in eq.
    rewrite <- plus_assoc in eq.
    rewrite <- plus_rlmove in eq.
    do 2 rewrite <- homo_plus in eq.
    apply inj in eq.
    rewrite eq.
    apply plus_comm.
Qed.

Theorem int_mult_rid : ∀ a, a × 1 = from_int a.
Proof.
    intros a.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold from_int, int_mult; equiv_simpl.
    unfold from_int_base, int_mult_base; cbn.
    do 2 rewrite nat_mult_rid.
    reflexivity.
Qed.

Global Instance from_int_one : HomomorphismOne from_int.
Proof.
    split.
    unfold one at 1, from_int; equiv_simpl.
    unfold from_int_base; cbn.
    setoid_rewrite homo_zero.
    setoid_rewrite homo_one.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Global Instance from_int_plus : HomomorphismPlus from_int.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold plus at 1, from_int; equiv_simpl.
    unfold from_int_base; cbn.
    setoid_rewrite homo_plus.
    rewrite neg_plus.
    apply plus_4.
Qed.

Global Instance from_int_mult : HomomorphismMult from_int.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold mult at 1, from_int; equiv_simpl.
    unfold from_int_base; cbn.
    setoid_rewrite homo_plus.
    setoid_rewrite homo_mult.
    rewrite ldist.
    do 2 rewrite rdist.
    do 2 rewrite mult_lneg.
    do 2 rewrite mult_rneg.
    rewrite neg_neg.
    rewrite neg_plus.
    do 2 rewrite (plus_comm (- (from_nat (fst a) * from_nat (snd b)))).
    rewrite plus_4.
    reflexivity.
Qed.

Theorem int_mult_from : ∀ a b, a × b = from_int a * b.
Proof.
    intros a b.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold from_int, int_mult; equiv_simpl.
    unfold int_mult_base, from_int_base; cbn.
    rewrite rdist.
    do 2 rewrite nat_mult_from.
    rewrite mult_lneg.
    reflexivity.
Qed.

Global Instance from_int_le : HomomorphismLe from_int.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold from_int, le at 1; equiv_simpl.
    unfold from_int_base; cbn.
    intros leq.
    rewrite <- le_plus_lrmove.
    rewrite plus_comm, plus_assoc.
    rewrite <- le_plus_rrmove.
    do 2 rewrite <- homo_plus.
    rewrite <- homo_le2.
    rewrite plus_comm.
    rewrite (plus_comm b1).
    exact leq.
Qed.

Theorem from_int_nat : ∀ n, from_int (from_nat n) = from_nat n.
Proof.
    intros n.
    rewrite from_nat_int.
    unfold from_int; equiv_simpl.
    unfold from_int_base; cbn.
    rewrite homo_zero.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem from_int_unique : ∀ f : int → U, HomomorphismPlus f → HomomorphismOne f
    → f = from_int.
Proof.
    intros f f_plus f_one.
    assert (∀ x, 0 ≤ x → f x = from_int x) as wlog.
    {
        intros x x_pos.
        apply int_pos_nat_ex in x_pos as [n x_eq]; subst x.
        nat_induction n.
        -   rewrite homo_zero.
            setoid_rewrite homo_zero.
            reflexivity.
        -   rewrite from_nat_suc.
            setoid_rewrite homo_plus.
            setoid_rewrite homo_one.
            rewrite IHn.
            reflexivity.
    }
    functional_intros x.
    destruct (connex 0 x) as [x_pos|x_neg].
    -   exact (wlog x x_pos).
    -   apply neg_eq.
        do 2 rewrite <- homo_neg.
        apply neg_pos in x_neg.
        exact (wlog _ x_neg).
Qed.

End IntAbstract.

Theorem from_int_eq_int : ∀ a, from_int a = a.
Proof.
    intros a.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold from_int; equiv_simpl.
    unfold from_int_base; cbn.
    do 2 rewrite from_nat_int.
    unfold plus, neg; equiv_simpl.
    rewrite plus_lid, plus_rid.
    reflexivity.
Qed.

Definition int_to_ring (R : Ring) : morphism int_ring R
    := make_ring_homomorphism
        int_ring R from_int from_int_plus from_int_mult from_int_one.
Definition int_to_cring (R : CRing) : morphism int_cring R
    := make_cring_homomorphism
        int_cring R from_int from_int_plus from_int_mult from_int_one.

Theorem ring_initial : initial int_ring.
Proof.
    intros R.
    split.
    exists (int_to_ring R).
    intros f.
    apply ring_homo_eq.
    apply func_eq.
    apply from_int_unique; apply f.
Qed.

Theorem cring_initial : initial int_cring.
Proof.
    intros R.
    split.
    exists (int_to_cring R).
    intros f.
    apply cring_homo_eq.
    apply func_eq.
    apply from_int_unique; apply f.
Qed.
