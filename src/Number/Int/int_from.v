Require Import init.

Require Import nat_abstract.

Require Export int_base.
Require Export int_plus.
Require Export int_mult.
Require Export int_order.
Require Export int_abstract.
Require Import set.
Require Import nat.
Require Import order_minmax.

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

Definition from_int := unary_op from_int_wd.

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

Theorem from_int_min : ∀ a b,
    from_int (min a b) = min (from_int a) (from_int b).
Proof.
    intros a b.
    destruct (connex a b) as [leq|leq].
    -   rewrite (min_leq _ _ leq).
        rewrite homo_le2 in leq.
        rewrite (min_leq _ _ leq).
        reflexivity.
    -   rewrite (min_req _ _ leq).
        rewrite homo_le2 in leq.
        rewrite (min_req _ _ leq).
        reflexivity.
Qed.

Theorem from_int_max : ∀ a b,
    from_int (max a b) = max (from_int a) (from_int b).
Proof.
    intros a b.
    destruct (connex a b) as [leq|leq].
    -   rewrite (max_req _ _ leq).
        rewrite homo_le2 in leq.
        rewrite (max_req _ _ leq).
        reflexivity.
    -   rewrite (max_leq _ _ leq).
        rewrite homo_le2 in leq.
        rewrite (max_leq _ _ leq).
        reflexivity.
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
