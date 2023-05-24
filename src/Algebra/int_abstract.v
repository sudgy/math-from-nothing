Require Import init.

Require Import nat_abstract.

Require Export int.
Require Import set.
Require Import nat.
Require Import order_minmax.

Section IntAbstract.

Context {U} `{
    OrderedFieldClass U,
    @CharacteristicZero U UP UZ UE
}.

Definition int_to_abstract_base (x : nat * nat)
    := from_nat (fst x) - from_nat (snd x).

Local Open Scope int_scope.

Theorem int_to_abstract_wd : ∀ a b, a ~ b →
    int_to_abstract_base a = int_to_abstract_base b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    cbn in eq.
    unfold int_to_abstract_base; cbn.
    rewrite <- plus_rrmove.
    rewrite (plus_comm (_ b1)).
    rewrite <- plus_assoc.
    rewrite <- plus_llmove.
    do 2 rewrite <- homo_plus.
    rewrite plus_comm.
    rewrite eq.
    reflexivity.
Qed.

Definition int_to_abstract := unary_op int_to_abstract_wd.

Theorem int_to_abstract_eq : ∀ a b,
    int_to_abstract a = int_to_abstract b → a = b.
Proof.
    intros a b eq.
    equiv_get_value a b.
    unfold int_to_abstract in eq.
    equiv_simpl in eq.
    equiv_simpl.
    unfold int_to_abstract_base in eq.
    rewrite plus_comm in eq.
    rewrite <- plus_lrmove in eq.
    rewrite <- plus_assoc in eq.
    rewrite <- plus_rlmove in eq.
    do 2 rewrite <- homo_plus in eq.
    apply inj in eq.
    rewrite eq.
    apply plus_comm.
Qed.

Theorem int_to_abstract_le : ∀ a b,
    int_to_abstract a ≤ int_to_abstract b ↔ a ≤ b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold int_to_abstract; equiv_simpl.
    unfold le at 2; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2]; cbn.
    unfold int_to_abstract_base; cbn.
    rewrite <- le_plus_lrmove.
    rewrite plus_comm, plus_assoc.
    rewrite <- le_plus_rrmove.
    do 2 rewrite <- homo_plus.
    rewrite <- homo_le2.
    rewrite plus_comm.
    rewrite (plus_comm b1).
    reflexivity.
Qed.

Theorem int_to_abstract_lt : ∀ a b,
    int_to_abstract a < int_to_abstract b ↔ a < b.
Proof.
    intros a b.
    unfold strict.
    rewrite int_to_abstract_le.
    rewrite (f_eq_iff int_to_abstract_eq).
    reflexivity.
Qed.

Theorem int_to_abstract_zero : int_to_abstract 0 = 0.
Proof.
    unfold zero at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    setoid_rewrite homo_zero.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem int_to_abstract_one : int_to_abstract 1 = 1.
Proof.
    unfold one at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    setoid_rewrite homo_zero.
    setoid_rewrite homo_one.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem int_to_abstract_plus : ∀ a b,
    int_to_abstract (a + b) = int_to_abstract a + int_to_abstract b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold plus at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    setoid_rewrite homo_plus.
    rewrite neg_plus.
    repeat rewrite plus_assoc.
    apply rplus.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    apply plus_comm.
Qed.

Theorem int_to_abstract_neg : ∀ a, int_to_abstract (-a) = -int_to_abstract a.
Proof.
    intros a.
    equiv_get_value a.
    unfold neg at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    rewrite plus_comm.
    rewrite neg_plus.
    rewrite neg_neg.
    reflexivity.
Qed.

Theorem int_to_abstract_mult : ∀ a b,
    int_to_abstract (a * b) = int_to_abstract a * int_to_abstract b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold mult at 1, int_to_abstract; equiv_simpl.
    unfold int_to_abstract_base; cbn.
    setoid_rewrite homo_plus.
    setoid_rewrite homo_mult.
    rewrite ldist.
    do 2 rewrite rdist.
    repeat rewrite <- plus_assoc.
    apply lplus.
    rewrite plus_comm.
    rewrite plus_assoc.
    do 2 rewrite mult_lneg.
    do 2 rewrite mult_rneg.
    rewrite neg_neg.
    apply rplus.
    rewrite plus_comm.
    rewrite neg_plus.
    reflexivity.
Qed.

Theorem nat_to_int_to_abstract : ∀ n,
    int_to_abstract (nat_to_int n) = from_nat n.
Proof.
    nat_induction n.
    -   unfold int_to_abstract, nat_to_int; equiv_simpl.
        unfold int_to_abstract_base; cbn.
        rewrite homo_zero.
        rewrite neg_zero.
        apply plus_lid.
    -   cbn.
        change (nat_suc n) with (1 + n).
        rewrite nat_to_int_plus.
        rewrite int_to_abstract_plus.
        rewrite IHn.
        rewrite int_to_abstract_one.
        reflexivity.
Qed.

Theorem int_to_abstract_min : ∀ a b,
    int_to_abstract (min a b) = min (int_to_abstract a) (int_to_abstract b).
Proof.
    intros a b.
    destruct (connex a b) as [leq|leq].
    -   rewrite (min_leq _ _ leq).
        rewrite <- int_to_abstract_le in leq.
        rewrite (min_leq _ _ leq).
        reflexivity.
    -   rewrite (min_req _ _ leq).
        rewrite <- int_to_abstract_le in leq.
        rewrite (min_req _ _ leq).
        reflexivity.
Qed.

Theorem int_to_abstract_max : ∀ a b,
    int_to_abstract (max a b) = max (int_to_abstract a) (int_to_abstract b).
Proof.
    intros a b.
    destruct (connex a b) as [leq|leq].
    -   rewrite (max_req _ _ leq).
        rewrite <- int_to_abstract_le in leq.
        rewrite (max_req _ _ leq).
        reflexivity.
    -   rewrite (max_leq _ _ leq).
        rewrite <- int_to_abstract_le in leq.
        rewrite (max_leq _ _ leq).
        reflexivity.
Qed.

Definition int_mult_base (a : nat * nat) (b : U) := fst a × b - snd a × b.

Theorem int_mult_wd : ∀ c a b, a ~ b → int_mult_base a c = int_mult_base b c.
Proof.
    intros c [a1 a2] [b1 b2] eq.
    cbn in eq.
    unfold int_mult_base; cbn.
    rewrite <- plus_rrmove.
    rewrite (nat_mult_commute_neg b1 _ c).
    rewrite <- plus_assoc.
    rewrite <- plus_llmove.
    do 2 rewrite <- nat_mult_rdist.
    rewrite plus_comm.
    rewrite eq.
    reflexivity.
Qed.

Definition int_mult a b := unary_op (int_mult_wd b) a.
Infix "×" := int_mult (at level 40, left associativity) : int_scope.
Arguments int_mult : simpl never.

Theorem int_mult_lanni : ∀ a, 0 × a = 0.
Proof.
    intros a.
    unfold int_mult, zero at 1; cbn.
    equiv_simpl.
    unfold int_mult_base; cbn.
    rewrite nat_mult_lanni.
    rewrite neg_zero.
    apply plus_lid.
Qed.

Theorem int_mult_ranni : ∀ a, a × 0 = 0.
Proof.
    intros a.
    equiv_get_value a.
    unfold int_mult; equiv_simpl.
    unfold int_mult_base.
    do 2 rewrite nat_mult_ranni.
    rewrite neg_zero.
    apply plus_lid.
Qed.

Theorem int_mult_lid : ∀ a, 1 × a = a.
Proof.
    intros a.
    unfold one, int_mult; equiv_simpl.
    unfold int_mult_base; cbn.
    rewrite nat_mult_lid, nat_mult_lanni.
    rewrite neg_zero.
    apply plus_rid.
Qed.

Theorem int_mult_ldist : ∀ a b c, a × (b + c) = a × b + a × c.
Proof.
    intros a b c.
    equiv_get_value a.
    unfold int_mult.
    equiv_simpl.
    unfold int_mult_base.
    destruct a as [a1 a2]; cbn.
    do 2 rewrite nat_mult_ldist.
    rewrite neg_plus.
    apply plus_4.
Qed.

Theorem int_mult_rdist : ∀ a b c, (a + b) × c = a × c + b × c.
Proof.
    intros a b c.
    equiv_get_value a b.
    unfold plus at 1, int_mult; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2].
    unfold int_mult_base; cbn.
    do 2 rewrite nat_mult_rdist.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    rewrite (nat_mult_commute a2).
    rewrite neg_plus_group.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply nat_mult_commute_neg.
Qed.

Theorem int_mult_mult : ∀ a b c, a × (b × c) = (a * b) × c.
Proof.
    intros a b c.
    equiv_get_value a b.
    unfold mult, int_mult; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2].
    unfold int_mult_base; cbn.
    do 2 rewrite nat_mult_rdist.
    assert (∀ a, nat_mult a (nat_mult b1 c - nat_mult b2 c)
        = nat_mult (a * b1) c - nat_mult (a * b2) c) as eq.
    {
        nat_induction a.
        -   do 2 rewrite mult_lanni.
            do 2 rewrite nat_mult_lanni.
            rewrite neg_zero, plus_lid.
            reflexivity.
        -   rewrite nat_mult_suc.
            rewrite IHa.
            do 2 rewrite nat_mult_lsuc.
            do 2 rewrite nat_mult_rdist.
            do 2 rewrite <- plus_assoc.
            apply lplus.
            rewrite (nat_mult_commute b2).
            rewrite neg_plus_group.
            do 2 rewrite plus_assoc.
            apply rplus.
            symmetry; apply nat_mult_commute_neg.
    }
    do 2 rewrite eq.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    rewrite (nat_mult_commute (a1 * b2)).
    do 2 rewrite neg_plus_group.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite neg_neg.
    symmetry; apply nat_mult_commute_neg.
Qed.

Theorem int_mult_assoc : ∀ a b c, a × (b * c) = (a × b) * c.
Proof.
    intros a b c.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold int_mult; equiv_simpl.
    unfold int_mult_base; cbn.
    rewrite rdist.
    do 2 rewrite nat_mult_assoc.
    rewrite mult_lneg.
    reflexivity.
Qed.

Theorem int_mult_lneg : ∀ a b, -(a × b) = (-a) × b.
Proof.
    intros a b.
    equiv_get_value a.
    unfold neg at 2, int_mult; equiv_simpl.
    destruct a as [a1 a2].
    unfold int_mult_base; cbn.
    rewrite neg_plus_group.
    rewrite neg_neg.
    reflexivity.
Qed.

Theorem int_mult_rneg : ∀ a b, -(a × b) = a × (-b).
Proof.
    intros a b.
    equiv_get_value a.
    unfold int_mult; equiv_simpl.
    destruct a as [a1 a2].
    unfold int_mult_base; cbn.
    rewrite nat_mult_commute_neg.
    rewrite neg_plus_group.
    do 2 rewrite nat_mult_rneg.
    reflexivity.
Qed.

Theorem int_mult_commute : ∀ a b c, a × c + b × c = b × c + a × c.
Proof.
    intros a b c.
    do 2 rewrite <- int_mult_rdist.
    rewrite plus_comm.
    reflexivity.
Qed.

Theorem int_mult_commute_neg : ∀ a b c, a × c - b × c = -(b × c) + a × c.
Proof.
    intros a b c.
    rewrite int_mult_lneg.
    apply int_mult_commute.
Qed.

End IntAbstract.
