Require Import init.

Require Import nat_abstract.

Require Export int_base.
Require Export int_plus.
Require Export int_mult.
Require Export int_order.
Require Import set.
Require Import nat.
Require Import order_minmax.

Section IntAbstract.

Local Open Scope int_scope.

Context {U} `{
    OrderedFieldClass U,
    @CharacteristicZero U UP UZ UE
}.

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

Infix "×" := int_mult (at level 40, left associativity) : int_scope.
