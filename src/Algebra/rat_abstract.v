Require Import init.

Require Import fraction_base.

Require Export rat.
Require Import set.
Require Import nat.
Require Import int.
Require Import order_minmax.

Section RatAbstract.

Context {U} `{
    OrderedFieldClass U,
    @CharacteristicZero U UP UZ UE
}.
Local Existing Instance characteristic_zero_not_trivial.

Let F : Field := make_field U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Let from_int' : morphism int_domain (field_to_domain F)
    := make_domain_homomorphism int_domain _ from_int _ _ _ _.

Definition rat_to_abstract : morphism (ofield_to_field rat) F :=
    ofrac_frac_extend from_int'.

Global Instance nat_to_rat_le : HomomorphismLe rat_to_abstract.
Proof.
    unfold rat_to_abstract.
    pose (F' := make_ofield U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    pose (fi := make_odomain_homomorphism int (ofield_to_odomain F') from_int
        _ _ _ _ _).
    rewrite (ofrac_frac_eq fi).
    cbn.
    apply (ofrac_extend fi).
Qed.

Theorem nat_to_rat_to_abstract : ∀ n,
    rat_to_abstract (from_nat n) = from_nat n.
Proof.
    intros n.
    nat_induction n.
    -   do 2 rewrite homo_zero.
        symmetry; apply homo_zero.
    -   do 2 rewrite from_nat_suc.
        rewrite (homo_plus (f := rat_to_abstract)).
        rewrite IHn.
        rewrite homo_one.
        reflexivity.
Qed.

Theorem int_to_rat_to_abstract : ∀ n,
    rat_to_abstract (from_int n) = from_int n.
Proof.
    intros a.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply int_pos_nat_ex in a_pos as [n a_eq]; subst a.
        do 2 rewrite from_int_nat.
        apply nat_to_rat_to_abstract.
    -   apply int_neg_nat_ex in a_neg as [n a_eq]; subst a.
        do 2 rewrite homo_neg.
        rewrite (homo_neg (f := from_int)).
        apply f_equal.
        do 2 rewrite from_int_nat.
        apply nat_to_rat_to_abstract.
Qed.

End RatAbstract.

Section RatAbstractArch.

Context {U} `{
    UP : Plus U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    UZ : Zero U,
    @PlusLid U UP UZ,
    @PlusRid U UP UZ,
    UN : Neg U,
    @PlusLinv U UP UZ UN,
    @PlusRinv U UP UZ UN,
    UM : Mult U,
    @MultComm U UM,
    @MultAssoc U UM,
    @Ldist U UP UM,
    @Rdist U UP UM,
    UE : One U,
    @MultLid U UM UE,
    @MultRid U UM UE,
    @MultLcancel U UZ UM,
    @MultRcancel U UZ UM,
    UO : Order U,
    @Antisymmetric U le,
    @Transitive U le,
    @Connex U le,
    @OrderLplus U UP UO,
    @OrderRplus U UP UO,
    @OrderMult U UZ UM UO,
    @OrderLmult U UZ UM UO,
    @OrderRmult U UZ UM UO,
    @OrderMultLcancel U UZ UM UO,
    @OrderMultRcancel U UZ UM UO,
    NotTrivial U,
    UD : Div U,
    @MultLinv U UZ UM UE UD,
    @MultRinv U UZ UM UE UD,
    @Archimedean U UP UZ UO
}.

Lemma rat_dense_in_arch_pos : ∀ a b : U, 0 ≤ a → a < b →
    ∃ r : rat, a < rat_to_abstract r ∧ rat_to_abstract r < b.
Proof.
    intros a b a_pos ab.
    apply lt_plus_0_anb_b_a in ab.
    pose proof (archimedean2 _ ab) as [n ltq].
    apply lt_rmult_pos with (from_nat (nat_suc n)) in ltq.
    2: apply from_nat_pos.
    rewrite mult_linv in ltq by apply from_nat_pos.
    remember (from_nat (nat_suc n)) as n'.
    rewrite rdist in ltq.
    apply lt_plus_rrmove in ltq.
    rewrite mult_lneg in ltq.
    rewrite neg_neg in ltq.
    pose proof (archimedean1' (a * n')) as [m' m'_ltq].
    assert (∃ m, a * n' < from_nat m) as S_ex
        by (exists m'; exact m'_ltq).
    pose proof (well_ordered _ S_ex) as [m [m_ltq m_least]].
    clear m' m'_ltq S_ex.
    remember (from_nat m) as m'.
    exists (from_nat m / from_nat (nat_suc n)).
    rewrite homo_mult.
    rewrite homo_div.
    2: {
        rewrite <- (homo_zero (f := from_nat)).
        intros contr.
        apply inj in contr.
        inversion contr.
    }
    do 2 rewrite nat_to_rat_to_abstract.
    rewrite <- Heqn', <- Heqm'.
    split.
    -   apply lt_mult_lrmove_pos.
        1: rewrite Heqn'; apply from_nat_pos.
        exact m_ltq.
    -   apply lt_mult_rrmove_pos.
        1: rewrite Heqn'; apply from_nat_pos.
        nat_destruct m.
        {
            rewrite lt_plus_0_anb_b_a in ab.
            rewrite Heqm'.
            change (from_nat 0) with 0.
            apply lt_mult.
            -   exact (le_lt_trans a_pos ab).
            -   rewrite Heqn'.
                apply from_nat_pos.
        }
        assert (from_nat m ≤ a * n') as m_ltq2.
        {
            classic_contradiction contr.
            rewrite nle_lt in contr.
            specialize (m_least _ contr).
            rewrite <- nlt_le in m_least.
            contradiction (m_least (nat_lt_suc m)).
        }
        apply (le_lt_trans2 ltq).
        rewrite Heqm'.
        change (nat_suc m) with (1 + m).
        setoid_rewrite homo_plus.
        rewrite homo_one.
        apply le_lplus.
        exact m_ltq2.
Qed.
Theorem rat_dense_in_arch : ∀ a b : U, a < b →
    ∃ r : rat, a < rat_to_abstract r ∧ rat_to_abstract r < b.
Proof.
    intros a b ab.
    classic_case (0 ≤ a) as [a_pos|a_neg].
    {
        apply rat_dense_in_arch_pos; assumption.
    }
    rewrite nle_lt in a_neg.
    classic_case (0 < b) as [b_pos|b_neg].
    {
        exists 0.
        rewrite homo_zero.
        split; assumption.
    }
    rewrite nlt_le in b_neg.
    apply neg_pos in b_neg.
    apply lt_neg in ab.
    pose proof (rat_dense_in_arch_pos (-b) (-a) b_neg ab) as [r [r_gt r_lt]].
    exists (-r).
    rewrite homo_neg.
    apply lt_neg in r_gt, r_lt.
    rewrite neg_neg in r_gt, r_lt.
    split; assumption.
Qed.

End RatAbstractArch.
