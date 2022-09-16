Require Import init.

Require Import int_abstract.
Require Import fraction_base.

Require Export rat.
Require Import set.
Require Import fraction_order.

Section RatAbstract.

Context {U} `{
    OrderedField U,
    @CharacteristicZero U UP UZ UE
}.
Local Existing Instance characteristic_zero_not_trivial.

Definition rat_to_abstract_base (x : frac_base int)
    := int_to_abstract (fst x) / int_to_abstract [snd x|] : U.

Local Infix "~" := (eq_equal (frac_equiv int)).

Theorem int_to_abstract_nz : ∀ a : frac_base int, 0 ≠ int_to_abstract [snd a|].
Proof.
    intros a.
    intros contr.
    apply [|snd a].
    rewrite <- int_to_abstract_zero in contr.
    apply int_to_abstract_eq in contr.
    exact contr.
Qed.

Theorem rat_to_abstract_wd : ∀ a b, a ~ b →
    rat_to_abstract_base a = rat_to_abstract_base b.
Proof.
    intros a b eq.
    cbn in eq.
    unfold frac_eq in eq; cbn in eq.
    unfold rat_to_abstract_base; cbn.
    rewrite <- mult_rrmove by apply int_to_abstract_nz.
    rewrite (mult_comm (_ (fst b))).
    rewrite <- mult_assoc.
    rewrite <- mult_llmove by apply int_to_abstract_nz.
    do 2 rewrite <- int_to_abstract_mult.
    rewrite mult_comm.
    rewrite eq.
    reflexivity.
Qed.

Definition rat_to_abstract (a : rat) := unary_op rat_to_abstract_wd a.

Theorem rat_to_abstract_eq : ∀ a b,
    rat_to_abstract a = rat_to_abstract b → a = b.
Proof.
    intros a b eq.
    equiv_get_value a b.
    unfold rat_to_abstract in eq.
    equiv_simpl in eq.
    unfold rat; equiv_simpl.
    unfold frac_eq.
    unfold rat_to_abstract_base in eq.
    rewrite <- mult_rrmove in eq by apply int_to_abstract_nz.
    rewrite (mult_comm (_ (fst b))) in eq.
    rewrite <- mult_assoc in eq.
    rewrite <- mult_llmove in eq by apply int_to_abstract_nz.
    do 2 rewrite <- int_to_abstract_mult in eq.
    apply int_to_abstract_eq in eq.
    rewrite <- eq.
    apply mult_comm.
Qed.

Theorem rat_to_abstract_le : ∀ a b,
    rat_to_abstract a ≤ rat_to_abstract b ↔ a ≤ b.
Proof.
    intros a b.
    pose proof (frac_pos_ex int a) as [a1 [a2 [a2_pos a_eq]]].
    pose proof (frac_pos_ex int b) as [b1 [b2 [b2_pos b_eq]]].
    subst a b.
    unfold rat_to_abstract; equiv_simpl.
    pose proof (frac_le int a1 a2 b1 b2 a2_pos b2_pos) as stupid.
    rewrite stupid; clear stupid.
    unfold rat_to_abstract_base; cbn.
    rewrite <- int_to_abstract_lt in a2_pos, b2_pos.
    rewrite int_to_abstract_zero in a2_pos, b2_pos.
    rewrite <- le_mult_lrmove_pos by exact b2_pos.
    rewrite mult_comm, mult_assoc.
    rewrite <- le_mult_rrmove_pos by exact a2_pos.
    do 2 rewrite <- int_to_abstract_mult.
    rewrite int_to_abstract_le.
    rewrite mult_comm.
    rewrite (mult_comm b1).
    reflexivity.
Qed.

Theorem rat_to_abstract_lt : ∀ a b,
    rat_to_abstract a < rat_to_abstract b ↔ a < b.
Proof.
    intros a b.
    unfold strict.
    rewrite rat_to_abstract_le.
    rewrite (f_eq_iff rat_to_abstract_eq).
    reflexivity.
Qed.

Theorem rat_to_abstract_zero : rat_to_abstract 0 = 0.
Proof.
    unfold zero at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    rewrite int_to_abstract_zero.
    apply mult_lanni.
Qed.

Theorem rat_to_abstract_one : rat_to_abstract 1 = 1.
Proof.
    unfold one at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    rewrite int_to_abstract_one.
    rewrite div_one.
    apply mult_lid.
Qed.

Theorem rat_to_abstract_plus : ∀ a b,
    rat_to_abstract (a + b) = rat_to_abstract a + rat_to_abstract b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold plus at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    rewrite int_to_abstract_plus.
    do 3 rewrite int_to_abstract_mult.
    rewrite div_mult by apply int_to_abstract_nz.
    rewrite mult_assoc.
    do 2 rewrite rdist.
    rewrite mult_rrinv by apply int_to_abstract_nz.
    apply rplus.
    rewrite <- mult_assoc.
    rewrite (mult_comm (/ _ [snd a|])).
    rewrite mult_assoc.
    rewrite mult_rrinv by apply int_to_abstract_nz.
    reflexivity.
Qed.

Theorem rat_to_abstract_neg : ∀ a, rat_to_abstract (-a) = -rat_to_abstract a.
Proof.
    intros a.
    equiv_get_value a.
    unfold neg at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    rewrite int_to_abstract_neg.
    apply mult_lneg.
Qed.

Theorem rat_to_abstract_mult : ∀ a b,
    rat_to_abstract (a * b) = rat_to_abstract a * rat_to_abstract b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold mult at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    do 2 rewrite int_to_abstract_mult.
    do 2 rewrite <- mult_assoc.
    apply lmult.
    rewrite div_mult by apply int_to_abstract_nz.
    do 2 rewrite mult_assoc.
    apply rmult.
    apply mult_comm.
Qed.

Theorem rat_to_abstract_div : ∀ a, 0 ≠ a →
    rat_to_abstract (/a) = /rat_to_abstract a.
Proof.
    intros a a_nz.
    equiv_get_value a.
    unfold div at 1, rat_to_abstract; equiv_simpl.
    unfold zero in a_nz; cbn in a_nz.
    unfold to_frac, rat in a_nz; equiv_simpl in a_nz.
    unfold frac_eq in a_nz; cbn in a_nz.
    rewrite mult_rid, mult_lanni in a_nz.
    destruct (strong_excluded_middle (0 = fst a)) as [contr|a_nz'];
        [>contradiction|].
    unfold rat_to_abstract_base; cbn.
    rewrite div_mult.
    -   rewrite div_div by apply int_to_abstract_nz.
        apply mult_comm.
    -   intros contr.
        rewrite <- int_to_abstract_zero in contr.
        apply int_to_abstract_eq in contr.
        contradiction.
    -   apply div_nz.
        apply int_to_abstract_nz.
Qed.

Theorem int_to_rat_to_abstract : ∀ n,
    rat_to_abstract (int_to_rat n) = int_to_abstract n.
Proof.
    intros n.
    equiv_get_value n.
    unfold int_to_rat, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base, int_to_abstract_base; cbn.
    rewrite int_to_abstract_one.
    rewrite div_one, mult_rid.
    reflexivity.
Qed.

Theorem nat_to_rat_to_abstract : ∀ n,
    rat_to_abstract (nat_to_rat n) = from_nat n.
Proof.
    intros n.
    unfold nat_to_rat.
    rewrite int_to_rat_to_abstract.
    apply nat_to_int_to_abstract.
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
    pose proof (archimedean1 (a * n')) as [m' m'_ltq].
    assert (∃ m, a * n' < from_nat m) as S_ex
        by (exists m'; exact m'_ltq).
    pose proof (well_ordered _ S_ex) as [m [m_ltq m_least]].
    clear m' m'_ltq S_ex.
    remember (from_nat m) as m'.
    exists (nat_to_rat m / nat_to_rat (nat_suc n)).
    rewrite rat_to_abstract_mult.
    rewrite rat_to_abstract_div.
    2: {
        change 0 with (nat_to_rat 0).
        intros contr.
        apply nat_to_rat_eq in contr.
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
        rewrite from_nat_plus.
        rewrite from_nat_one.
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
        rewrite rat_to_abstract_zero.
        split; assumption.
    }
    rewrite nlt_le in b_neg.
    apply neg_pos in b_neg.
    apply lt_neg in ab.
    pose proof (rat_dense_in_arch_pos (-b) (-a) b_neg ab) as [r [r_gt r_lt]].
    exists (-r).
    rewrite rat_to_abstract_neg.
    apply lt_neg in r_gt, r_lt.
    rewrite neg_neg in r_gt, r_lt.
    split; assumption.
Qed.

End RatAbstractArch.
