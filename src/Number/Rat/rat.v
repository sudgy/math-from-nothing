Require Import init.

Require Import nat.
Require Import int.
Require Import set.

Require Export fraction_category.

Require Export nat_abstract.

Definition rat := ofrac int.

Definition rat_arch := ofrac_arch int.
Global Existing Instances rat_arch.

Theorem from_int_rat : ∀ n, from_int n = to_ofrac int n.
Proof.
    apply func_eq.
    symmetry.
    apply from_int_unique; apply (to_ofrac int).
Qed.

Section RatAbstract.

Context {U} `{
    OrderedFieldClass U,
    @CharacteristicZero U UP UZ UE
}.
Local Existing Instance characteristic_zero_not_trivial.

Let F : Field := make_field U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.

Definition from_rat : morphism (ofield_to_field rat) F :=
    ofrac_frac_extend (int_to_domain (field_to_domain F)).

Global Instance from_rat_le : HomomorphismLe from_rat.
Proof.
    unfold from_rat.
    pose (F' := make_ofield U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    pose proof (ofrac_frac_eq (int_to_odomain (ofield_to_odomain F'))) as eq.
    cbn in eq.
    rewrite (proof_irrelevance _ H1) in eq.
    rewrite eq; cbn.
    apply (ofrac_extend (int_to_odomain (ofield_to_odomain_base F'))).
Qed.

Theorem from_rat_nat : ∀ n, from_rat (from_nat n) = from_nat n.
Proof.
    intros n.
    nat_induction n.
    -   do 2 rewrite homo_zero.
        symmetry; apply homo_zero.
    -   do 2 rewrite from_nat_suc.
        rewrite (homo_plus (f := from_rat)).
        rewrite IHn.
        rewrite homo_one.
        reflexivity.
Qed.

Theorem from_rat_int : ∀ n, from_rat (from_int n) = from_int n.
Proof.
    apply func_eq.
    apply from_int_unique;
        apply ((⌈field_to_domain⌉ from_rat) ∘ (int_to_domain _)).
Qed.

End RatAbstract.

Definition rat_to_ofield (O : OrderedField) : morphism rat O
    := make_ofield_homomorphism rat O from_rat
        (field_homo_plus _ _ from_rat)
        (field_homo_mult _ _ from_rat)
        (field_homo_one _ _ from_rat)
        from_rat_le.

Theorem rat_initial : initial rat.
Proof.
    intros O.
    split.
    exists (rat_to_ofield O).
    intros f.
    assert (∀ n, f (from_int n) = from_int n) as f_eq.
    {
        apply func_eq.
        apply from_int_unique.
        1: apply homo_plus_compose.
        3: apply homo_one_compose.
        1: exact from_int_plus.
        2: exact from_int_one.
        all: apply f.
    }
    apply ofield_homo_eq.
    intros x.
    pose proof (to_ofrac_ex x) as [p [q [q_pos x_eq]]]; subst x.
    do 2 rewrite <- from_int_rat.
    cbn.
    rewrite homo_mult.
    rewrite (homo_mult (f := from_rat)).
    rewrite homo_div.
    2: apply (inj_zero from_int); apply q_pos.
    rewrite (homo_div (f := from_rat)).
    2: apply (inj_zero from_int); apply q_pos.
    do 2 rewrite f_eq.
    do 2 rewrite from_rat_int.
    reflexivity.
Qed.

Section RatAbstractArch.

Context {U} `{OrderedFieldClass U, @Archimedean U _ _ _}.

Lemma rat_dense_in_arch_pos : ∀ a b : U, 0 ≤ a → a < b →
    ∃ r : rat, a < from_rat r ∧ from_rat r < b.
Proof.
    intros a b a_pos ab.
    apply lt_plus_0_anb_b_a in ab.
    pose proof (archimedean2 _ ab) as [n ltq].
    apply lt_rmult_pos with (from_nat (nat_suc n)) in ltq.
    2: apply from_nat_pos.
    rewrite mult_linv in ltq by apply from_nat_pos.
    remember (from_nat (nat_suc n)) as n'.
    rewrite rdist in ltq.
    rewrite mult_lneg in ltq.
    rewrite <- lt_plus_lrmove in ltq.
    pose proof (archimedean1' (a * n')) as [m' m'_ltq].
    pose proof (well_ordered (λ m, a * n' < from_nat m) (ex_intro _ m' m'_ltq))
        as [m [m_ltq m_least]].
    clear m' m'_ltq.
    remember (from_nat m) as m'.
    exists (from_nat m / from_nat (nat_suc n)).
    rewrite homo_mult.
    rewrite homo_div by apply from_nat_pos.
    do 2 rewrite from_rat_nat.
    rewrite <- Heqn', <- Heqm'.
    split.
    -   apply lt_mult_lrmove_pos.
        +   rewrite Heqn'; apply from_nat_pos.
        +   exact m_ltq.
    -   apply lt_mult_rrmove_pos.
        1: rewrite Heqn'; apply from_nat_pos.
        nat_destruct m.
        +   rewrite lt_plus_0_anb_b_a in ab.
            rewrite Heqm'.
            rewrite homo_zero.
            apply lt_mult.
            *   exact (le_lt_trans a_pos ab).
            *   rewrite Heqn'.
                apply from_nat_pos.
        +   apply (le_lt_trans2 ltq).
            rewrite Heqm'.
            change (nat_suc m) with (1 + m).
            setoid_rewrite homo_plus.
            rewrite homo_one.
            apply le_lplus.
            classic_contradiction contr.
            rewrite nle_lt in contr.
            specialize (m_least _ contr).
            rewrite <- nlt_le in m_least.
            contradiction (m_least (nat_lt_suc m)).
Qed.
Theorem rat_dense_in_arch : ∀ a b : U, a < b →
    ∃ r : rat, a < from_rat r ∧ from_rat r < b.
Proof.
    intros a b ab.
    classic_case (0 ≤ a) as [a_pos|a_neg].
    1: exact (rat_dense_in_arch_pos a b a_pos ab).
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
    rewrite lt_half_lneg in r_gt.
    rewrite lt_half_rneg in r_lt.
    split; assumption.
Qed.

End RatAbstractArch.
