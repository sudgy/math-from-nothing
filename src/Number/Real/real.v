Require Import init.

Require Export real_base.

Require Import fraction_base.

Require Import set.
Require Import nat.
Require Import int.
Require Import rat.

Definition real_pos := set_type (λ x, 0 < x).

Global Instance real_archimedean : Archimedean real.
Proof.
    apply field_impl_arch1.
    intros x x_pos.
    classic_contradiction contr.
    pose (S (a : real) := ∃ n, a < from_nat n).
    assert (∀ a, ¬(∃ n, a < from_nat n) → is_upper_bound le S a) as S_upper.
    {
        intros a a_ge b [n b_lt].
        apply (lt_le_trans b_lt).
        rewrite not_ex in a_ge.
        specialize (a_ge n).
        rewrite nlt_le in a_ge.
        exact a_ge.
    }
    pose proof (sup_complete S) as sup_ex.
    prove_parts sup_ex.
    {
        exists 0.
        exists 1.
        rewrite homo_one.
        apply one_pos.
    }
    {
        exists x.
        exact (S_upper _ contr).
    }
    destruct sup_ex as [m [m_upper m_least]].
    assert (S (m - 1)) as Sm1.
    {
        unfold S.
        classic_contradiction contr2.
        specialize (m_least _ (S_upper _ contr2)).
        contradiction (irrefl _ (le_lt_trans m_least (lt_minus_one _))).
    }
    assert (S (m + 1)) as Sm1'.
    {
        destruct Sm1 as [n n_lt].
        exists (n + 2).
        do 2 rewrite (homo_plus (f := from_nat)).
        rewrite (homo_one (f := from_nat)).
        rewrite plus_assoc.
        apply lt_rplus.
        rewrite lt_plus_rrmove.
        exact n_lt.
    }
    specialize (m_upper _ Sm1').
    contradiction (irrefl _ (le_lt_trans m_upper (lt_plus_one _))).
Qed.

Lemma real_n_div_pos : ∀ n, 0 < / from_nat (nat_suc n).
Proof.
    intros n.
    apply div_pos.
    apply from_nat_pos.
Qed.

Theorem real_nested_interval : ∀ a b : nat → real,
    (∀ n, a n ≤ b n) →
    (∀ n, closed_interval (a (1 + n)) (b (1 + n)) ⊆ closed_interval (a n) (b n))
    → ∃ x, ∀ n, closed_interval (a n) (b n) x.
Proof.
    intros a b ab sub.
    assert (∀ m n, m ≤ n →
        closed_interval (a n) (b n) ⊆ closed_interval (a m) (b m)) as sub'.
    {
        intros m n mn.
        apply nat_le_ex in mn as [c eq]; subst n.
        nat_induction c.
        1: rewrite plus_rid; apply refl.
        apply (trans2 IHc).
        rewrite nat_plus_rsuc.
        apply sub.
    }
    assert (∀ m n, a m ≤ b n) as ab_leq.
    {
        intros m n.
        destruct (connex m n) as [mn|mn].
        -   apply (sub' _ _ mn).
            split.
            +   apply ab.
            +   apply refl.
        -   apply (sub' _ _ mn).
            split.
            +   apply refl.
            +   apply ab.
    }
    pose (S := image a).
    pose proof (sup_complete S) as x_ex.
    prove_parts x_ex.
    {
        exists (a 0).
        exists 0.
        reflexivity.
    }
    {
        exists (b 0).
        intros x [n]; subst x.
        apply ab_leq.
    }
    destruct x_ex as [x [x_upper x_least]].
    exists x.
    intros n.
    split.
    -   apply x_upper.
        exists n.
        reflexivity.
    -   apply x_least.
        intros y [m]; subst y.
        apply ab_leq.
Qed.
