Require Import init.

Require Export nat_base.
Require Import nat_plus.
Require Import nat_mult.

Require Export order_plus.
Require Export order_mult.
Require Export order_pos.
Require Export order_bounds.
Require Export set_order.

Global Instance nat_order : Order nat := {
    le := fix le a b :=
        match a with
        | nat_suc a' =>
            match b with
            | nat_suc b' => le a' b'
            | nat_zero => False
            end
        | nat_zero => True
        end
}.

Definition nat_to_set_type n := set_type (initial_segment n).

Global Instance nat_pos : OrderPositive nat.
Proof.
    split.
    intros x.
    exact true.
Qed.

Theorem nat_pos2 : ∀ n, 0 < nat_suc n.
Proof.
    intros n.
    split; [>apply all_pos|].
    apply nat_zero_suc.
Qed.
Lemma nat_neg : ∀ {n}, ¬(nat_suc n ≤ 0).
Proof.
    intros n contr.
    contradiction (contr).
Qed.

Theorem nat_one_pos : 0 < 1.
Proof.
    apply nat_pos2.
Qed.

Theorem nat_sucs_le : ∀ a b, nat_suc a ≤ nat_suc b ↔ a ≤ b.
Proof.
    intros a b.
    split; intro eq; exact eq.
Qed.
Theorem nat_sucs_lt : ∀ a b, nat_suc a < nat_suc b ↔ a < b.
Proof.
    intros a b.
    unfold strict.
    rewrite nat_sucs_le.
    rewrite nat_suc_eq.
    reflexivity.
Qed.

Global Instance nat_le_connex : Connex le.
Proof.
    split.
    intros a.
    nat_induction a; intros b.
    -   left.
        apply nat_pos.
    -   nat_destruct b.
        +   right.
            apply nat_pos.
        +   apply or_to_strong.
            do 2 rewrite nat_sucs_le.
            apply or_from_strong.
            apply IHa.
Qed.

Global Instance nat_le_antisymmetric : Antisymmetric le.
Proof.
    split.
    intros a.
    nat_induction a; intros b eq1 eq2.
    -   nat_destruct b; [>reflexivity|].
        contradiction eq2.
    -   nat_destruct b.
        +   contradiction eq1.
        +   apply f_equal.
            rewrite nat_sucs_le in eq1, eq2.
            apply IHa; assumption.
Qed.

Global Instance nat_le_transitive : Transitive le.
Proof.
    split.
    intros a b c; revert a b.
    nat_induction c; intros a b eq1 eq2.
    -   apply all_neg_eq in eq2.
        rewrite <- eq2 in eq1.
        exact eq1.
    -   nat_destruct b.
        +   apply all_neg_eq in eq1.
            rewrite <- eq1.
            apply all_pos.
        +   nat_destruct a.
            *   apply all_pos.
            *   rewrite nat_sucs_le in *.
                apply IHc with b; assumption.
Qed.

Definition nat_lt_0_false (a : nat_to_set_type 0) := not_neg [|a].

Theorem nat_le_suc : ∀ a, a ≤ nat_suc a.
Proof.
    nat_induction a.
    -   apply nat_one_pos.
    -   rewrite nat_sucs_le.
        exact IHa.
Qed.
Theorem nat_lt_suc : ∀ a, a < nat_suc a.
Proof.
    nat_induction a.
    -   exact nat_one_pos.
    -   rewrite nat_sucs_lt.
        exact IHa.
Qed.

Theorem nat_le_ex : ∀ {a b}, a ≤ b → ∃ c, a + c = b.
Proof.
    nat_induction a; intros b ab.
    -   exists b.
        apply plus_lid.
    -   nat_destruct b.
        +   contradiction (nat_neg ab).
        +   rewrite nat_sucs_le in ab.
            specialize (IHa b ab) as [c IHa].
            exists c.
            rewrite nat_plus_lsuc.
            apply f_equal.
            exact IHa.
Qed.

Theorem nat_lt_ex : ∀ {a b}, a < b → ∃ c, a + nat_suc c = b.
Proof.
    intros a b [ab ab_neq].
    pose proof (nat_le_ex ab) as [c eq].
    nat_destruct c.
    -   rewrite plus_rid in eq.
        contradiction.
    -   exists c.
        exact eq.
Qed.

Global Instance nat_le_lplus : OrderLplus nat.
Proof.
    split.
    intros a b c ab.
    nat_induction c.
    -   do 2 rewrite plus_lid.
        exact ab.
    -   do 2 rewrite nat_plus_lsuc.
        rewrite nat_sucs_le.
        exact IHc.
Qed.

Global Instance nat_le_plus_lcancel : OrderPlusLcancel nat.
Proof.
    split.
    intros a b c eq.
    nat_induction c.
    -   do 2 rewrite plus_lid in eq.
        exact eq.
    -   apply IHc.
        do 2 rewrite nat_plus_lsuc in eq.
        rewrite nat_sucs_le in eq.
        exact eq.
Qed.

Global Instance nat_le_mult : OrderMult nat.
Proof.
    split.
    intros.
    apply nat_pos.
Qed.

Theorem nat_le_lmult : ∀ {a b} c, a ≤ b → c * a ≤ c * b.
Proof.
    intros a b c ab.
    nat_induction c.
    -   do 2 rewrite mult_lanni.
        apply refl.
    -   do 2 rewrite nat_mult_lsuc.
        exact (le_lrplus ab IHc).
Qed.

Global Instance nat_le_lmult_class : OrderLmult nat.
Proof.
    split.
    intros a b c c_pos.
    apply nat_le_lmult.
Qed.

Theorem nat_le_rmult : ∀ {a b} c, a ≤ b → a * c ≤ b * c.
Proof.
    intros a b c.
    apply le_rmult_pos.
    apply nat_pos.
Qed.

Theorem nat_le_mult_lcancel : ∀ {a b} c, 0 ≠ c → c * a ≤ c * b → a ≤ b.
Proof.
    intros a b c c_neq eq.
    nat_destruct c; [>contradiction|]; clear c_neq.
    revert b eq.
    nat_induction a; intros b eq.
    -   apply nat_pos.
    -   nat_destruct b.
        +   exfalso.
            rewrite mult_ranni in eq.
            apply all_neg_eq in eq.
            exact (nat_neq_suc_mult _ _ eq).
        +   rewrite nat_sucs_le.
            apply IHa; clear IHa.
            do 2 rewrite nat_mult_rsuc in eq.
            apply le_plus_lcancel in eq.
            exact eq.
Qed.

Theorem nat_le_mult_rcancel : ∀ {a b} c, 0 ≠ c → a * c ≤ b * c → a ≤ b.
Proof.
    intros a b c c_pos.
    do 2 rewrite (mult_comm _ c).
    apply le_mult_lcancel_pos.
    split; [>apply nat_pos|exact c_pos].
Qed.

Theorem nat_lt_suc_le : ∀ {a b}, a < nat_suc b ↔ a ≤ b.
Proof.
    intros a b.
    split.
    -   revert b.
        nat_induction a; intros b eq.
        +   apply nat_pos.
        +   rewrite nat_sucs_lt in eq.
            nat_destruct b.
            *   contradiction (not_neg eq).
            *   apply IHa.
                exact eq.
    -   intro eq.
        exact (le_lt_trans eq (nat_lt_suc b)).
Qed.
Theorem nat_le_suc_lt : ∀ {a b}, nat_suc a ≤ b ↔ a < b.
Proof.
    intros a b.
    nat_destruct b.
    -   split; intros contr.
        +   contradiction (nat_neg contr).
        +   contradiction (not_neg contr).
    -   rewrite nat_sucs_le.
        symmetry.
        apply nat_lt_suc_le.
Qed.

Theorem nat_le_self_lplus : ∀ a b, a ≤ b + a.
Proof.
    intros a b.
    rewrite <- le_plus_0_a_b_ab.
    apply nat_pos.
Qed.
Theorem nat_le_self_rplus : ∀ a b, a ≤ a + b.
Proof.
    intros a b.
    rewrite plus_comm.
    apply nat_le_self_lplus.
Qed.

Theorem nat_lt_one_eq : ∀ n, n < 1 → 0 = n.
Proof.
    intros n n_lt.
    unfold one in n_lt; cbn in n_lt.
    rewrite nat_lt_suc_le in n_lt.
    change nat_zero with (0 : nat) in n_lt.
    apply all_neg_eq in n_lt.
    exact n_lt.
Qed.

Theorem nat_le_self_lmult : ∀ a b, 0 ≠ b → a ≤ b * a.
Proof.
    intros a b b_nz.
    nat_induction a.
    -   rewrite mult_ranni.
        apply refl.
    -   rewrite nat_mult_rsuc.
        assert (1 ≤ b) as b_gt.
        {
            rewrite <- nlt_le.
            intro eq.
            apply nat_lt_one_eq in eq.
            contradiction.
        }
        exact (le_lrplus b_gt IHa).
Qed.
Theorem nat_le_self_rmult : ∀ a b, 0 ≠ b → a ≤ a * b.
Proof.
    intros a b.
    rewrite mult_comm.
    apply nat_le_self_lmult.
Qed.

Theorem nat_neq0_leq1 : ∀ {a}, 0 ≠ a → 1 ≤ a.
Proof.
    intros a a_neq.
    unfold one; cbn.
    rewrite nat_le_suc_lt.
    split.
    -   apply nat_pos.
    -   exact a_neq.
Qed.

Theorem strong_induction : ∀ S : nat → Prop,
    (∀ n, (∀ m, m < n → S m) → S n) → ∀ n, S n.
Proof.
    intros S ind n.
    pose (T n := ∀ m, m < n → S m).
    assert (∀ n', T n') as all_T.
    {
        nat_induction n'.
        -   unfold T.
            intros m m_lt.
            contradiction (not_neg m_lt).
        -   unfold T in *.
            intros m m_lt.
            apply ind.
            intros m' m'_eq.
            apply IHn'.
            rewrite nat_lt_suc_le in m_lt.
            exact (lt_le_trans m'_eq m_lt).
    }
    apply ind.
    apply all_T.
Qed.

Global Instance nat_wo : WellOrdered le.
Proof.
    split.
    intros S [x Sx].
    classic_contradiction no_least.
    rewrite not_ex in no_least.
    assert (∀ x, ¬S x) as none.
    {
        clear x Sx.
        intros x.
        induction x using strong_induction.
        intros Sx.
        specialize (no_least x).
        rewrite not_and_impl, not_all in no_least.
        specialize (no_least Sx) as [a a_eq].
        apply not_impl in a_eq as [Sa a_eq].
        rewrite nle_lt in a_eq.
        exact (H _ a_eq Sa).
    }
    exact (none _ Sx).
Qed.

Definition subsequence_seq (f : sequence nat) := ∀ n, f n < f (nat_suc n).
Definition subsequence {U} (a b : sequence U) :=
    ∃ f : sequence nat,
        subsequence_seq f ∧
        (∀ n, a (f n) = b n).

Theorem subsequence_seq_leq : ∀ f, subsequence_seq f → ∀ n, n ≤ f n.
Proof.
    intros f f_sub.
    unfold subsequence_seq in f_sub.
    intros n.
    nat_induction n.
    -   apply nat_pos.
    -   rewrite <- nat_lt_suc_le.
        rewrite nat_sucs_lt.
        exact (le_lt_trans IHn (f_sub n)).
Qed.
