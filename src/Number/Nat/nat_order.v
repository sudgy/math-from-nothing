Require Import init.

Require Export nat_base.
Require Import nat_plus.
Require Import nat_mult.

Require Export order_plus.
Require Export order_mult.
Require Export order_def.

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

Theorem nat_neg_eq : ∀ {a}, a <= 0 → 0 = a.
Proof.
    intros a eq.
    nat_destruct a; [>reflexivity|].
    contradiction eq.
Qed.
Lemma nat_pos : ∀ a, 0 <= a.
Proof.
    intros a.
    exact true.
Qed.
Theorem nat_pos2 : ∀ n, 0 < nat_suc n.
Proof.
    intros n.
    split; [>apply nat_pos|].
    intro contr.
    exact (nat_zero_suc contr).
Qed.
Lemma nat_neg : ∀ {n}, ¬(nat_suc n <= 0).
Proof.
    intros n contr.
    apply nat_neg_eq in contr.
    contradiction (nat_zero_suc contr).
Qed.
Lemma nat_neg2 : ∀ {a}, ¬(a < 0).
Proof.
    intros a [leq neq].
    apply nat_neg_eq in leq.
    symmetry in leq; contradiction.
Qed.

Theorem nat_one_pos : 0 < 1.
Proof.
    apply nat_pos2.
Qed.

Theorem nat_sucs_le : ∀ a b, nat_suc a <= nat_suc b ↔ a <= b.
Proof.
    intros a b.
    split; intro eq; exact eq.
Qed.
Theorem nat_sucs_lt : ∀ a b, nat_suc a < nat_suc b ↔ a < b.
Proof.
    intros a b.
    split.
    -   intros [leq neq].
        split; [>exact leq|].
        rewrite nat_suc_eq in neq.
        exact neq.
    -   intros [leq neq].
        split; [>exact leq|].
        rewrite nat_suc_eq.
        exact neq.
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
    -   exact (nat_neg_eq eq2).
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
    -   apply nat_neg_eq in eq2.
        rewrite <- eq2 in eq1.
        exact eq1.
    -   nat_destruct b.
        +   apply nat_neg_eq in eq1.
            rewrite <- eq1.
            apply nat_pos.
        +   nat_destruct a.
            *   apply nat_pos.
            *   rewrite nat_sucs_le in *.
                apply IHc with b; assumption.
Qed.

Theorem nat_le_suc : ∀ a, a <= nat_suc a.
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

Theorem nat_le_ex : ∀ {a b}, a <= b → ∃ c, a + c = b.
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

Theorem nat_lt_ex : ∀ {a b}, a < b → ∃ c, 0 ≠ c ∧ a + c = b.
Proof.
    intros a b [ab ab_neq].
    pose proof (nat_le_ex ab) as [c eq].
    exists c; split.
    -   intro contr.
        subst c.
        rewrite plus_rid in eq.
        contradiction.
    -   exact eq.
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

Theorem nat_le_lmult : ∀ {a b} c, a <= b → c * a <= c * b.
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

Theorem nat_le_rmult : ∀ {a b} c, a <= b → a * c <= b * c.
Proof.
    intros a b c.
    apply le_rmult_pos.
    apply nat_pos.
Qed.

Theorem nat_le_mult_lcancel : ∀ {a b} c, 0 ≠ c → c * a <= c * b → a <= b.
Proof.
    intros a b c c_neq eq.
    nat_destruct c; [>contradiction|]; clear c_neq.
    revert b eq.
    nat_induction a; intros b eq.
    -   apply nat_pos.
    -   nat_destruct b.
        +   exfalso.
            rewrite mult_ranni in eq.
            apply nat_neg_eq in eq.
            exact (nat_neq_suc_mult _ _ eq).
        +   rewrite nat_sucs_le.
            apply IHa; clear IHa.
            do 2 rewrite nat_mult_rsuc in eq.
            apply le_plus_lcancel in eq.
            exact eq.
Qed.

Global Instance nat_le_mult_lcancel_class : OrderMultLcancel nat.
Proof.
    split.
    intros a b c [C c_pos].
    apply nat_le_mult_lcancel.
    exact c_pos.
Qed.

Theorem nat_le_mult_rcancel : ∀ {a b} c, 0 ≠ c → a * c <= b * c → a <= b.
Proof.
    intros a b c c_pos.
    apply le_mult_rcancel_pos.
    split; [>apply nat_pos|exact c_pos].
Qed.

Theorem nat_lt_suc_le : ∀ {a b}, a < nat_suc b ↔ a <= b.
Proof.
    intros a b.
    split.
    -   revert b.
        nat_induction a; intros b eq.
        +   apply nat_pos.
        +   nat_destruct b.
            *   exfalso.
                unfold one in eq; cbn in eq.
                rewrite nat_sucs_lt in eq.
                exact (nat_neg2 eq).
            *   apply IHa.
                rewrite nat_sucs_lt in eq.
                exact eq.
    -   intro eq.
        split.
        +   apply (trans eq).
            apply nat_le_suc.
        +   intro contr.
            subst.
            rewrite <- nlt_le in eq.
            exact (eq (nat_lt_suc b)).
Qed.
Theorem nat_le_suc_lt : ∀ {a b}, nat_suc a <= b ↔ a < b.
Proof.
    intros a b.
    nat_destruct b.
    -   split; intros contr.
        +   contradiction (nat_neg contr).
        +   contradiction (nat_neg2 contr).
    -   rewrite nat_sucs_le.
        symmetry.
        apply nat_lt_suc_le.
Qed.

Theorem nat_le_self_lplus : ∀ a b, a <= b + a.
Proof.
    intros a b.
    rewrite <- le_plus_0_a_b_ab.
    apply nat_pos.
Qed.
Theorem nat_le_self_rplus : ∀ a b, a <= a + b.
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
    apply nat_neg_eq in n_lt.
    exact n_lt.
Qed.

Theorem nat_le_self_lmult : ∀ a b, 0 ≠ b → a <= b * a.
Proof.
    intros a b b_nz.
    nat_induction a.
    -   rewrite mult_ranni.
        apply refl.
    -   rewrite nat_mult_rsuc.
        assert (1 <= b) as b_gt.
        {
            rewrite <- nlt_le.
            intro eq.
            apply nat_lt_one_eq in eq.
            contradiction.
        }
        exact (le_lrplus b_gt IHa).
Qed.
Theorem nat_le_self_rmult : ∀ a b, 0 ≠ b → a <= a * b.
Proof.
    intros a b.
    rewrite mult_comm.
    apply nat_le_self_lmult.
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
            contradiction (nat_neg2 m_lt).
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

Global Instance nat_wo : WellFounded le.
Proof.
    apply well_ordered_founded.
    intros S [x Sx].
    classic_contradiction no_least.
    rewrite not_ex in no_least.
    unfold is_least in no_least.
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
