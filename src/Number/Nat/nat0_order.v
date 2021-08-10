Require Import init.

Require Export nat0_base.
Require Import nat0_plus.
Require Import nat0_mult.

Require Export order_plus.
Require Export order_mult.
Require Export order_def.

Fixpoint nat0_le a b :=
    match a with
    | nat0_suc a' =>
        match b with
        | nat0_suc b' => nat0_le a' b'
        | nat0_zero => False
        end
    | nat0_zero => True
    end.

(* begin hide *)
Instance nat0_order : Order nat0 := {
    le := nat0_le;
}.
(* end hide *)
Theorem nat0_le_zero_eq : ∀ a, a <= zero → a = zero.
    intros a eq.
    nat0_destruct a; try reflexivity.
    contradiction eq.
Qed.
Lemma nat0_le_zero : ∀ a, zero <= a.
    unfold zero, le; cbn.
    trivial.
Qed.
Lemma nat0_lt_zero : ∀ a, ¬(a < zero).
    intros a [leq neq].
    apply nat0_le_zero_eq in leq.
    contradiction.
Qed.

Theorem nat0_zero_lt_suc : ∀ n, 0 < nat0_suc n.
    intros n.
    split; try apply nat0_le_zero.
    intro contr; inversion contr.
Qed.

Theorem nat0_0_lt_1 : 0 < 1.
    split.
    -   apply nat0_le_zero.
    -   intro contr; inversion contr.
Qed.

Theorem nat0_sucs_le : ∀ a b, (nat0_suc a <= nat0_suc b) = (a <= b).
    intros a b.
    apply propositional_ext.
    split; intro eq; apply eq.
Qed.
Theorem nat0_sucs_lt : ∀ a b, (nat0_suc a < nat0_suc b) = (a < b).
    intros a b.
    apply propositional_ext.
    split.
    -   intros [eq neq].
        split; try assumption.
        intro.
        subst.
        contradiction.
    -   intros [eq neq].
        split; try assumption.
        intro eq2.
        inversion eq2.
        subst.
        contradiction.
Qed.

(* begin hide *)
Lemma nat0_le_connex_ : ∀ a b, {a <= b} + {b <= a}.
    nat0_induction a.
    -   intros.
        left.
        apply nat0_le_zero.
    -   intros b.
        nat0_destruct b.
        +   right.
            apply nat0_le_zero.
        +   destruct (IHa b) as [eq|eq]; clear IHa.
            *   left.
                rewrite nat0_sucs_le.
                exact eq.
            *   right.
                rewrite nat0_sucs_le.
                exact eq.
Qed.

Instance nat0_le_connex : @Connex nat0 le := {
    connex := nat0_le_connex_
}.

Lemma nat0_le_antisymmetric_ : ∀ a b, a <= b → b <= a → a = b.
    nat0_induction a.
    -   intros b eq1 eq2.
        apply nat0_le_zero_eq in eq2.
        symmetry; exact eq2.
    -   intros b eq1 eq2.
        nat0_destruct b.
        +   contradiction eq1.
        +   apply f_equal.
            rewrite nat0_sucs_le in eq1, eq2.
            apply IHa; assumption.
Qed.

Instance nat0_le_antisymmetric : @Antisymmetric nat0 le := {
    antisym := nat0_le_antisymmetric_
}.

Lemma nat0_le_transitive_ : ∀ a b c, a <= b → b <= c → a <= c.
    intros a b c; revert a b.
    nat0_induction c; intros a b eq1 eq2.
    -   apply nat0_le_zero_eq in eq2.
        rewrite eq2 in eq1.
        exact eq1.
    -   nat0_destruct b.
        +   apply nat0_le_zero_eq in eq1.
            rewrite eq1.
            apply nat0_le_zero.
        +   nat0_destruct a.
            *   apply nat0_le_zero.
            *   rewrite nat0_sucs_le in *.
                apply IHc with b; assumption.
Qed.

Instance nat0_le_transitive : @Transitive nat0 le := {
    trans := nat0_le_transitive_
}.
(* end hide *)
Theorem nat0_le_suc : ∀ a, a <= nat0_suc a.
    nat0_induction a.
    -   apply nat0_le_zero.
    -   rewrite nat0_sucs_le.
        exact IHa.
Qed.
Theorem nat0_lt_suc : ∀ a, a < nat0_suc a.
    split.
    -   apply nat0_le_suc.
    -   intro contr.
        nat0_induction a.
        +   inversion contr.
        +   inversion contr.
            exact (IHa H0).
Qed.

Theorem nat0_le_ex : ∀ a b, a <= b → ∃ c, a + c = b.
    nat0_induction a; intros b ab.
    -   exists b.
        apply plus_lid.
    -   nat0_destruct b.
        +   apply nat0_le_zero_eq in ab.
            inversion ab.
        +   rewrite nat0_sucs_le in ab.
            specialize (IHa b ab) as [c IHa].
            exists c.
            rewrite nat0_plus_lsuc.
            apply f_equal.
            exact IHa.
Qed.

Theorem nat0_lt_ex : ∀ a b, a < b → ∃ c, c ≠ zero ∧ a + c = b.
    intros a b [ab ab_neq].
    pose proof (nat0_le_ex a b ab) as [c eq].
    exists c; split.
    -   intro contr.
        subst c.
        rewrite plus_rid in eq.
        contradiction.
    -   exact eq.
Qed.

(* begin hide *)
Lemma nat0_le_lplus_ : ∀ a b c, a <= b → c + a <= c + b.
    intros a b c ab.
    nat0_induction c.
    -   do 2 rewrite plus_lid.
        exact ab.
    -   do 2 rewrite nat0_plus_lsuc.
        rewrite nat0_sucs_le.
        exact IHc.
Qed.

Instance nat0_le_lplus : OrderLplus nat0 := {
    le_lplus := nat0_le_lplus_;
}.

Lemma nat0_le_plus_lcancel_ : ∀ a b c, c + a <= c + b → a <= b.
    intros a b c eq.
    nat0_induction c.
    -   do 2 rewrite plus_lid in eq.
        exact eq.
    -   apply IHc.
        do 2 rewrite nat0_plus_lsuc in eq.
        rewrite nat0_sucs_le in eq.
        exact eq.
Qed.

Instance nat0_le_plus_lcancel : OrderPlusLcancel nat0 := {
    le_plus_lcancel := nat0_le_plus_lcancel_;
}.

Lemma nat0_le_mult_ : ∀ a b, zero <= a → zero <= b → zero <= a * b.
    intros a b C0 C1; clear C0 C1.
    apply nat0_le_zero.
Qed.

Instance nat0_le_mult : OrderMult nat0 := {
    le_mult := nat0_le_mult_;
}.
(* end hide *)
Theorem nat0_le_lmult : ∀ {a b} c, a <= b → c * a <= c * b.
    intros a b c ab.
    nat0_induction c.
    -   do 2 rewrite mult_lanni.
        apply refl.
    -   do 2 rewrite nat0_mult_lsuc.
        exact (le_lrplus ab IHc).
Qed.

(* begin hide *)
Lemma nat0_le_lmult_ : ∀ a b c, zero <= c → a <= b → c * a <= c * b.
    intros a b c c_pos.
    apply nat0_le_lmult.
Qed.

Instance nat0_le_lmult_class : OrderLmult nat0 := {
    le_lmult_pos := nat0_le_lmult_;
}.
(* end hide *)
Theorem nat0_le_rmult : ∀ {a b} c, a <= b → a * c <= b * c.
    intros a b c.
    apply le_rmult_pos.
    apply nat0_le_zero.
Qed.

Theorem nat0_le_mult_lcancel : ∀ {a b} c, zero ≠ c → c * a <= c * b → a <= b.
    intros a b c c_neq eq.
    nat0_destruct c; try contradiction; clear c_neq.
    revert b eq.
    nat0_induction a; intros b eq.
    -   apply nat0_le_zero.
    -   nat0_destruct b.
        +   exfalso.
            apply nat0_neq_suc_mult with c a.
            rewrite mult_ranni in eq.
            apply nat0_le_zero_eq in eq.
            symmetry; exact eq.
        +   rewrite nat0_sucs_le.
            apply IHa; clear IHa.
            do 2 rewrite nat0_mult_rsuc in eq.
            apply le_plus_lcancel in eq.
            exact eq.
Qed.

(* begin hide *)
Lemma nat0_le_mult_lcancel_ : ∀ a b c, zero < c → c * a <= c * b → a <= b.
    intros a b c [C c_pos].
    apply nat0_le_mult_lcancel.
    exact c_pos.
Qed.

Instance nat0_le_mult_lcancel_class : OrderMultLcancel nat0 := {
    le_mult_lcancel_pos := nat0_le_mult_lcancel_;
}.
(* end hide *)
Theorem nat0_le_mult_rcancel : ∀ {a b} c, zero ≠ c → a * c <= b * c → a <= b.
    intros a b c c_pos.
    apply le_mult_rcancel_pos.
    split; try assumption.
    apply nat0_le_zero.
Qed.

Theorem nat0_lt_suc_le : ∀ {a b}, (a < nat0_suc b) = (a <= b).
    intros a b.
    apply propositional_ext.
    split.
    -   revert b.
        nat0_induction a; intros b eq.
        +   apply nat0_le_zero.
        +   nat0_destruct b.
            *   exfalso.
                unfold one in eq; cbn in eq.
                rewrite nat0_sucs_lt in eq.
                apply nat0_lt_zero with a.
                exact eq.
            *   apply IHa.
                rewrite nat0_sucs_lt in eq.
                exact eq.
    -   intro eq.
        split.
        +   apply (trans eq).
            apply nat0_le_suc.
        +   intro contr.
            subst.
            rewrite <- nlt_le in eq.
            pose proof (nat0_lt_suc b).
            contradiction.
Qed.

Theorem nat0_le_self_lplus : ∀ a b, a <= b + a.
    intros a b.
    nat0_induction a.
    -   apply nat0_le_zero.
    -   rewrite nat0_plus_rsuc.
        rewrite nat0_sucs_le.
        exact IHa.
Qed.
Theorem nat0_le_self_rplus : ∀ a b, a <= a + b.
    intros a b.
    rewrite plus_comm.
    apply nat0_le_self_lplus.
Qed.
Theorem nat0_le_self_lmult : ∀ a b, 0 ≠ b → a <= b * a.
    intros a b b_nz.
    nat0_induction a.
    -   rewrite mult_ranni.
        apply refl.
    -   rewrite nat0_mult_rsuc.
        assert (1 <= b) as b_gt.
        {
            rewrite <- nlt_le.
            intro eq.
            unfold one in eq; cbn in eq.
            rewrite nat0_lt_suc_le in eq.
            apply nat0_le_zero_eq in eq.
            (* TODO: Make nat0_le_zero_eq symmetrized *)
            symmetry in eq; contradiction.
        }
        pose proof (le_lrplus b_gt IHa) as eq.
        exact eq.
Qed.
Theorem nat0_le_self_rmult : ∀ a b, 0 ≠ b → a <= a * b.
    intros a b.
    rewrite mult_comm.
    apply nat0_le_self_lmult; assumption.
Qed.

Theorem nat0_lt_1 : ∀ n, n < 1 → 0 = n.
    intros n n_lt.
    unfold one in n_lt; cbn in n_lt.
    rewrite nat0_lt_suc_le in n_lt.
    apply nat0_le_zero_eq in n_lt.
    symmetry; exact n_lt.
Qed.

Theorem strong_induction : ∀ S : nat0 → Prop,
        (∀ n, (∀ m, m < n → S m) → S n) → ∀ n, S n.
    intros S ind n.
    pose (T n := ∀ m, m < n → S m).
    assert (∀ n', T n') as all_T.
    {
        nat0_induction n'.
        -   unfold T.
            intros m m_lt.
            rewrite <- nle_lt in m_lt.
            pose proof (nat0_le_zero m).
            contradiction.
        -   unfold T in *.
            intros m m_lt.
            apply ind.
            intros m' m'_eq.
            apply IHn'.
            rewrite nat0_lt_suc_le in m_lt.
            exact (lt_le_trans m'_eq m_lt).
    }
    apply ind.
    apply all_T.
Qed.

Theorem nat0_wo : ∀ S : nat0 → Prop, (∃ x, S x) → has_least le S.
    intros S [x Sx].
    classic_contradiction no_least.
    unfold has_least in no_least.
    rewrite not_ex in no_least.
    unfold is_least in no_least.
    setoid_rewrite not_and in no_least.
    setoid_rewrite not_all in no_least.
    assert (∀ x, ¬S x) as none.
    {
        clear x Sx.
        intros x.
        induction x using strong_induction.
        intros Sx.
        specialize (no_least x) as [C0|[a a_eq]]; try contradiction.
        rewrite not_impl in a_eq.
        destruct a_eq as [Sa a_eq].
        rewrite nle_lt in a_eq.
        exact (H _ a_eq Sa).
    }
    exact (none _ Sx).
Qed.
(* begin hide *)
Lemma nat0_wf : ∀ S : nat0 → Prop, (∃ x, S x) → has_minimal le S.
    intros S S_ex.
    pose proof (nat0_wo S S_ex) as [x [Sx x_least]].
    exists x.
    split; try assumption.
    intros y Sy y_neq.
    rewrite nle_lt.
    rewrite neq_sym in y_neq.
    split; try assumption.
    apply x_least; exact Sy.
Qed.
Instance nat0_wf_class : WellFounded le := {
    well_founded := nat0_wf
}.
(* end hide *)
