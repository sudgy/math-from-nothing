Require Import init.

Require Export int_base.
Require Import int_plus.
Require Import int_mult.

Require Import nat.
Require Import set.
Require Export order_mult.
Require Import nat_abstract.

Notation "a ≦ b" := (fst a + snd b ≤ snd a + fst b)
    (at level 70, no associativity) : int_scope.

Open Scope int_scope.

Lemma int_le_wd_1 : ∀ a b c d, a ~ b → c ~ d → a ≦ c → b ≦ d.
Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd le.
    cbn in *.
    symmetry in ab.
    apply le_lplus with b2 in le.
    rewrite plus_assoc, (plus_comm b2) in le.
    rewrite <- ab in le.
    rewrite <- plus_assoc in le.
    do 2 rewrite (plus_3 _ a2) in le.
    apply le_plus_lcancel in le.
    apply le_rplus with d2 in le.
    rewrite <- (plus_assoc b2) in le.
    rewrite cd in le.
    rewrite <- plus_assoc in le.
    rewrite (plus_comm c2) in le.
    do 2 rewrite plus_assoc in le.
    apply le_plus_rcancel in le.
    exact le.
Qed.
Lemma int_le_wd : ∀ a b c d, a ~ b → c ~ d → (a ≦ c) = (b ≦ d).
Proof.
    intros a b c d ab cd.
    apply propositional_ext.
    split; apply int_le_wd_1.
    3, 4: apply eq_symmetric.
    all: assumption.
Qed.

Global Instance int_order : Order int := {
    le := binary_op int_le_wd;
}.

Global Instance int_le_connex_class : Connex le.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold le; equiv_simpl.
    rewrite (plus_comm b1 a2).
    rewrite (plus_comm b2 a1).
    apply connex.
Qed.


Global Instance int_le_antisym_class : Antisymmetric le.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold le; equiv_simpl.
    intros ab cd.
    rewrite (plus_comm a2 b1) in ab.
    rewrite (plus_comm b2 a1) in cd.
    exact (antisym ab cd).
Qed.


Global Instance int_le_trans_class : Transitive le.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold le; equiv_simpl.
    intros ab bc.
    apply le_rplus with c2 in ab.
    apply le_lplus with a2 in bc.
    do 2 rewrite <- plus_assoc in ab.
    pose proof (trans ab bc) as eq; clear ab bc.
    do 2 rewrite (plus_3 _ b2) in eq.
    apply le_plus_lcancel in eq.
    exact eq.
Qed.

Global Instance int_le_lplus_class : OrderLplus int.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold le, plus; equiv_simpl.
    intro eq.
    rewrite plus_4, (plus_4 c2).
    rewrite (plus_comm c1).
    apply le_lplus.
    exact eq.
Qed.

Theorem int_pos_nat_ex : ∀ a, 0 ≤ a → ∃ n, a = from_nat n.
Proof.
    intros a.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold le, zero; equiv_simpl.
    intro eq.
    do 2 rewrite plus_lid in eq.
    pose proof (nat_le_ex eq) as [c c_eq].
    exists c.
    rewrite from_nat_int.
    equiv_simpl.
    rewrite plus_rid.
    rewrite plus_comm.
    symmetry; exact c_eq.
Qed.

Theorem int_neg_nat_ex : ∀ a, a ≤ 0 → ∃ n, a = -from_nat n.
Proof.
    intros a a_neg.
    apply neg_pos in a_neg.
    apply int_pos_nat_ex in a_neg as [n n_eq].
    exists n.
    apply neg_eq.
    rewrite neg_neg.
    exact n_eq.
Qed.

Global Instance int_le_mult_class : OrderMult int.
Proof.
    split.
    intros a b a_pos b_pos.
    pose proof (int_pos_nat_ex a a_pos) as [m m_eq].
    pose proof (int_pos_nat_ex b b_pos) as [n n_eq].
    subst a b.
    do 2 rewrite from_nat_int.
    unfold zero at 1, mult, le; equiv_simpl.
    rewrite mult_lanni, mult_ranni.
    do 2 rewrite plus_lid.
    apply nat_pos.
Qed.

Global Instance int_le_mult_lcancel : OrderMultLcancel int.
Proof.
    split.
    intros a b c c_pos eq.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    apply lt_lmult_pos with c in contr; [>|exact c_pos].
    contradiction (irrefl _ (le_lt_trans eq contr)).
Qed.

Theorem nat_nz_int : ∀ n, (0 : int) ≠ from_nat (nat_suc n).
Proof.
    intros n n_eq.
    rewrite <- homo_zero in n_eq.
    apply from_nat_inj in n_eq.
    exact (nat_zero_suc n_eq).
Qed.

Theorem int_lt_nat : ∀ a b,
    to_equiv int_equiv a < to_equiv int_equiv b ↔ fst a + snd b < snd a + fst b.
Proof.
    intros a b.
    unfold strict, le at 1; equiv_simpl.
    rewrite (plus_comm (fst b)).
    reflexivity.
Qed.

Theorem int_lt_suc_le : ∀ a b, a < b + 1 ↔ a ≤ b.
Proof.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold plus, one, le at 2; equiv_simpl.
    rewrite plus_rid.
    rewrite int_lt_nat; cbn.
    rewrite (plus_comm _ 1).
    rewrite plus_3.
    rewrite nat_lt_suc_le.
    reflexivity.
Qed.
Theorem int_le_suc_lt : ∀ a b, a + 1 ≤ b ↔ a < b.
Proof.
    intros a b.
    rewrite <- int_lt_suc_le.
    split; intro eq.
    -   apply lt_plus_rcancel in eq; exact eq.
    -   apply lt_rplus; exact eq.
Qed.
Theorem int_le_pre_lt : ∀ a b, a ≤ b ↔ a - 1 < b.
Proof.
    intros a b.
    rewrite <- lt_plus_rrmove.
    symmetry; apply int_lt_suc_le.
Qed.
Theorem int_lt_pre_le : ∀ a b, a < b ↔ a ≤ b - 1.
Proof.
    intros a b.
    rewrite <- le_plus_lrmove.
    symmetry; apply int_le_suc_lt.
Qed.

Theorem int_pos_nat1_ex : ∀ n, 0 < n → ∃ n', n = from_nat (nat_suc n').
Proof.
    intros n' n_pos.
    pose proof (int_pos_nat_ex _ (land n_pos)) as [n n_eq].
    subst n'.
    nat_destruct n.
    -   setoid_rewrite homo_zero in n_pos.
        contradiction (irrefl _ n_pos).
    -   exists n.
        reflexivity.
Qed.

Theorem int_neg_nat1_ex : ∀ n, n < 0 → ∃ n', n = -from_nat (nat_suc n').
Proof.
    intros n n_lt.
    apply neg_pos2 in n_lt.
    pose proof (int_pos_nat1_ex _ n_lt) as [n' n_eq].
    exists n'.
    apply neg_eq.
    rewrite neg_neg.
    exact n_eq.
Qed.

Global Program Instance int_archimedean : Archimedean int.
Next Obligation.
    rename H into x_pos, H0 into y_pos.
    pose proof (int_pos_nat1_ex _ x_pos) as [a x_eq].
    exists (nat_suc (nat_suc a)).
    rewrite nat_mult_suc.
    rewrite nat_mult_from.
    rewrite <- x_eq.
    clear x_eq a.
    pose proof (lt_rplus (x * y) y_pos) as ltq.
    rewrite plus_lid in ltq.
    apply (le_lt_trans2 ltq).
    rewrite <- (mult_rid x) at 1.
    apply le_lmult_pos; [>apply x_pos|].
    rewrite int_le_pre_lt.
    rewrite plus_rinv.
    exact y_pos.
Qed.

Close Scope int_scope.
