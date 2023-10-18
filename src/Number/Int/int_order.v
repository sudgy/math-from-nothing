Require Import init.

Require Export int_base.
Require Import int_plus.
Require Import int_mult.

Require Import nat.
Require Import set.
Require Export order_mult.
Require Import nat_abstract.

Definition int_suc a := a + 1.
Definition int_pre a := a + -(1).

Notation "a ≦ b" := (fst a + snd b ≤ snd a + fst b)
    (at level 70, no associativity) : int_scope.

(* begin hide *)
Open Scope int_scope.

Lemma int_le_wd_1 : ∀ a b c d, a ~ b → c ~ d → a ≦ c → b ≦ d.
Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd le.
    simpl in *.
    symmetry in ab.
    apply le_lplus with (a2 + b1) in le.
    apply le_lplus with (c1 + d2) in le.
    rewrite plus_comm in ab.
    rewrite ab in le at 2; clear ab.
    rewrite cd in le at 2; clear cd.
    plus_bring_left a1 in le; apply le_plus_lcancel in le.
    plus_bring_left a2 in le; apply le_plus_lcancel in le.
    plus_bring_left c1 in le; apply le_plus_lcancel in le.
    plus_bring_left c2 in le; apply le_plus_lcancel in le.
    rewrite (plus_comm b1 d2).
    rewrite (plus_comm b2 d1).
    exact le.
Qed.
Lemma int_le_wd : ∀ a b c d, a ~ b → c ~ d → (a ≦ c) = (b ≦ d).
Proof.
    intros a b c d ab cd.
    apply propositional_ext.
    split; apply int_le_wd_1; auto; try apply eq_symmetric; auto.
Qed.

Global Instance int_order : Order int := {
    le := binary_op int_le_wd;
}.

Lemma int_le_connex : ∀ a b, {a ≤ b} + {b ≤ a}.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold le; simpl; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2]; simpl.
    rewrite (plus_comm b1 a2).
    rewrite (plus_comm b2 a1).
    destruct (connex (a1 + b2) (a2 + b1)) as [eq|eq].
        left; exact eq.
        right; exact eq.
Qed.

Global Instance int_le_connex_class : Connex le := {
    connex := int_le_connex
}.

Lemma int_le_antisymmetric : ∀ a b, a ≤ b → b ≤ a → a = b.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold le; simpl; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2]; simpl.
    intros ab cd.
    rewrite (plus_comm a2 b1) in ab.
    rewrite (plus_comm b2 a1) in cd.
    apply antisym; auto.
Qed.

Global Instance int_le_antisym_class : Antisymmetric le := {
    antisym := int_le_antisymmetric
}.

Lemma int_le_transitive : ∀ a b c, a ≤ b → b ≤ c → a ≤ c.
Proof.
    intros a b c.
    equiv_get_value a b c.
    unfold le; simpl; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; simpl.
    intros ab bc.
    apply le_rplus with c2 in ab.
    apply le_lplus with a2 in bc.
    do 2 rewrite plus_assoc in bc.
    pose proof (trans ab bc) as eq; clear ab bc.
    plus_bring_left b2 in eq; apply le_plus_lcancel in eq.
    exact eq.
Qed.

Global Instance int_le_trans_class : Transitive le := {
    trans := int_le_transitive;
}.

Lemma int_le_lplus : ∀ a b c, a ≤ b → c + a ≤ c + b.
Proof.
    intros a b c.
    equiv_get_value a b c.
    unfold le, plus; simpl; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; simpl.
    intro eq.
    plus_bring_left c1; apply le_lplus.
    plus_bring_left c2; apply le_lplus.
    exact eq.
Qed.

Global Instance int_le_lplus_class : OrderLplus int := {
    le_lplus := int_le_lplus;
}.
(* end hide *)
Theorem int_pos_nat_ex : ∀ a, 0 ≤ a → ∃ n, a = from_nat n.
Proof.
    intros a.
    equiv_get_value a.
    unfold le, zero; equiv_simpl.
    destruct a as [a1 a2]; simpl.
    intro eq.
    do 2 rewrite plus_lid in eq.
    pose proof (nat_le_ex eq) as [c c_eq].
    exists c.
    rewrite from_nat_int.
    equiv_simpl; simpl.
    rewrite plus_rid.
    rewrite plus_comm.
    symmetry; exact c_eq.
Qed.

Theorem int_neg_nat_ex : ∀ a, a ≤ 0 → ∃ n, -a = from_nat n.
Proof.
    intros a a_neg.
    apply int_pos_nat_ex.
    apply neg_pos.
    exact a_neg.
Qed.

(* begin hide *)
Lemma int_le_mult : ∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ a * b.
Proof.
    intros a b a_pos b_pos.
    pose proof (int_pos_nat_ex a a_pos) as [m m_eq].
    pose proof (int_pos_nat_ex b b_pos) as [n n_eq].
    rewrite m_eq, n_eq.
    do 2 rewrite from_nat_int.
    unfold zero at 1, mult, le; equiv_simpl.
    rewrite mult_lanni, mult_ranni.
    do 2 rewrite plus_lid.
    apply nat_pos.
Qed.

Global Instance int_le_mult_class : OrderMult int := {
    le_mult := int_le_mult;
}.

Lemma int_le_mult_lcancel_pos : ∀ a b c, 0 < c → c * a ≤ c * b → a ≤ b.
Proof.
    intros a b c c_pos eq.
    classic_case (a ≤ b) as [C|contr]; auto.
    rewrite nle_lt in contr.
    apply lt_lmult_pos with c in contr; auto.
    destruct (le_lt_trans eq contr); contradiction.
Qed.

Global Instance int_le_mult_lcancel : OrderMultLcancel int := {
    le_mult_lcancel_pos := int_le_mult_lcancel_pos;
}.
(* end hide *)
Theorem nat_nz_int : ∀ n, (0 : int) ≠ from_nat (nat_suc n).
Proof.
    intros n n_eq.
    rewrite <- homo_zero in n_eq.
    apply from_nat_inj in n_eq.
    inversion n_eq.
Qed.

Theorem int_lt_suc : ∀ a, a < int_suc a.
Proof.
    intros a.
    unfold int_suc.
    rewrite <- (plus_rid a) at 1.
    apply lt_lplus.
    exact one_pos.
Qed.
Theorem int_le_suc : ∀ a, a ≤ int_suc a.
Proof.
    apply int_lt_suc.
Qed.
Theorem int_pre_lt : ∀ a, int_pre a < a.
Proof.
    intros a.
    unfold int_pre.
    rewrite <- (plus_rid a) at 2.
    apply lt_lplus.
    rewrite <- neg_zero.
    rewrite <- lt_neg.
    exact one_pos.
Qed.
Theorem int_pre_le : ∀ a, int_pre a ≤ a.
Proof.
    apply int_pre_lt.
Qed.
Theorem int_lt_suc_le : ∀ a b, a < int_suc b → a ≤ b.
Proof.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold strict, le, int_suc, plus, one; equiv_simpl.
    intros eq.
    rewrite plus_rid in eq.
    destruct eq as [leq neq].
    rewrite (plus_comm _ a2) in neq.
    assert (a1 + b2 < a2 + (b1 + 1)) as eq by (split; auto).
    change 1 with (nat_suc 0) in eq.
    do 2 rewrite nat_plus_rsuc in eq.
    rewrite nat_lt_suc_le in eq.
    rewrite plus_rid in eq.
    exact eq.
Qed.
Theorem int_le_lt_suc : ∀ a b, a ≤ b → a < int_suc b.
Proof.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold strict, le, int_suc, plus, one; equiv_simpl.
    intros eq.
    rewrite <- nat_lt_suc_le in eq.
    change 1 with (nat_suc 0).
    repeat rewrite nat_plus_rsuc.
    rewrite nat_plus_lsuc.
    do 2 rewrite plus_rid.
    rewrite (plus_comm b1).
    apply eq.
Qed.
Theorem int_pre_lt_le : ∀ a b, int_pre a < b → a ≤ b.
Proof.
    intros a b eq.
    apply int_lt_suc_le.
    unfold int_pre in eq.
    apply lt_rplus with 1 in eq.
    rewrite <- plus_assoc, plus_linv, plus_rid in eq.
    exact eq.
Qed.
Theorem int_le_pre_lt : ∀ a b, a ≤ b → int_pre a < b.
Proof.
    intros a b eq.
    apply int_le_lt_suc in eq.
    unfold int_pre.
    apply lt_plus_rrmove.
    exact eq.
Qed.

(* begin hide *)
Close Scope int_scope.
(* end hide *)
Theorem nat_to_int_pos : ∀ a, 0 ≤ from_nat a.
Proof.
    intros a.
    rewrite from_nat_int.
    unfold zero at 1, le; equiv_simpl.
    do 2 rewrite plus_lid.
    apply nat_pos.
Qed.

Theorem int_pos_nat1_ex : ∀ n, 0 < n → ∃ n', n = from_nat (nat_suc n').
Proof.
    intros n' n_pos.
    pose proof (int_pos_nat_ex _ (land n_pos)) as [n n_eq].
    subst n'.
    rewrite <- (homo_zero (f := from_nat)) in n_pos.
    pose proof (homo_lt2 (f := from_nat) 0 n) as stupid.
    apply stupid in n_pos.
    destruct n_pos as [C0 n_nz]; clear C0.
    nat_destruct n; try contradiction.
    clear n_nz.
    exists n.
    reflexivity.
Qed.

Theorem int_neg_nat1_ex : ∀ n, n < 0 → ∃ n', n = -from_nat (nat_suc n').
Proof.
    intros n n_lt.
    apply lt_neg in n_lt.
    rewrite neg_zero in n_lt.
    pose proof (int_pos_nat1_ex _ n_lt) as [n' n_eq].
    exists n'.
    apply (f_equal neg) in n_eq.
    rewrite neg_neg in n_eq.
    exact n_eq.
Qed.

Theorem nat1_to_int_pos : ∀ n, 0 < from_nat (nat_suc n).
Proof.
    intros n.
    split.
    -   apply nat_to_int_pos.
    -   apply nat_nz_int.
Qed.

Theorem nat1_to_int_pos1 : ∀ n, 1 ≤ from_nat (nat_suc n).
Proof.
    intros n.
    rewrite <- (homo_one (f := from_nat)).
    apply (homo_le2 (f := from_nat)).
    unfold one; cbn.
    rewrite nat_sucs_le.
    apply nat_pos.
Qed.

Global Program Instance int_archimedean : Archimedean int.
Next Obligation.
    rename H into x_pos, H0 into y_pos.
    pose proof (int_pos_nat1_ex _ x_pos) as [a x_eq].
    exists (nat_suc (nat_suc a)).
    change (nat_suc (nat_suc a) × y) with (y + nat_suc a × y).
    rewrite nat_mult_from.
    rewrite <- x_eq.
    clear x_eq a.
    pose proof (lt_rplus (x * y) y_pos) as ltq.
    rewrite plus_lid in ltq.
    apply (le_lt_trans2 ltq).
    rewrite <- (mult_rid x) at 1.
    apply le_lmult_pos; [>apply x_pos|].
    apply int_pre_lt_le.
    applys_eq y_pos.
    unfold int_pre.
    apply plus_rinv.
Qed.
