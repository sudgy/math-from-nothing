Require Import init.

Require Export int_base.
Require Import int_plus.
Require Import int_mult.

Require Import nat.
Require Import set.
Require Export order_mult.

Definition int_suc a := a + 1.
Definition int_pre a := a + -(1).

Notation "a ≦ b" := (fst a + snd b <= snd a + fst b)
    (at level 70, no associativity) : int_scope.

(* begin hide *)
Open Scope int_scope.

Lemma int_le_wd_1 : ∀ a b c d, a ~ b → c ~ d → a ≦ c → b ≦ d.
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
    intros a b c d ab cd.
    apply propositional_ext.
    split; apply int_le_wd_1; auto; try apply eq_symmetric; auto.
Qed.

Global Instance int_order : Order int := {
    le := binary_op int_le_wd;
}.

Lemma int_le_connex : ∀ a b, {a <= b} + {b <= a}.
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

Lemma int_le_antisymmetric : ∀ a b, a <= b → b <= a → a = b.
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

Lemma int_le_transitive : ∀ a b c, a <= b → b <= c → a <= c.
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

Lemma int_le_lplus : ∀ a b c, a <= b → c + a <= c + b.
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
Theorem int_pos_nat_ex : ∀ a, 0 <= a → ∃ n, a = nat_to_int n.
    intros a.
    equiv_get_value a.
    unfold le, zero, nat_to_int; simpl. equiv_simpl; simpl.
    destruct a as [a1 a2]; simpl.
    intro eq.
    do 2 rewrite plus_lid in eq.
    pose proof (nat_le_ex a2 a1 eq) as [c c_eq].
    exists c.
    equiv_simpl; simpl.
    rewrite plus_rid.
    rewrite plus_comm.
    symmetry; exact c_eq.
Qed.

Theorem int_neg_nat_ex : ∀ a, a <= 0 → ∃ n, -a = nat_to_int n.
    intros a a_neg.
    apply int_pos_nat_ex.
    apply neg_pos.
    exact a_neg.
Qed.

(* begin hide *)
Lemma int_le_mult : ∀ a b, 0 <= a → 0 <= b → 0 <= a * b.
    intros a b a_pos b_pos.
    pose proof (int_pos_nat_ex a a_pos) as [m m_eq].
    pose proof (int_pos_nat_ex b b_pos) as [n n_eq].
    rewrite m_eq, n_eq.
    unfold zero at 1, nat_to_int, mult, le; simpl; equiv_simpl; simpl.
    rewrite mult_lanni, mult_ranni.
    do 2 rewrite plus_lid.
    apply nat_le_zero.
Qed.

Global Instance int_le_mult_class : OrderMult int := {
    le_mult := int_le_mult;
}.

Lemma int_le_mult_lcancel_pos : ∀ a b c, 0 < c → c * a <= c * b → a <= b.
    intros a b c c_pos eq.
    classic_case (a <= b) as [C|contr]; auto.
    rewrite nle_lt in contr.
    apply lt_lmult_pos with c in contr; auto.
    destruct (le_lt_trans eq contr); contradiction.
Qed.

Global Instance int_le_mult_lcancel : OrderMultLcancel int := {
    le_mult_lcancel_pos := int_le_mult_lcancel_pos;
}.
(* end hide *)
Theorem int_lt_suc : ∀ a, a < int_suc a.
    intros a.
    unfold int_suc.
    rewrite <- (plus_rid a) at 1.
    apply lt_lplus.
    exact one_pos.
Qed.
Theorem int_le_suc : ∀ a, a <= int_suc a.
    apply int_lt_suc.
Qed.
Theorem int_pre_lt : ∀ a, int_pre a < a.
    intros a.
    unfold int_pre.
    rewrite <- (plus_rid a) at 2.
    apply lt_lplus.
    rewrite <- neg_zero.
    rewrite <- lt_neg.
    exact one_pos.
Qed.
Theorem int_pre_le : ∀ a, int_pre a <= a.
    apply int_pre_lt.
Qed.
Theorem int_lt_suc_le : ∀ a b, a < int_suc b → a <= b.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold lt, strict, le, int_suc, plus, one; equiv_simpl.
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
Theorem int_le_lt_suc : ∀ a b, a <= b → a < int_suc b.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold lt, strict, le, int_suc, plus, one; equiv_simpl.
    intros eq.
    rewrite <- nat_lt_suc_le in eq.
    change 1 with (nat_suc 0).
    repeat rewrite nat_plus_rsuc.
    rewrite nat_plus_lsuc.
    do 2 rewrite plus_rid.
    rewrite (plus_comm b1).
    apply eq.
Qed.
Theorem int_pre_lt_le : ∀ a b, int_pre a < b → a <= b.
    intros a b eq.
    apply int_lt_suc_le.
    unfold int_pre in eq.
    apply lt_rplus with 1 in eq.
    rewrite <- plus_assoc, plus_linv, plus_rid in eq.
    exact eq.
Qed.
Theorem int_le_pre_lt : ∀ a b, a <= b → int_pre a < b.
    intros a b eq.
    apply int_le_lt_suc in eq.
    unfold int_pre.
    apply lt_plus_rrmove.
    exact eq.
Qed.

(* begin hide *)
Close Scope int_scope.
(* end hide *)
Theorem nat_to_int_pos : ∀ a, 0 <= nat_to_int a.
    intros a.
    unfold zero, nat_to_int, le; simpl; equiv_simpl; simpl.
    do 2 rewrite plus_lid.
    apply nat_le_zero.
Qed.

Theorem nat_to_int_ex : ∀ a, 0 <= a → ∃ n, nat_to_int n = a.
    intros a a_pos.
    equiv_get_value a.
    unfold zero, le in a_pos; simpl in a_pos; equiv_simpl in a_pos.
    destruct a as [a1 a2]; simpl in a_pos.
    do 2 rewrite plus_lid in a_pos.
    pose proof (nat_le_ex _ _ a_pos) as [c c_eq].
    exists c.
    unfold nat_to_int; equiv_simpl; simpl.
    rewrite plus_comm, plus_rid.
    exact c_eq.
Qed.

Theorem nat_to_int_le : ∀ a b, nat_to_int a <= nat_to_int b ↔ a <= b.
    intros a b.
    split.
    -   revert b.
        induction a.
        +   intros b eq.
            apply nat_le_zero.
        +   intros b eq.
            destruct b.
            *   change (nat_suc a) with (1 + a) in eq.
                change (nat_to_int 0) with 0 in eq.
                rewrite nat_to_int_plus in eq.
                change (nat_to_int 1) with 1 in eq.
                pose proof one_pos as pos1.
                pose proof (nat_to_int_pos a) as pos2.
                apply lt_rplus with (nat_to_int a) in pos1.
                rewrite plus_lid in pos1.
                pose proof (le_lt_trans pos2 pos1) as contr.
                rewrite <- nle_lt in contr.
                contradiction.
            *   apply IHa.
                change (nat_suc a) with (1 + a) in eq.
                change (nat_suc b) with (1 + b) in eq.
                do 2 rewrite nat_to_int_plus in eq.
                apply le_plus_lcancel in eq.
                exact eq.
    -   revert b.
        induction a.
        +   intros.
            apply nat_to_int_pos.
        +   intros b eq.
            destruct b.
            *   inversion eq.
            *   change (nat_suc a) with (1 + a).
                change (nat_suc b) with (1 + b).
                do 2 rewrite nat_to_int_plus.
                apply le_lplus.
                apply IHa.
                exact eq.
Qed.
Theorem nat_to_int_lt : ∀ a b, nat_to_int a < nat_to_int b ↔ a < b.
    intros a b.
    split.
    -   intros [leq neq].
        split.
        +   apply nat_to_int_le; auto.
        +   intro contr; rewrite contr in neq; contradiction.
    -   intros [leq neq].
        split.
        +   apply nat_to_int_le; auto.
        +   intros eq.
            apply nat_to_int_eq in eq.
            contradiction.
Qed.

Theorem int_pos_nat1_ex : ∀ n, 0 < n → ∃ n', n = nat_to_int (nat_suc n').
    intros n' n_pos.
    pose proof (int_pos_nat_ex _ (land n_pos)) as [n n_eq].
    subst n'.
    change 0 with (nat_to_int 0) in n_pos.
    apply nat_to_int_lt in n_pos.
    destruct n_pos as [C0 n_nz]; clear C0.
    nat_destruct n; try contradiction.
    clear n_nz.
    exists n.
    reflexivity.
Qed.

Theorem int_neg_nat1_ex : ∀ n, n < 0 → ∃ n', n = -nat_to_int (nat_suc n').
    intros n n_lt.
    apply lt_neg in n_lt.
    rewrite neg_zero in n_lt.
    pose proof (int_pos_nat1_ex _ n_lt) as [n' n_eq].
    exists n'.
    apply (f_equal neg) in n_eq.
    rewrite neg_neg in n_eq.
    exact n_eq.
Qed.

Theorem nat1_to_int_pos : ∀ n, 0 < nat_to_int (nat_suc n).
    intros n.
    split.
    -   apply nat_to_int_pos.
    -   apply nat_nz_int.
Qed.

Theorem nat1_to_int_pos1 : ∀ n, 1 <= nat_to_int (nat_suc n).
    intros n.
    change 1 with (nat_to_int 1).
    apply nat_to_int_le.
    unfold one; cbn.
    rewrite nat_sucs_le.
    apply nat_le_zero.
Qed.
