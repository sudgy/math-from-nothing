Require Import init.

Require Export op_group.
Require Export nat0.
Require Export int.

Fixpoint op_pow_nat0 {U} (op : U → U → U) `{Id U op} (a : U) (n : nat0) :=
    match n with
    | nat0_zero => id
    | nat0_suc n' => op a (op_pow_nat0 op a n')
    end.

Definition op_pow_int {U} (op : U→U→U) `{Id U op, Inv U op} (a : U) (n : int) :=
    match (connex 0 n) with
    | strong_or_left pos =>
        op_pow_nat0 op a (ex_val (int_pos_nat0_ex _ pos))
    | strong_or_right neg =>
        op_pow_nat0 op (inv a) (ex_val (int_neg_nat0_ex _ neg))
    end.

(* begin hide *)
Section OpPow.

Context {U} (op : U → U → U) `{
    Assoc U op,
    ID : Id U op,
    @Lid U op ID,
    @Rid U op ID,
    INV : Inv U op,
    @Linv U op ID INV,
    @Rinv U op ID INV
}.
Local Infix "·" := op.

Section OpPowNat0.
(* end hide *)

(* begin show *)
Local Notation "a ^ b" := (op_pow_nat0 op a b).
(* end show *)

Theorem op_pow_nat0_zero : ∀ a, a^0 = id.
    intros a.
    reflexivity.
Qed.

Theorem op_pow_nat0_one : ∀ a, a^1 = a.
    intros a.
    unfold one; cbn.
    apply rid.
Qed.

Theorem op_pow_nat0_mult : ∀ a m n, a^m · a^n = a^(m + n).
    intros a m n.
    nat0_induction m.
    -   rewrite op_pow_nat0_zero.
        rewrite plus_lid.
        apply lid.
    -   rewrite nat0_plus_lsuc.
        cbn.
        rewrite <- assoc.
        rewrite IHm.
        reflexivity.
Qed.

Theorem op_pow_nat0_pow : ∀ a m n, (a^m)^n = a^(m * n).
    intros a m n.
    nat0_induction n.
    -   rewrite mult_ranni.
        do 2 rewrite op_pow_nat0_zero.
        reflexivity.
    -   rewrite nat0_mult_rsuc.
        cbn.
        rewrite IHn.
        rewrite op_pow_nat0_mult.
        reflexivity.
Qed.

Theorem op_pow_nat0_comm_any : ∀ a b n, a · b = b · a → a · b^n = b^n · a.
    intros a b n com.
    nat0_induction n.
    -   rewrite op_pow_nat0_zero.
        rewrite lid, rid.
        reflexivity.
    -   cbn.
        rewrite assoc.
        rewrite com.
        rewrite <- assoc.
        rewrite IHn.
        apply assoc.
Qed.

Theorem op_pow_nat0_comm : ∀ a n, a · a^n = a^n · a.
    intros a n.
    apply op_pow_nat0_comm_any.
    reflexivity.
Qed.

Theorem op_pow_nat0_inv : ∀ a n, inv a^n = inv (a^n).
    intros a n.
    nat0_induction n.
    -   do 2 rewrite op_pow_nat0_zero.
        rewrite <- (lid (inv id)).
        rewrite rinv.
        reflexivity.
    -   cbn.
        rewrite IHn.
        rewrite <- (inv_op op).
        apply f_equal.
        symmetry.
        apply op_pow_nat0_comm.
Qed.

(* begin hide *)
End OpPowNat0.
(* end hide *)

(* begin show *)
Local Notation "a ^^ b" := (op_pow_nat0 op a b)
    (at level 30, right associativity).
Local Notation "a ^ b" := (op_pow_int op a b).
(* end show *)

Theorem op_pow_int_pos : ∀ a n, a^(nat0_to_int n) = a^^n.
    intros a n.
    unfold op_pow_int.
    destruct (connex 0 (nat0_to_int n)) as [n_pos|n_neg].
    -   rewrite_ex_val n' n'_eq.
        apply nat0_to_int_eq in n'_eq.
        rewrite n'_eq.
        reflexivity.
    -   rewrite_ex_val n' n'_eq.
        change 0 with (nat0_to_int 0) in n_neg.
        rewrite nat0_to_int_le in n_neg.
        pose proof (antisym n_neg (nat0_le_zero _)).
        subst n.
        change (nat0_to_int 0) with 0 in n'_eq.
        rewrite neg_zero in n'_eq.
        change 0 with (nat0_to_int 0) in n'_eq.
        apply nat0_to_int_eq in n'_eq.
        subst n'.
        do 2 rewrite op_pow_nat0_zero.
        reflexivity.
Qed.

Theorem op_pow_int_neg : ∀ a n, a^(-nat0_to_int n) = inv a^^n.
    intros a n.
    unfold op_pow_int.
    destruct (connex 0 (-nat0_to_int n)) as [n_neg|n_pos].
    -   rewrite_ex_val n' n'_eq.
        apply pos_neg in n_neg.
        rewrite neg_neg in n_neg.
        change 0 with (nat0_to_int 0) in n_neg.
        rewrite nat0_to_int_le in n_neg.
        pose proof (antisym n_neg (nat0_le_zero _)).
        subst n.
        change (nat0_to_int 0) with 0 in n'_eq.
        rewrite neg_zero in n'_eq.
        change 0 with (nat0_to_int 0) in n'_eq.
        apply nat0_to_int_eq in n'_eq.
        subst n'.
        do 2 rewrite op_pow_nat0_zero.
        reflexivity.
    -   rewrite_ex_val n' n'_eq.
        rewrite neg_neg in n'_eq.
        apply nat0_to_int_eq in n'_eq.
        rewrite n'_eq.
        reflexivity.
Qed.

Theorem op_pow_int_zero : ∀ a, a^0 = id.
    intros a.
    change 0 with (nat0_to_int 0).
    rewrite op_pow_int_pos.
    apply op_pow_nat0_zero.
Qed.

Theorem op_pow_int_one : ∀ a, a^1 = a.
    intros a.
    change 1 with (nat0_to_int 1).
    rewrite op_pow_int_pos.
    apply op_pow_nat0_one.
Qed.

Theorem op_pow_int_comm_any : ∀ a b n, a · b = b · a → a · b^n = b^n · a.
    intros a b n com.
    unfold op_pow_int.
    destruct (connex 0 n) as [n_pos|n_neg];
    rewrite_ex_val n' n'_eq.
    -   apply op_pow_nat0_comm_any.
        exact com.
    -   apply op_pow_nat0_comm_any.
        apply (rop op) with (inv b) in com.
        rewrite <- assoc, rinv, rid in com.
        apply (lop op) with (inv b) in com.
        rewrite assoc, assoc, linv, lid in com.
        symmetry.
        exact com.
Qed.

Theorem op_pow_int_comm : ∀ a n, a · a^n = a^n · a.
    intros a n.
    apply op_pow_int_comm_any.
    reflexivity.
Qed.

Theorem op_pow_int_inv : ∀ a n, inv a^n = inv (a^n).
    intros a n.
    unfold op_pow_int.
    destruct (connex 0 n) as [n_pos|n_neg];
    rewrite_ex_val n' n'_eq.
    -   apply op_pow_nat0_inv.
    -   apply op_pow_nat0_inv.
Qed.

Theorem op_pow_int_neg_inv : ∀ a n, a^(-n) = inv a^n.
    intros a n.
    unfold op_pow_int at 2.
    destruct (connex 0 n) as [n_pos|n_neg];
    rewrite_ex_val n' n'_eq.
    -   subst n.
        rewrite op_pow_int_neg.
        reflexivity.
    -   apply (f_equal neg) in n'_eq.
        rewrite neg_neg in n'_eq.
        subst n.
        rewrite neg_neg.
        rewrite (inv_inv op).
        rewrite op_pow_int_pos.
        reflexivity.
Qed.

Theorem op_pow_int_mult : ∀ a m n, a^m · a^n = a^(m + n).
    intros a m n.
    unfold op_pow_int.
    destruct (connex 0 m) as [m_pos|m_neg];
    destruct (connex 0 n) as [n_pos|n_neg];
    destruct (connex 0 (m + n)) as [mn_pos|mn_neg];
    rewrite_ex_val m' m'_eq;
    rewrite_ex_val n' n'_eq;
    rewrite_ex_val mn' mn'_eq.
    -   subst m n.
        rewrite nat0_to_int_plus in mn'_eq.
        apply nat0_to_int_eq in mn'_eq.
        rewrite <- mn'_eq.
        apply op_pow_nat0_mult.
    -   subst m n.
        rewrite nat0_to_int_plus in mn'_eq.
        rewrite <- op_pow_int_neg.
        rewrite <- mn'_eq.
        rewrite neg_neg.
        rewrite op_pow_int_pos.
        apply op_pow_nat0_mult.
    -   apply (f_equal neg) in n'_eq.
        rewrite neg_neg in n'_eq.
        subst m n.
        apply rplus with (nat0_to_int n') in mn'_eq.
        rewrite <- plus_assoc, plus_linv, plus_rid in mn'_eq.
        rewrite <- op_pow_int_pos.
        rewrite mn'_eq.
        rewrite nat0_to_int_plus.
        rewrite op_pow_int_pos.
        rewrite <- op_pow_nat0_mult.
        rewrite op_pow_nat0_inv.
        rewrite <- assoc, rinv, rid.
        reflexivity.
    -   apply (f_equal neg) in n'_eq.
        rewrite neg_neg in n'_eq.
        subst m n.
        rewrite neg_plus, neg_neg in mn'_eq.
        apply lplus with (nat0_to_int m') in mn'_eq.
        rewrite assoc, plus_rinv, plus_lid in mn'_eq.
        rewrite <- (op_pow_int_pos (inv a)).
        rewrite mn'_eq.
        rewrite nat0_to_int_plus.
        rewrite op_pow_int_pos.
        rewrite <- op_pow_nat0_mult.
        rewrite op_pow_nat0_inv.
        rewrite assoc, rinv, lid.
        reflexivity.
    -   apply (f_equal neg) in m'_eq.
        rewrite neg_neg in m'_eq.
        subst m n.
        apply lplus with (nat0_to_int m') in mn'_eq.
        rewrite plus_assoc, plus_rinv, plus_lid in mn'_eq.
        rewrite <- (op_pow_int_pos a).
        rewrite mn'_eq.
        rewrite nat0_to_int_plus.
        rewrite op_pow_int_pos.
        rewrite <- op_pow_nat0_mult.
        rewrite op_pow_nat0_inv.
        rewrite assoc, linv, lid.
        reflexivity.
    -   apply (f_equal neg) in m'_eq.
        rewrite neg_neg in m'_eq.
        subst m n.
        rewrite neg_plus, neg_neg in mn'_eq.
        apply rplus with (nat0_to_int n') in mn'_eq.
        rewrite <- assoc, plus_linv, plus_rid in mn'_eq.
        rewrite <- (op_pow_int_pos (inv a)).
        rewrite mn'_eq.
        rewrite nat0_to_int_plus.
        rewrite op_pow_int_pos.
        rewrite <- op_pow_nat0_mult.
        rewrite (op_pow_nat0_inv a n').
        rewrite <- assoc, linv, rid.
        reflexivity.
    -   apply (f_equal neg) in m'_eq.
        rewrite neg_neg in m'_eq.
        apply (f_equal neg) in n'_eq.
        rewrite neg_neg in n'_eq.
        subst m n.
        rewrite <- op_pow_int_neg.
        apply rplus with (nat0_to_int n') in mn'_eq.
        rewrite <- plus_assoc, plus_linv, plus_rid in mn'_eq.
        rewrite mn'_eq.
        rewrite nat0_to_int_plus.
        rewrite op_pow_int_pos.
        rewrite <- op_pow_nat0_mult.
        rewrite op_pow_nat0_inv.
        rewrite <- assoc, rinv, rid.
        reflexivity.
    -   apply (f_equal neg) in m'_eq.
        rewrite neg_neg in m'_eq.
        apply (f_equal neg) in n'_eq.
        rewrite neg_neg in n'_eq.
        subst m n.
        rewrite neg_plus, neg_neg, neg_neg in mn'_eq.
        rewrite nat0_to_int_plus in mn'_eq.
        apply nat0_to_int_eq in mn'_eq.
        rewrite <- mn'_eq.
        apply op_pow_nat0_mult.
Qed.

Theorem op_pow_int_pow1 :
        ∀ a m n, (a^m)^(nat0_to_int n) = a^(m * (nat0_to_int n)).
    intros a m n.
    unfold op_pow_int at 2.
    destruct (connex 0 m) as [m_pos|m_neg];
    rewrite_ex_val m' m'_eq.
    -   subst m.
        rewrite nat0_to_int_mult.
        do 2 rewrite op_pow_int_pos.
        apply op_pow_nat0_pow.
    -   apply (f_equal neg) in m'_eq.
        rewrite neg_neg in m'_eq.
        subst m.
        rewrite mult_lneg.
        rewrite op_pow_int_neg_inv.
        rewrite nat0_to_int_mult.
        do 2 rewrite op_pow_int_pos.
        apply op_pow_nat0_pow.
Qed.
Theorem op_pow_int_pow : ∀ a m n, (a^m)^n = a^(m * n).
    intros a m n.
    unfold op_pow_int at 1.
    destruct (connex 0 n) as [n_pos|n_neg];
    rewrite_ex_val n' n'_eq.
    -   subst n.
        rewrite <- op_pow_int_pos.
        apply op_pow_int_pow1.
    -   rewrite <- op_pow_int_pos.
        apply (f_equal neg) in n'_eq.
        rewrite neg_neg in n'_eq.
        subst n.
        rewrite mult_rneg.
        rewrite op_pow_int_neg_inv.
        rewrite <- op_pow_int_inv.
        apply op_pow_int_pow1.
Qed.

(* begin hide *)
End OpPow.
(* end hide *)
