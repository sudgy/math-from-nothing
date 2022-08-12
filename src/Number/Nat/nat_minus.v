Require Import init.

Require Export nat_base.
Require Export nat_plus.
Require Export nat_order.

Require Import order_minmax.

Fixpoint nat_minus a b := match a, b with
    | a', nat_zero => opt_val a'
    | nat_zero, _ => opt_nil nat
    | nat_suc a', nat_suc b' => nat_minus a' b'
    end.

(** This is \bar *)
Infix "¯" := nat_minus (at level 50) : nat_scope.

Open Scope nat_scope.

Theorem nat_minus_eq : ∀ a, a ¯ a = opt_val 0.
Proof.
    intros a.
    nat_induction a.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        exact IHa.
Qed.

Theorem nat_minus_zero : ∀ a, a ¯ 0 = opt_val a.
Proof.
    intros a.
    nat_destruct a.
    -   apply nat_minus_eq.
    -   unfold zero; cbn.
        reflexivity.
Qed.

Theorem nat_minus_lt : ∀ a b, a < b → a ¯ b = opt_nil nat.
Proof.
    intros a b ltq.
    apply nat_lt_ex in ltq as [c [c_nz eq]].
    subst b.
    nat_destruct c; [>contradiction|]; clear c_nz.
    rewrite nat_plus_rsuc.
    nat_induction a.
    -   unfold zero at 1; cbn.
        reflexivity.
    -   cbn.
        rewrite nat_plus_lsuc.
        exact IHa.
Qed.

Theorem nat_minus_plus : ∀ a b, (a + b) ¯ a = opt_val b.
Proof.
    intros a b.
    nat_induction a.
    -   rewrite plus_lid.
        apply nat_minus_zero.
    -   rewrite nat_plus_lsuc.
        cbn.
        exact IHa.
Qed.

Fixpoint nat_abs_minus a b := match a, b with
    | a', nat_zero => a'
    | nat_zero, b' => b'
    | nat_suc a', nat_suc b' => nat_abs_minus a' b'
    end.

Infix "⊖" := (nat_abs_minus) (at level 50) : nat_scope.

Theorem nat_abs_minus_eq : ∀ a, a ⊖ a = 0.
Proof.
    intros a.
    nat_induction a.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        exact IHa.
Qed.

Theorem nat_abs_minus_lid : ∀ a, 0 ⊖ a = a.
Proof.
    intros a.
    destruct a; reflexivity.
Qed.

Theorem nat_abs_minus_rid : ∀ a, a ⊖ 0 = a.
Proof.
    intros a.
    destruct a; reflexivity.
Qed.

Theorem nat_abs_minus_comm : ∀ a b, a ⊖ b = b ⊖ a.
Proof.
    intros a.
    nat_induction a; intros b.
    -   rewrite nat_abs_minus_lid, nat_abs_minus_rid.
        reflexivity.
    -   destruct b.
        +   cbn.
            reflexivity.
        +   cbn.
            apply IHa.
Qed.

Theorem nat_abs_minus_plus : ∀ a b, (a + b) ⊖ a = b.
Proof.
    intros a b.
    nat_induction a.
    -   rewrite plus_lid.
        apply nat_abs_minus_rid.
    -   rewrite nat_plus_lsuc.
        cbn.
        exact IHa.
Qed.

Theorem nat_abs_minus_min : ∀ a b, a ⊖ b + min a b = max a b.
Proof.
    intros a b.
    unfold min, max; case_if [leq|leq].
    -   apply nat_le_ex in leq as [c eq]; subst.
        rewrite nat_abs_minus_comm.
        rewrite nat_abs_minus_plus.
        apply plus_comm.
    -   rewrite nle_lt in leq.
        apply nat_lt_ex in leq as [c [c_nz eq]]; subst.
        rewrite nat_abs_minus_plus.
        apply plus_comm.
Qed.

Theorem nat_abs_minus_eq_zero : ∀ a b, 0 = a ⊖ b → a = b.
Proof.
    nat_induction a; intros b eq.
    -   rewrite nat_abs_minus_lid in eq.
        exact eq.
    -   nat_destruct b.
        +   rewrite nat_abs_minus_rid in eq.
            symmetry; exact eq.
        +   cbn in eq.
            rewrite (IHa b eq).
            reflexivity.
Qed.

Close Scope nat_scope.
