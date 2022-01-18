Require Import init.

Require Export nat_base.
Require Export nat_plus.
Require Export nat_order.

Fixpoint nat_minus a b := match a, b with
    | a', nat_zero => opt_val a'
    | nat_zero, _ => opt_nil nat
    | nat_suc a', nat_suc b' => nat_minus a' b'
    end.

Infix "¯" := nat_minus (at level 50) : nat_scope.

Open Scope nat_scope.

Theorem nat_minus_eq : ∀ a, a ¯ a = opt_val 0.
    intros a.
    nat_induction a.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        exact IHa.
Qed.

Theorem nat_minus_zero : ∀ a, a ¯ 0 = opt_val a.
    intros a.
    nat_destruct a.
    -   apply nat_minus_eq.
    -   unfold zero; cbn.
        reflexivity.
Qed.

Theorem nat_minus_lt : ∀ a b, a < b → a ¯ b = opt_nil nat.
    intros a b ltq.
    apply nat_lt_ex in ltq as [c [c_nz eq]].
    subst b.
    nat_destruct c; [>contradiction|].
    clear c_nz.
    rewrite nat_plus_rsuc.
    nat_induction a.
    -   unfold zero at 1; cbn.
        reflexivity.
    -   cbn.
        rewrite nat_plus_lsuc.
        exact IHa.
Qed.

Theorem nat_minus_plus : ∀ a b, (a + b) ¯ a = opt_val b.
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
    intros a.
    nat_induction a.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        exact IHa.
Qed.

Theorem nat_abs_minus_lid : ∀ a, 0 ⊖ a = a.
    intros a.
    destruct a; reflexivity.
Qed.

Theorem nat_abs_minus_rid : ∀ a, a ⊖ 0 = a.
    intros a.
    destruct a; reflexivity.
Qed.

Theorem nat_abs_minus_comm : ∀ a b, a ⊖ b = b ⊖ a.
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
    intros a b.
    nat_induction a.
    -   rewrite plus_lid.
        apply nat_abs_minus_rid.
    -   rewrite nat_plus_lsuc.
        cbn.
        exact IHa.
Qed.

Close Scope nat_scope.
