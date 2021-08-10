Require Import init.
Require Export nat0_base.

Require Export plus_group.

Fixpoint nat0_plus_ a b :=
    match a with
        | nat0_zero => b
        | nat0_suc a' => nat0_plus_ a' (nat0_suc b)
    end.

(* begin hide *)
Instance nat0_plus : Plus nat0 := {
    plus := nat0_plus_;
}.
(* end hide *)
Theorem nat0_plus_lrsuc : ∀ a b, nat0_suc a + b = a + nat0_suc b.
    intros a b.
    unfold plus; cbn.
    reflexivity.
Qed.

Theorem nat0_plus_lsuc : ∀ a b, nat0_suc a + b = nat0_suc (a + b).
    induction a.
    -   intros b.
        unfold plus; cbn.
        reflexivity.
    -   intros b.
        rewrite nat0_plus_lrsuc.
        rewrite IHa.
        rewrite nat0_plus_lrsuc.
        reflexivity.
Qed.

Theorem nat0_plus_rsuc : ∀ a b, a + nat0_suc b = nat0_suc (a + b).
    intros a b.
    rewrite <- nat0_plus_lrsuc, nat0_plus_lsuc.
    reflexivity.
Qed.

(* begin hide *)
Instance nat0_zero_instance : Zero nat0 := {
    zero := nat0_zero;
}.
Ltac nat0_induction n := induction n; change nat0_zero with zero in *.
Ltac nat0_destruct n := destruct n; change nat0_zero with zero in *.

Lemma nat0_plus_lid_ : ∀ a, zero + a = a.
    intros a.
    reflexivity.
Qed.
Instance nat0_plus_lid : PlusLid nat0 := {
    plus_lid := nat0_plus_lid_;
}.
Lemma nat0_plus_rid_ : ∀ a, a + zero = a.
    nat0_induction a.
    -   reflexivity.
    -   rewrite nat0_plus_lsuc.
        rewrite IHa.
        reflexivity.
Qed.

Lemma nat0_plus_comm_ : ∀ a b, a + b = b + a.
    intros a b.
    nat0_induction a.
    -   rewrite plus_lid, nat0_plus_rid_.
        reflexivity.
    -   rewrite nat0_plus_lsuc, nat0_plus_rsuc.
        rewrite IHa.
        reflexivity.
Qed.

Instance nat0_plus_comm : PlusComm nat0 := {
    plus_comm := nat0_plus_comm_;
}.

Lemma nat0_plus_assoc_ : ∀ a b c, a + (b + c) = (a + b) + c.
    intros a b c.
    nat0_induction a.
    -   do 2 rewrite plus_lid.
        reflexivity.
    -   do 3 rewrite nat0_plus_lsuc.
        rewrite IHa.
        reflexivity.
Qed.
Instance nat0_plus_assoc : PlusAssoc nat0 := {
    plus_assoc := nat0_plus_assoc_;
}.

Lemma nat0_plus_lcancel_ : ∀ a b c, c + a = c + b → a = b.
    intros a b c eq.
    nat0_induction c.
    -   do 2 rewrite plus_lid in eq.
        exact eq.
    -   apply IHc; clear IHc.
        do 2 rewrite nat0_plus_lsuc in eq.
        inversion eq.
        reflexivity.
Qed.
Instance nat0_plus_lcancel : PlusLcancel nat0 := {
    plus_lcancel := nat0_plus_lcancel_;
}.
(* end hide *)
Theorem nat0_plus_zero : ∀ a b, 0 = a + b → 0 = a ∧ 0 = b.
    intros a b eq.
    nat0_destruct a.
    -   nat0_destruct b.
        +   split; reflexivity.
        +   rewrite nat0_plus_rsuc in eq.
            inversion eq.
    -   rewrite nat0_plus_lsuc in eq.
        inversion eq.
Qed.
