Require Import init.
Require Export nat_base.

Require Export plus_group.

Fixpoint nat_plus_ a b :=
    match a with
        | nat_zero => b
        | nat_suc a' => nat_plus_ a' (nat_suc b)
    end.

(* begin hide *)
Instance nat_plus : Plus nat := {
    plus := nat_plus_;
}.
(* end hide *)
Theorem nat_plus_lrsuc : ∀ a b, nat_suc a + b = a + nat_suc b.
    intros a b.
    unfold plus; cbn.
    reflexivity.
Qed.

Theorem nat_plus_lsuc : ∀ a b, nat_suc a + b = nat_suc (a + b).
    induction a.
    -   intros b.
        unfold plus; cbn.
        reflexivity.
    -   intros b.
        rewrite nat_plus_lrsuc.
        rewrite IHa.
        rewrite nat_plus_lrsuc.
        reflexivity.
Qed.

Theorem nat_plus_rsuc : ∀ a b, a + nat_suc b = nat_suc (a + b).
    intros a b.
    rewrite <- nat_plus_lrsuc, nat_plus_lsuc.
    reflexivity.
Qed.

(* begin hide *)
Instance nat_zero_instance : Zero nat := {
    zero := nat_zero;
}.
Ltac nat_induction n := induction n; change nat_zero with zero in *.
Ltac nat_destruct n := destruct n; change nat_zero with zero in *.

Lemma nat_plus_lid_ : ∀ a, zero + a = a.
    intros a.
    reflexivity.
Qed.
Instance nat_plus_lid : PlusLid nat := {
    plus_lid := nat_plus_lid_;
}.
Lemma nat_plus_rid_ : ∀ a, a + zero = a.
    nat_induction a.
    -   reflexivity.
    -   rewrite nat_plus_lsuc.
        rewrite IHa.
        reflexivity.
Qed.

Lemma nat_plus_comm_ : ∀ a b, a + b = b + a.
    intros a b.
    nat_induction a.
    -   rewrite plus_lid, nat_plus_rid_.
        reflexivity.
    -   rewrite nat_plus_lsuc, nat_plus_rsuc.
        rewrite IHa.
        reflexivity.
Qed.

Instance nat_plus_comm : PlusComm nat := {
    plus_comm := nat_plus_comm_;
}.

Lemma nat_plus_assoc_ : ∀ a b c, a + (b + c) = (a + b) + c.
    intros a b c.
    nat_induction a.
    -   do 2 rewrite plus_lid.
        reflexivity.
    -   do 3 rewrite nat_plus_lsuc.
        rewrite IHa.
        reflexivity.
Qed.
Instance nat_plus_assoc : PlusAssoc nat := {
    plus_assoc := nat_plus_assoc_;
}.

Lemma nat_plus_lcancel_ : ∀ a b c, c + a = c + b → a = b.
    intros a b c eq.
    nat_induction c.
    -   do 2 rewrite plus_lid in eq.
        exact eq.
    -   apply IHc; clear IHc.
        do 2 rewrite nat_plus_lsuc in eq.
        inversion eq.
        reflexivity.
Qed.
Instance nat_plus_lcancel : PlusLcancel nat := {
    plus_lcancel := nat_plus_lcancel_;
}.
(* end hide *)
Theorem nat_plus_zero : ∀ a b, 0 = a + b → 0 = a ∧ 0 = b.
    intros a b eq.
    nat_destruct a.
    -   nat_destruct b.
        +   split; reflexivity.
        +   rewrite nat_plus_rsuc in eq.
            inversion eq.
    -   rewrite nat_plus_lsuc in eq.
        inversion eq.
Qed.
