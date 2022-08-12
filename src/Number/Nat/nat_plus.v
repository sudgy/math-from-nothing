Require Import init.
Require Export nat_base.

Require Export plus_group.

Global Instance nat_plus : Plus nat := {
    plus := fix plus a b :=
        match a with
            | nat_zero => b
            | nat_suc a' => plus a' (nat_suc b)
        end
}.

Theorem nat_plus_lrsuc : ∀ a b, nat_suc a + b = a + nat_suc b.
Proof.
    intros a b.
    reflexivity.
Qed.

Theorem nat_plus_lsuc : ∀ a b, nat_suc a + b = nat_suc (a + b).
Proof.
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
Proof.
    intros a b.
    rewrite <- nat_plus_lrsuc, nat_plus_lsuc.
    reflexivity.
Qed.

Global Instance nat_zero_instance : Zero nat := {
    zero := nat_zero;
}.
Ltac nat_induction n := induction n; change nat_zero with zero in *.
Ltac nat_destruct n := destruct n; change nat_zero with zero in *.

Global Instance nat_plus_lid : PlusLid nat.
Proof.
    split.
    intros a.
    unfold zero, plus; cbn.
    reflexivity.
Qed.

Lemma nat_plus_rid_tmp : ∀ a, a + 0 = a.
Proof.
    nat_induction a.
    -   apply plus_lid.
    -   rewrite nat_plus_lsuc.
        rewrite IHa.
        reflexivity.
Qed.

Global Instance nat_plus_comm : PlusComm nat.
Proof.
    split.
    intros a b.
    nat_induction a.
    -   rewrite plus_lid, nat_plus_rid_tmp.
        reflexivity.
    -   rewrite nat_plus_lsuc, nat_plus_rsuc.
        rewrite IHa.
        reflexivity.
Qed.

Global Instance nat_plus_assoc : PlusAssoc nat.
Proof.
    split.
    intros a b c.
    nat_induction a.
    -   do 2 rewrite plus_lid.
        reflexivity.
    -   do 3 rewrite nat_plus_lsuc.
        rewrite IHa.
        reflexivity.
Qed.

Global Instance nat_plus_lcancel : PlusLcancel nat.
Proof.
    split.
    intros a b c eq.
    nat_induction c.
    -   do 2 rewrite plus_lid in eq.
        exact eq.
    -   apply IHc; clear IHc.
        do 2 rewrite nat_plus_lsuc in eq.
        rewrite nat_suc_eq in eq.
        exact eq.
Qed.

Theorem nat_plus_zero : ∀ a b, 0 = a + b → 0 = a ∧ 0 = b.
Proof.
    intros a b eq.
    nat_destruct a.
    -   rewrite plus_lid in eq.
        split; [>reflexivity|exact eq].
    -   rewrite nat_plus_lsuc in eq.
        contradiction (nat_zero_suc eq).
Qed.
