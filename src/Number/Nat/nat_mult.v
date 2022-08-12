Require Import init.

Require Import nat_plus.

Require Export mult.

Global Instance nat_mult : Mult nat := {
    mult := fix mult a b :=
        match a with
            | nat_suc a' => b + mult a' b
            | nat_zero => 0
        end
}.

Lemma nat_mult_lanni_tmp : ∀ a, 0 * a = 0.
Proof.
    intros a.
    unfold mult, zero at 1; cbn.
    reflexivity.
Qed.

Global Instance nat_mult_one : One nat := {
    one := nat_suc nat_zero;
}.
Ltac nat_induction n ::=
    induction n;
    change nat_zero with (zero (U := nat)) in *;
    change (nat_suc zero) with (one (U := nat)) in *.
Ltac nat_destruct n ::=
    destruct n;
    change nat_zero with (zero (U := nat)) in *;
    change (nat_suc zero) with (one (U := nat)) in *.

Global Instance nat_mult_lid : MultLid nat.
Proof.
    split.
    intros a.
    unfold one, mult; cbn.
    apply plus_rid.
Qed.

Theorem nat_mult_lsuc : ∀ a b, nat_suc a * b = b + a * b.
Proof.
    reflexivity.
Qed.
Theorem nat_mult_rsuc : ∀ a b, a * nat_suc b = a + a * b.
Proof.
    intros a b.
    nat_induction a.
    -   do 2 rewrite nat_mult_lanni_tmp.
        rewrite plus_rid.
        reflexivity.
    -   do 2 rewrite nat_mult_lsuc.
        rewrite IHa.
        do 2 rewrite plus_assoc.
        rewrite nat_plus_lsuc.
        rewrite (nat_plus_lsuc a b).
        rewrite (plus_comm a b).
        reflexivity.
Qed.

Global Instance nat_mult_comm : MultComm nat.
Proof.
    split.
    intros a b.
    nat_induction a.
    -   rewrite nat_mult_lanni_tmp.
        nat_induction b.
        +   rewrite nat_mult_lanni_tmp.
            reflexivity.
        +   rewrite nat_mult_lsuc.
            rewrite plus_lid.
            exact IHb.
    -   rewrite nat_mult_lsuc.
        rewrite nat_mult_rsuc.
        rewrite IHa.
        reflexivity.
Qed.

Global Instance nat_ldist : Ldist nat.
Proof.
    split.
    intros a b c.
    nat_induction a.
    -   do 3 rewrite nat_mult_lanni_tmp.
        rewrite plus_lid.
        reflexivity.
    -   do 3 rewrite nat_mult_lsuc.
        rewrite IHa.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.

Global Instance nat_mult_assoc : MultAssoc nat.
Proof.
    split.
    intros a b c.
    nat_induction a.
    -   do 3 rewrite mult_lanni.
        reflexivity.
    -   do 2 rewrite nat_mult_lsuc.
        rewrite IHa.
        rewrite rdist.
        reflexivity.
Qed.

Theorem nat_neq_suc_mult : ∀ a b, 0 ≠ nat_suc a * nat_suc b.
Proof.
    intros a b contr.
    rewrite nat_mult_lsuc in contr.
    rewrite nat_plus_lsuc in contr.
    exact (nat_zero_suc contr).
Qed.

Global Instance nat_mult_lcancel : MultLcancel nat.
Proof.
    split.
    intros a b c c_neq eq.
    nat_destruct c; [>contradiction|].
    clear c_neq.
    revert b eq.
    nat_induction a; intros b eq.
    -   nat_destruct b; [>reflexivity|].
        exfalso.
        rewrite mult_ranni in eq.
        exact (nat_neq_suc_mult _ _ eq).
    -   nat_destruct b.
        +   exfalso; clear IHa.
            rewrite mult_ranni in eq.
            symmetry in eq.
            exact (nat_neq_suc_mult _ _ eq).
        +   apply f_equal.
            apply IHa.
            do 2 rewrite nat_mult_rsuc in eq.
            apply plus_lcancel in eq.
            exact eq.
Qed.

#[refine]
Global Instance nat_not_trivial_class : NotTrivial nat := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Proof.
    apply nat_zero_suc.
Qed.
