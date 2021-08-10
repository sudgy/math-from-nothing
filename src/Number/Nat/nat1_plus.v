Require Import init.
Require Export nat1_base.
Require Import nat0_plus.

Require Export plus_group.
Require Import mult_ring.

Fixpoint nat1_plus a b :=
    match a with
        | nat1_one => nat1_suc b
        | nat1_suc a' => nat1_plus a' (nat1_suc b)
    end.

Instance nat1_plus_class : Plus nat1 := {
    plus := nat1_plus
}.

Theorem nat1_plus_lrsuc : ∀ a b, nat1_suc a + b = a + nat1_suc b.
    intros a b.
    unfold plus; cbn.
    reflexivity.
Qed.
Theorem nat1_plus_lsuc : ∀ a b, nat1_suc a + b = nat1_suc (a + b).
    induction a.
    -   intros b.
        unfold plus; cbn.
        reflexivity.
    -   intros b.
        rewrite nat1_plus_lrsuc.
        rewrite IHa.
        rewrite nat1_plus_lrsuc.
        reflexivity.
Qed.
Theorem nat1_plus_rsuc : ∀ a b, a + nat1_suc b = nat1_suc (a + b).
    intros a b.
    rewrite <- nat1_plus_lsuc, nat1_plus_lrsuc.
    reflexivity.
Qed.

Theorem nat1_to_nat0_plus : ∀ a b,
        nat1_to_nat0 a + nat1_to_nat0 b = nat1_to_nat0 (a + b).
    induction a.
    -   intros b.
        reflexivity.
    -   intros b.
        cbn.
        rewrite nat0_plus_lsuc.
        rewrite IHa.
        rewrite nat1_plus_lsuc.
        cbn.
        reflexivity.
Qed.

Lemma nat1_plus_comm : ∀ a b, a + b = b + a.
    intros a b.
    apply nat1_to_nat0_eq.
    do 2 rewrite <- nat1_to_nat0_plus.
    apply plus_comm.
Qed.
Instance nat1_plus_comm_class : PlusComm nat1 := {
    plus_comm := nat1_plus_comm
}.

Lemma nat1_plus_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
    intros a b c.
    apply nat1_to_nat0_eq.
    do 4 rewrite <- nat1_to_nat0_plus.
    apply plus_assoc.
Qed.
Instance nat1_plus_assoc_class : PlusAssoc nat1 := {
    plus_assoc := nat1_plus_assoc
}.

Lemma nat1_plus_lcancel : ∀ a b c, c + a = c + b → a = b.
    intros a b c eq.
    apply nat1_to_nat0_eq.
    apply (f_equal nat1_to_nat0) in eq.
    do 2 rewrite <- nat1_to_nat0_plus in eq.
    apply plus_lcancel in eq.
    exact eq.
Qed.
Instance nat1_plus_lcancel_class : PlusLcancel nat1 := {
    plus_lcancel := nat1_plus_lcancel
}.
