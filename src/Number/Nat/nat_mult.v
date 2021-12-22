Require Import init.

Require Import nat_plus.

Require Export mult.

Fixpoint nat_mult_ a b :=
    match a with
        | nat_suc a' => b + nat_mult_ a' b
        | nat_zero => zero
    end.

(* begin hide *)
Global Instance nat_mult : Mult nat := {
    mult := nat_mult_;
}.

Lemma nat_mult_lanni_ : ∀ a, zero * a = zero.
    intros a.
    reflexivity.
Qed.
Global Instance nat_mult_lanni : MultLanni nat := {
    mult_lanni := nat_mult_lanni_;
}.

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

Lemma nat_mult_lid_ : ∀ a, one * a = a.
    intros a.
    unfold one, mult; cbn.
    apply plus_rid.
Qed.
Global Instance nat_mult_lid : MultLid nat := {
    mult_lid := nat_mult_lid_;
}.
(* end hide *)
Theorem nat_mult_lsuc : ∀ a b, nat_suc a * b = b + a * b.
    intros a b.
    unfold mult; cbn.
    reflexivity.
Qed.
Theorem nat_mult_rsuc : ∀ a b, a * nat_suc b = a + a * b.
    intros a b.
    nat_induction a.
    -   do 2 rewrite mult_lanni.
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

(* begin hide *)
Lemma nat_mult_comm_ : ∀ a b, a * b = b * a.
    intros a b.
    nat_induction a.
    -   rewrite mult_lanni.
        nat_induction b.
        +   rewrite mult_lanni.
            reflexivity.
        +   rewrite nat_mult_lsuc.
            rewrite <- IHb.
            rewrite plus_lid.
            reflexivity.
    -   rewrite nat_mult_lsuc.
        rewrite nat_mult_rsuc.
        rewrite IHa.
        reflexivity.
Qed.

Global Instance nat_mult_comm : MultComm nat := {
    mult_comm := nat_mult_comm_;
}.

Lemma nat_ldist_ : ∀ a b c, a * (b + c) = a * b + a * c.
    intros a b c.
    nat_induction a.
    -   do 3 rewrite mult_lanni.
        rewrite plus_lid.
        reflexivity.
    -   do 3 rewrite nat_mult_lsuc.
        rewrite IHa.
        (* TODO: RING *)
        do 2 rewrite <- plus_assoc.
        apply lplus.
        rewrite plus_comm.
        rewrite <- plus_assoc.
        apply lplus.
        apply plus_comm.
Qed.

Global Instance nat_ldist : Ldist nat := {
    ldist := nat_ldist_;
}.

Lemma nat_mult_assoc_ : ∀ a b c, a * (b * c) = (a * b) * c.
    intros a b c.
    nat_induction a.
    -   do 3 rewrite mult_lanni.
        reflexivity.
    -   do 2 rewrite nat_mult_lsuc.
        rewrite IHa.
        rewrite rdist.
        reflexivity.
Qed.

Global Instance nat_mult_assoc : MultAssoc nat := {
    mult_assoc := nat_mult_assoc_;
}.
(* end hide *)
Theorem nat_neq_suc_mult : ∀ a b, zero ≠ nat_suc a * nat_suc b.
    intros a b contr.
    rewrite nat_mult_lsuc in contr.
    rewrite nat_plus_lsuc in contr.
    inversion contr.
Qed.

Theorem nat_mult_zero : ∀ a b, 0 = a * b → 0 = a ∨ 0 = b.
    intros a b eq.
    nat_destruct a.
    -   left; reflexivity.
    -   nat_destruct b.
        +   right; reflexivity.
        +   exfalso.
            apply (nat_neq_suc_mult a b).
            exact eq.
Qed.

(* begin hide *)
Lemma nat_mult_lcancel_ : ∀ a b c, zero ≠ c → c * a = c * b → a = b.
    intros a b c c_neq eq.
    nat_destruct c.
    { contradiction. }
    clear c_neq.
    revert b eq.
    nat_induction a.
    -   intros b eq.
        nat_destruct b; try reflexivity.
        exfalso.
        rewrite mult_ranni in eq.
        apply nat_neq_suc_mult with c b.
        exact eq.
    -   intros b eq.
        nat_destruct b.
        +   exfalso; clear IHa.
            rewrite mult_ranni in eq.
            apply nat_neq_suc_mult with c a.
            symmetry; exact eq.
        +   apply f_equal.
            apply IHa.
            do 2 rewrite nat_mult_rsuc in eq.
            apply plus_lcancel in eq.
            exact eq.
Qed.

Global Instance nat_mult_lcancel : MultLcancel nat := {
    mult_lcancel := nat_mult_lcancel_;
}.

Lemma nat_not_trivial : 0 ≠ 1.
    intro contr; inversion contr.
Qed.

Global Instance nat_not_trivial_class : NotTrivial nat := {
    not_trivial := nat_not_trivial
}.
(* end hide *)
