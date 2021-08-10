Require Import init.

Require Import nat0_plus.

Require Export mult.

Fixpoint nat0_mult_ a b :=
    match a with
        | nat0_suc a' => b + nat0_mult_ a' b
        | nat0_zero => zero
    end.

(* begin hide *)
Instance nat0_mult : Mult nat0 := {
    mult := nat0_mult_;
}.

Lemma nat0_mult_lanni_ : ∀ a, zero * a = zero.
    intros a.
    reflexivity.
Qed.
Instance nat0_mult_lanni : MultLanni nat0 := {
    mult_lanni := nat0_mult_lanni_;
}.

Instance nat0_mult_one : One nat0 := {
    one := nat0_suc nat0_zero;
}.
Ltac nat0_induction n ::=
    induction n;
    change nat0_zero with (zero (U := nat0)) in *;
    change (nat0_suc zero) with (one (U := nat0)) in *.
Ltac nat0_destruct n ::=
    destruct n;
    change nat0_zero with (zero (U := nat0)) in *;
    change (nat0_suc zero) with (one (U := nat0)) in *.

Lemma nat0_mult_lid_ : ∀ a, one * a = a.
    intros a.
    unfold one, mult; cbn.
    apply plus_rid.
Qed.
Instance nat0_mult_lid : MultLid nat0 := {
    mult_lid := nat0_mult_lid_;
}.
(* end hide *)
Theorem nat0_mult_lsuc : ∀ a b, nat0_suc a * b = b + a * b.
    intros a b.
    unfold mult; cbn.
    reflexivity.
Qed.
Theorem nat0_mult_rsuc : ∀ a b, a * nat0_suc b = a + a * b.
    intros a b.
    nat0_induction a.
    -   do 2 rewrite mult_lanni.
        rewrite plus_rid.
        reflexivity.
    -   do 2 rewrite nat0_mult_lsuc.
        rewrite IHa.
        do 2 rewrite plus_assoc.
        rewrite nat0_plus_lsuc.
        rewrite (nat0_plus_lsuc a b).
        rewrite (plus_comm a b).
        reflexivity.
Qed.

(* begin hide *)
Lemma nat0_mult_comm_ : ∀ a b, a * b = b * a.
    intros a b.
    nat0_induction a.
    -   rewrite mult_lanni.
        nat0_induction b.
        +   rewrite mult_lanni.
            reflexivity.
        +   rewrite nat0_mult_lsuc.
            rewrite <- IHb.
            rewrite plus_lid.
            reflexivity.
    -   rewrite nat0_mult_lsuc.
        rewrite nat0_mult_rsuc.
        rewrite IHa.
        reflexivity.
Qed.

Instance nat0_mult_comm : MultComm nat0 := {
    mult_comm := nat0_mult_comm_;
}.

Lemma nat0_ldist_ : ∀ a b c, a * (b + c) = a * b + a * c.
    intros a b c.
    nat0_induction a.
    -   do 3 rewrite mult_lanni.
        rewrite plus_lid.
        reflexivity.
    -   do 3 rewrite nat0_mult_lsuc.
        rewrite IHa.
        (* TODO: RING *)
        do 2 rewrite <- plus_assoc.
        apply lplus.
        rewrite plus_comm.
        rewrite <- plus_assoc.
        apply lplus.
        apply plus_comm.
Qed.

Instance nat0_ldist : Ldist nat0 := {
    ldist := nat0_ldist_;
}.

Lemma nat0_mult_assoc_ : ∀ a b c, a * (b * c) = (a * b) * c.
    intros a b c.
    nat0_induction a.
    -   do 3 rewrite mult_lanni.
        reflexivity.
    -   do 2 rewrite nat0_mult_lsuc.
        rewrite IHa.
        rewrite rdist.
        reflexivity.
Qed.

Instance nat0_mult_assoc : MultAssoc nat0 := {
    mult_assoc := nat0_mult_assoc_;
}.
(* end hide *)
Theorem nat0_neq_suc_mult : ∀ a b, zero ≠ nat0_suc a * nat0_suc b.
    intros a b contr.
    rewrite nat0_mult_lsuc in contr.
    rewrite nat0_plus_lsuc in contr.
    inversion contr.
Qed.

Theorem nat0_mult_zero : ∀ a b, 0 = a * b → 0 = a ∨ 0 = b.
    intros a b eq.
    nat0_destruct a.
    -   left; reflexivity.
    -   nat0_destruct b.
        +   right; reflexivity.
        +   exfalso.
            apply (nat0_neq_suc_mult a b).
            exact eq.
Qed.

(* begin hide *)
Lemma nat0_mult_lcancel_ : ∀ a b c, zero ≠ c → c * a = c * b → a = b.
    intros a b c c_neq eq.
    nat0_destruct c.
    { contradiction. }
    clear c_neq.
    revert b eq.
    nat0_induction a.
    -   intros b eq.
        nat0_destruct b; try reflexivity.
        exfalso.
        rewrite mult_ranni in eq.
        apply nat0_neq_suc_mult with c b.
        exact eq.
    -   intros b eq.
        nat0_destruct b.
        +   exfalso; clear IHa.
            rewrite mult_ranni in eq.
            apply nat0_neq_suc_mult with c a.
            symmetry; exact eq.
        +   apply f_equal.
            apply IHa.
            do 2 rewrite nat0_mult_rsuc in eq.
            apply plus_lcancel in eq.
            exact eq.
Qed.

Instance nat0_mult_lcancel : MultLcancel nat0 := {
    mult_lcancel := nat0_mult_lcancel_;
}.

Lemma nat0_not_trivial : 0 ≠ 1.
    intro contr; inversion contr.
Qed.

Instance nat0_not_trivial_class : NotTrivial nat0 := {
    not_trivial := nat0_not_trivial
}.
(* end hide *)
