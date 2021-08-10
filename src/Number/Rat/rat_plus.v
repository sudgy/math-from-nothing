Require Import init.

Require Import nat0.
Require Import int.
Require Import set.
Require Export plus_group.

Require Export rat_base.

Theorem nat01_mult_ex : ∀ a b, ∃ n, nat0_suc a * nat0_suc b = nat0_suc n.
    intros a b.
    remember (nat0_suc a * nat0_suc b) as c.
    nat0_destruct c.
    -   rewrite nat0_mult_lsuc in Heqc.
        rewrite nat0_plus_lsuc in Heqc.
        inversion Heqc.
    -   exists c.
        reflexivity.
Qed.

Definition nat01_mult a b := ex_val (nat01_mult_ex a b).
Theorem nat01_mult_eq :
        ∀ a b, nat0_suc (nat01_mult a b) = nat0_suc a * nat0_suc b.
    intros a b.
    unfold nat01_mult.
    rewrite_ex_val c c_eq.
    symmetry; exact c_eq.
Qed.

Notation "a ⊕ b" := (fst a * nat0_to_int (nat0_suc (snd b))
                        + fst b * nat0_to_int (nat0_suc (snd a)),
                     nat01_mult (snd a) (snd b)) : rat_scope.

(* begin hide *)
Section RatPlus.

Local Open Scope rat_scope.

Lemma rat_plus_wd : ∀ a b c d, a ~ b → c ~ d → a ⊕ c ~ b ⊕ d.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd.
    cbn in *.
    do 2 rewrite rdist.
    do 2 rewrite nat01_mult_eq.
    do 2 rewrite <- nat0_to_int_mult.
    mult_bring_left (nat0_to_int (nat0_suc b2)).
    mult_bring_left a1.
    rewrite mult_assoc.
    rewrite ab.
    mult_bring_left (nat0_to_int (nat0_suc d2)).
    mult_bring_left c1.
    rewrite (mult_assoc c1).
    rewrite cd.
    mult_bring_left (nat0_to_int (nat0_suc b2)).
    mult_bring_left (nat0_to_int (nat0_suc c2)).
    reflexivity.
Qed.

End RatPlus.

Instance rat_plus : Plus rat := {
    plus := binary_self_op rat_plus_wd
}.

Lemma rat_plus_comm : ∀ a b, a + b = b + a.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold plus; equiv_simpl.
    do 2 rewrite nat01_mult_eq.
    rewrite plus_comm.
    rewrite (mult_comm (nat0_suc b2)).
    reflexivity.
Qed.
Instance rat_plus_comm_class : PlusComm rat := {
    plus_comm := rat_plus_comm
}.

Lemma rat_plus_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold plus; equiv_simpl.
    repeat rewrite nat01_mult_eq.
    do 6 rewrite rdist.
    rewrite plus_assoc.
    repeat rewrite <- mult_assoc.
    repeat rewrite nat0_to_int_mult.
    mult_bring_left (nat0_suc a2).
    mult_bring_right (nat0_suc c2).
    reflexivity.
Qed.
Instance rat_plus_assoc_class : PlusAssoc rat := {
    plus_assoc := rat_plus_assoc
}.

Instance rat_zero : Zero rat := {
    zero := int_to_rat 0
}.

Lemma rat_plus_lid : ∀ a, 0 + a = a.
    intros a.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold zero; cbn; unfold int_to_rat, plus; equiv_simpl.
    rewrite nat01_mult_eq.
    rewrite mult_lanni, plus_lid.
    change (nat0_suc 0) with (one (U := nat0)).
    rewrite mult_lid.
    change (nat0_to_int 1) with 1.
    rewrite mult_rid.
    reflexivity.
Qed.
Instance rat_plus_lid_class : PlusLid rat := {
    plus_lid := rat_plus_lid;
}.
(* end hide *)
Notation "⊖ a" := (-fst a, snd a) (at level 35, right associativity): rat_scope.

(* begin hide *)
Section RatNeg.

Local Open Scope rat_scope.

Lemma rat_neg_wd : ∀ a b, a ~ b → ⊖a ~ ⊖b.
    intros [a1 a2] [b1 b2] ab.
    cbn in *.
    do 2 rewrite mult_lneg.
    apply f_equal.
    exact ab.
Qed.

End RatNeg.

Instance rat_neg : Neg rat := {
    neg := unary_self_op rat_neg_wd;
}.

Lemma rat_plus_linv : ∀ a, -a + a = zero.
    intros a.
    equiv_get_value a.
    destruct a as [a b].
    unfold zero; cbn.
    unfold neg, plus, int_to_rat; equiv_simpl.
    rewrite mult_lneg.
    rewrite plus_linv.
    do 2 rewrite mult_lanni.
    reflexivity.
Qed.

Instance rat_plus_linv_class : PlusLinv rat := {
    plus_linv := rat_plus_linv;
}.
(* end hide *)
Theorem int_to_rat_plus : ∀ a b,
        int_to_rat a + int_to_rat b = int_to_rat (a + b).
    intros a b.
    unfold int_to_rat, plus at 1; equiv_simpl.
    rewrite nat01_mult_eq.
    change (nat0_suc 0) with (one (U := nat0)).
    rewrite mult_lid.
    change (nat0_to_int 1) with 1.
    do 4 rewrite mult_rid.
    reflexivity.
Qed.

Theorem nat0_to_rat_plus : ∀ a b,
        nat0_to_rat a + nat0_to_rat b = nat0_to_rat (a + b).
    intros a b.
    unfold nat0_to_rat.
    rewrite int_to_rat_plus.
    rewrite nat0_to_int_plus.
    reflexivity.
Qed.

(* DELETE
Theorem nat1_nz_rat : ∀ n, 0 ≠ nat1_to_rat n.
    intros n n_eq.
    apply (nat0_to_rat_eq 0 (nat1_to_nat0 n)) in n_eq.
    exact (nat1_nz _ n_eq).
Qed.
*)

Theorem int_to_rat_neg : ∀ a, -int_to_rat a = int_to_rat (-a).
    intros a.
    unfold neg at 1, int_to_rat; equiv_simpl.
    reflexivity.
Qed.
