Require Import init.

Require Import nat1.
Require Import int.
Require Import set.
Require Export plus_group.

Require Export rat_base.

Notation "a ⊕ b" := (fst a * nat1_to_int (snd b) + fst b * nat1_to_int (snd a),
                     snd a * snd b) : rat_scope.

(* begin hide *)
Section RatPlus.

Local Open Scope rat_scope.

Lemma rat_plus_wd : ∀ a b c d, a ~ b → c ~ d → a ⊕ c ~ b ⊕ d.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd.
    cbn in *.
    do 2 rewrite rdist.
    do 2 rewrite <- nat1_to_int_mult.
    mult_bring_left (nat1_to_int b2).
    mult_bring_left a1.
    rewrite mult_assoc.
    rewrite ab.
    mult_bring_left (nat1_to_int d2).
    mult_bring_left c1.
    rewrite (mult_assoc c1).
    rewrite cd.
    mult_bring_left (nat1_to_int b2).
    mult_bring_left (nat1_to_int c2).
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
    rewrite plus_comm.
    rewrite (mult_comm b2).
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
    do 6 rewrite rdist.
    rewrite plus_assoc.
    repeat rewrite <- mult_assoc.
    repeat rewrite nat1_to_int_mult.
    mult_bring_left a2.
    mult_bring_right c2.
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
    rewrite mult_lanni, plus_lid.
    rewrite mult_lid.
    rewrite nat1_to_int_one.
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
    rewrite mult_lid.
    rewrite nat1_to_int_one.
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

Theorem nat1_to_rat_plus : ∀ a b,
        nat1_to_rat a + nat1_to_rat b = nat1_to_rat (a + b).
    intros a b.
    unfold nat1_to_rat.
    rewrite int_to_rat_plus.
    rewrite nat1_to_int_plus.
    reflexivity.
Qed.

Theorem nat1_nz_rat : ∀ n, 0 ≠ nat1_to_rat n.
    intros n n_eq.
    apply (nat0_to_rat_eq 0 (nat1_to_nat0 n)) in n_eq.
    exact (nat1_nz _ n_eq).
Qed.

Theorem int_to_rat_neg : ∀ a, -int_to_rat a = int_to_rat (-a).
    intros a.
    unfold neg at 1, int_to_rat; equiv_simpl.
    reflexivity.
Qed.
