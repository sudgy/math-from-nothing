Require Import init.

Require Import nat.
Require Import set.
Require Export plus_group.

Require Export int_base.

Notation "a ⊕ b" := (fst a + fst b, snd a + snd b) : int_scope.

(* begin hide *)
Section IntPlus.

Local Open Scope int_scope.

Lemma int_plus_wd : ∀ a b c d, a ~ b → c ~ d → a ⊕ c ~ b ⊕ d.
Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd.
    cbn in *.
    pose proof (lrplus ab cd) as eq; clear ab cd.
    do 2 rewrite <- plus_assoc in eq.
    rewrite (plus_assoc b2) in eq; rewrite (plus_assoc a2) in eq.
    rewrite (plus_comm b2) in eq; rewrite (plus_comm a2) in eq.
    repeat rewrite plus_assoc in eq; repeat rewrite plus_assoc.
    exact eq.
Qed.

End IntPlus.

Global Instance int_plus : Plus int := {
    plus := binary_self_op int_plus_wd
}.

Lemma int_plus_comm : ∀ a b, a + b = b + a.
Proof.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold plus; equiv_simpl.
    rewrite (plus_comm a1).
    rewrite (plus_comm a2).
    reflexivity.
Qed.
Global Instance int_plus_comm_class : PlusComm int := {
    plus_comm := int_plus_comm
}.

Lemma int_plus_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold plus; equiv_simpl.
    repeat rewrite assoc.
    reflexivity.
Qed.
Global Instance int_plus_assoc_class : PlusAssoc int := {
    plus_assoc := int_plus_assoc
}.

Global Instance int_zero : Zero int := {
    zero := to_equiv_type int_equiv (zero, zero);
}.

Lemma int_plus_lid : ∀ a, zero + a = a.
Proof.
    intros a.
    equiv_get_value a.
    unfold zero, plus; equiv_simpl.
    do 2 rewrite plus_lid.
    reflexivity.
Qed.

Global Instance int_plus_lid_class : PlusLid int := {
    plus_lid := int_plus_lid;
}.
(* end hide *)
Notation "⊖ a" := (snd a, fst a) (at level 35, right associativity) : int_scope.

(* begin hide *)
Section IntNeg.

Local Open Scope int_scope.

Lemma int_neg_wd : ∀ a b, a ~ b → ⊖a ~ ⊖b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    cbn in *.
    symmetry.
    rewrite (plus_comm b2), (plus_comm a2).
    exact eq.
Qed.

End IntNeg.

Global Instance int_neg : Neg int := {
    neg := unary_self_op int_neg_wd;
}.

Lemma int_plus_linv : ∀ a, -a + a = zero.
Proof.
    intros a.
    equiv_get_value a.
    unfold zero, plus, neg; equiv_simpl.
    rewrite plus_rid, plus_lid.
    apply plus_comm.
Qed.

Global Instance int_plus_linv_class : PlusLinv int := {
    plus_linv := int_plus_linv;
}.
(* end hide *)
Theorem nat_to_int_plus : ∀ a b,
    nat_to_int (a + b) = nat_to_int a + nat_to_int b.
Proof.
    intros a b.
    unfold plus at 2, nat_to_int; equiv_simpl.
    do 2 rewrite plus_rid.
    reflexivity.
Qed.

Theorem nat_nz_int : ∀ n, 0 ≠ nat_to_int (nat_suc n).
Proof.
    intros n n_eq.
    apply nat_to_int_eq in n_eq.
    inversion n_eq.
Qed.
