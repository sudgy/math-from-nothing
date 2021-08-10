Require Import init.

Require Import nat0.
Require Import nat1.
Require Export mult.
Require Import set.

Require Import int_plus.

Notation "a ⊗ b" :=
    (fst a * fst b + snd a * snd b, fst a * snd b + snd a * fst b)
    (at level 40, left associativity) : int_scope.

(* begin hide *)
Open Scope int_scope.

Lemma int_mult_wd : ∀ a b c d, a ~ b → c ~ d → a ⊗ c ~ b ⊗ d.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd.
    simpl in *.
    pose proof (rmult c1 ab) as eq1.
    pose proof (rmult c2 ab) as eq2.
    pose proof (lmult b1 cd) as eq3.
    pose proof (lmult b2 cd) as eq4.
    symmetry in eq2.
    symmetry in eq4.
    pose proof (lrplus eq1 eq2) as eq5.
    pose proof (lrplus eq3 eq4) as eq6.
    pose proof (lrplus eq5 eq6) as eq.
    clear ab cd eq1 eq2 eq3 eq4 eq5 eq6.
    repeat rewrite ldist in eq.
    repeat rewrite rdist in eq.
    plus_cancel_right (b2 * c1) in eq.
    plus_cancel_right (b1 * c2) in eq.
    plus_cancel_right (b1 * c1) in eq.
    plus_cancel_right (b2 * c2) in eq.
    plus_bring_left (a1 * c2).
    plus_bring_left (a2 * c1).
    repeat rewrite plus_assoc.
    exact eq.
Qed.

Instance int_mult : Mult int := {
    mult := binary_self_op int_mult_wd;
}.

Lemma int_mult_comm : ∀ a b, a * b = b * a.
    intros a b.
    equiv_get_value a b.
    unfold mult; simpl; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2].
    simpl.
    do 2 rewrite (mult_comm b1 _).
    do 2 rewrite (mult_comm b2 _).
    rewrite (plus_comm (a2 * b1)).
    reflexivity.
Qed.

Global Instance int_mult_comm_class : MultComm int := {
    mult_comm := int_mult_comm;
}.

Lemma int_mult_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
    intros a b c.
    equiv_get_value a b c.
    unfold mult; simpl; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; simpl.
    repeat rewrite ldist, rdist.
    repeat rewrite mult_assoc.
    plus_cancel_left (a1 * b1 * c1)%nat0.
    plus_cancel_left (a1 * b1 * c2)%nat0.
    plus_cancel_left (a1 * b2 * c1)%nat0.
    plus_cancel_left (a1 * b2 * c2)%nat0.
    plus_cancel_left (a2 * b1 * c1)%nat0.
    plus_cancel_left (a2 * b1 * c2)%nat0.
    reflexivity.
Qed.

Global Instance int_mult_assoc_class : MultAssoc int := {
    mult_assoc := int_mult_assoc;
}.

Lemma int_ldist : ∀ a b c, a * (b + c) = a * b + a * c.
    intros a b c.
    equiv_get_value a b c.
    unfold plus, mult; simpl; equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; simpl.
    do 4 rewrite ldist.
    plus_cancel_left (a1 * b1)%nat0.
    plus_cancel_left (a1 * c1)%nat0.
    plus_cancel_left (a2 * b2)%nat0.
    plus_cancel_left (a2 * c2)%nat0.
    plus_cancel_left (a2 * b1)%nat0.
    plus_cancel_left (a1 * c2)%nat0.
    reflexivity.
Qed.

Global Instance int_ldist_class : Ldist int := {
    ldist := int_ldist;
}.

Global Instance int_one : One int := {
    one := to_equiv_type int_equiv (1, 0);
}.

Lemma int_mult_lid : ∀ a, 1 * a = a.
    intros a.
    equiv_get_value a.
    unfold mult, one; simpl; equiv_simpl.
    destruct a as [a1 a2]; simpl.
    repeat rewrite mult_lanni.
    repeat rewrite plus_rid.
    do 2 rewrite mult_lid.
    reflexivity.
Qed.

Instance int_mult_lid_class : MultLid int := {
    mult_lid := int_mult_lid;
}.
(* end hide *)
Theorem int_mult_0 : ∀ {a b}, a * b = 0 → a = 0 ∨ b = 0.
    intros a b eq.
    equiv_get_value a b.
    unfold mult, zero in *; simpl in *.
    equiv_simpl in eq.
    equiv_simpl.
    destruct a as [a1 a2], b as [b1 b2]; simpl in *.
    repeat rewrite plus_rid in *.
    repeat rewrite plus_lid in *.
    pose proof (trichotomy a1 a2) as comps.
    destruct comps as [comps|comp].
    destruct comps as [comp|comp].
    { (* a1 < a2 *)
        apply nat0_lt_ex in comp as [c [c_neq_0 c_eq]].
        rewrite <- c_eq in eq.
        do 2 rewrite rdist in eq.
        plus_cancel_left (a1 * b1) in eq.
        plus_cancel_left (a1 * b2) in eq.
        apply mult_lcancel in eq.
        right; symmetry; exact eq.
        rewrite neq_sym; exact c_neq_0.
    }
    { (* a1 = a2 *)
        left; exact comp.
    }
    { (* a1 > a2 *)
        apply nat0_lt_ex in comp as [c [c_neq_0 c_eq]].
        rewrite <- c_eq in eq.
        do 2 rewrite rdist in eq.
        plus_cancel_left (a2 * b1)%nat0 in eq.
        plus_cancel_left (a2 * b2)%nat0 in eq.
        apply mult_lcancel in eq.
        right; exact eq.
        rewrite neq_sym; exact c_neq_0.
    }
Qed.

(* begin hide *)
Lemma int_mult_lcancel : ∀ a b c, 0 ≠ c → c * a = c * b → a = b.
    intros a b c c_neq_0 eq.
    rewrite neq_sym in c_neq_0.
    apply plus_eq_rneg in eq.
    rewrite <- mult_rneg in eq.
    rewrite <- ldist in eq.
    symmetry in eq.
    destruct (int_mult_0 eq) as [eq2|eq2]; try contradiction.
    apply plus_lrneg_eq.
    exact eq2.
Qed.

Global Instance int_mult_lcancel_class : MultLcancel int := {
    mult_lcancel := int_mult_lcancel;
}.

Lemma int_not_trivial : 0 ≠ 1.
    unfold zero, one; simpl.
    equiv_simpl.
    intro eq.
    inversion eq.
Qed.

Instance int_not_trivial_class : NotTrivial int := {
    not_trivial := int_not_trivial;
}.

Close Scope int_scope.
(* end hide *)
Theorem nat0_to_int_mult : ∀ a b,
        nat0_to_int a * nat0_to_int b = nat0_to_int (a * b).
    intros a b.
    unfold mult at 1, nat0_to_int; simpl; equiv_simpl; simpl.
    do 2 rewrite mult_lanni.
    rewrite mult_ranni.
    do 4 rewrite plus_rid.
    reflexivity.
Qed.

Theorem nat1_to_int_mult : ∀ a b,
        nat1_to_int a * nat1_to_int b = nat1_to_int (a * b).
    intros a b.
    unfold nat1_to_int.
    rewrite nat0_to_int_mult.
    rewrite nat1_to_nat0_mult.
    reflexivity.
Qed.

Theorem nat1_to_int_one : nat1_to_int 1 = 1.
    reflexivity.
Qed.
