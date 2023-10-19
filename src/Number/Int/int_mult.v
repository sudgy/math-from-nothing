Require Import init.

Require Import nat.
Require Export mult_ring.
Require Import set.
Require Export domain_category.
Require Export ring_category.

Require Import int_plus.

Notation "a ⊗ b" :=
    (fst a * fst b + snd a * snd b, fst a * snd b + snd a * fst b)
    (at level 40, left associativity) : int_scope.

Open Scope int_scope.

Lemma int_mult_wd : ∀ a b c d, a ~ b → c ~ d → a ⊗ c ~ b ⊗ d.
Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd.
    cbn in *.
    pose proof (rmult c1 ab) as eq1.
    pose proof (rmult c2 ab) as eq2.
    pose proof (lmult b1 cd) as eq3.
    pose proof (lmult b2 cd) as eq4.
    symmetry in eq2.
    symmetry in eq4.
    pose proof (lrplus eq1 eq3) as eq5.
    pose proof (lrplus eq2 eq4) as eq6.
    do 2 rewrite ldist in eq5, eq6.
    do 2 rewrite rdist in eq5, eq6.
    rewrite plus_4 in eq5.
    rewrite (plus_comm (a1 * c1)) in eq5.
    do 2 rewrite <- plus_assoc in eq5.
    apply plus_lcancel in eq5.
    rewrite (plus_4 (a1 * c2)) in eq6.
    rewrite (plus_comm (b2 * c2)) in eq6.
    do 2 rewrite plus_assoc in eq6.
    apply plus_rcancel in eq6.
    pose proof (lrplus eq5 eq6) as eq.
    clear ab cd eq1 eq2 eq3 eq4 eq5 eq6.
    rewrite plus_4 in eq.
    rewrite (plus_comm _ (b1 * c2)) in eq.
    do 2 rewrite (plus_assoc _ (b1 * c2)) in eq.
    do 2 rewrite (plus_comm _ (b1 * c2)) in eq.
    do 4 rewrite <- (plus_assoc (b1 * c2)) in eq.
    apply plus_lcancel in eq.
    rewrite (plus_comm _ (b2 * c1)) in eq.
    do 2 rewrite <- (plus_assoc (b2 * c1)) in eq.
    do 2 rewrite (plus_comm (b2 * c1)) in eq.
    do 2 rewrite (plus_assoc _ _ (b2 * c1)) in eq.
    apply plus_rcancel in eq.
    rewrite (plus_comm (a1 * c2)).
    rewrite (plus_4 (b1 * d1)).
    rewrite (plus_comm (b1 * d1)), (plus_comm (b2 * d2)).
    exact eq.
Qed.

Global Instance int_mult : Mult int_base := {
    mult := binary_op (binary_self_wd int_mult_wd);
}.

Global Instance int_mult_comm : MultComm int_base.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold mult; equiv_simpl.
    do 2 rewrite (mult_comm b1 _).
    do 2 rewrite (mult_comm b2 _).
    rewrite (plus_comm (a2 * b1)).
    reflexivity.
Qed.


Global Instance int_mult_assoc : MultAssoc int_base.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold mult; equiv_simpl.
    do 4 rewrite ldist, rdist.
    do 8 rewrite mult_assoc.
    apply lrplus.
    -   rewrite (plus_comm (a2 * b1 * c2)).
        apply plus_4.
    -   rewrite plus_4.
        rewrite (plus_comm (a2 * b2 * c2)).
        reflexivity.
Qed.

Global Instance int_ldist : Ldist int_base.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold plus, mult; equiv_simpl.
    do 4 rewrite ldist.
    apply lrplus; apply plus_4.
Qed.

Global Instance int_one : One int_base := {
    one := to_equiv int_equiv (1, 0);
}.

Global Instance int_mult_lid : MultLid int_base.
Proof.
    split.
    intros a.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold mult, one; equiv_simpl.
    do 2 rewrite mult_lanni.
    do 2 rewrite plus_rid.
    do 2 rewrite mult_lid.
    reflexivity.
Qed.

Lemma int_mult_zero : ∀ {a b}, 0 = a * b → 0 = a ∨ 0 = b.
Proof.
    intros a b eq.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold mult, zero in *.
    equiv_simpl in eq.
    equiv_simpl.
    do 2 rewrite plus_rid, plus_lid.
    rewrite plus_lid, plus_rid in eq.
    destruct (trichotomy a1 a2) as [[ltq|eq']|ltq].
    -   apply nat_lt_ex in ltq as [c c_eq].
        rewrite <- c_eq in eq.
        do 2 rewrite rdist in eq.
        rewrite plus_3 in eq.
        do 2 apply plus_lcancel in eq.
        apply mult_lcancel in eq; [>|apply nat_zero_suc].
        right; symmetry; exact eq.
    -   left; symmetry; exact eq'.
    -   apply nat_lt_ex in ltq as [c c_eq].
        rewrite <- c_eq in eq.
        do 2 rewrite rdist in eq.
        rewrite plus_comm in eq.
        rewrite (plus_comm _ (a2 * b2)) in eq.
        rewrite plus_3 in eq.
        do 2 apply plus_lcancel in eq.
        apply mult_lcancel in eq; [>|apply nat_zero_suc].
        right; exact eq.
Qed.

Global Instance int_mult_lcancel : MultLcancel int_base.
Proof.
    split.
    intros a b c c_neq_0 eq.
    rewrite <- plus_0_anb_a_b in eq.
    rewrite <- mult_rneg in eq.
    rewrite <- ldist in eq.
    destruct (int_mult_zero eq) as [eq2|eq2]; [>contradiction|].
    rewrite plus_0_anb_a_b in eq2.
    exact eq2.
Qed.

#[refine]
Global Instance int_not_trivial : NotTrivial int_base := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Proof.
    unfold zero, one; equiv_simpl.
    do 2 rewrite plus_rid.
    exact not_trivial_one.
Qed.

Definition int : IntegralDomain := make_domain
    int_base
    int_not_trivial
    int_plus
    int_zero
    int_neg
    int_mult
    int_one
    int_plus_assoc
    int_plus_comm
    int_plus_lid
    int_plus_linv
    int_mult_assoc
    int_mult_comm
    int_ldist
    int_mult_lid
    int_mult_lcancel.

Definition int_ring := domain_to_ring int.
Definition int_cring := domain_to_cring int.

Theorem from_nat_int : ∀ n, (from_nat n : int) = (to_equiv int_equiv (n, 0) : int).
Proof.
    intros n.
    nat_induction n.
    -   rewrite homo_zero.
        unfold zero at 1; cbn.
        reflexivity.
    -   rewrite from_nat_suc.
        rewrite IHn.
        unfold one, plus; equiv_simpl.
        do 3 rewrite plus_rid.
        reflexivity.
Qed.

Close Scope int_scope.
