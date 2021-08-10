Require Import init.

Require Import nat.
Require Import int.
Require Import set.
Require Export mult.

Require Import rat_plus.

Notation "a ⊗ b" := (fst a * fst b, nat1_mult (snd a) (snd b))
    (at level 40, left associativity) : rat_scope.

Open Scope rat_scope.

(* begin hide *)
Lemma rat_mult_wd : ∀ a b c d, a ~ b → c ~ d → a ⊗ c ~ b ⊗ d.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd.
    cbn in *.
    do 2 rewrite nat1_mult_eq.
    pose proof (lrmult ab cd) as eq; clear ab cd.
    do 2 rewrite <- mult_assoc in eq.
    rewrite (mult_assoc _ c1) in eq.
    rewrite (mult_assoc _ d1) in eq.
    rewrite (mult_comm _ c1) in eq.
    rewrite (mult_comm _ d1) in eq.
    do 2 rewrite <- mult_assoc in eq.
    do 2 rewrite nat_to_int_mult in eq.
    do 2 rewrite mult_assoc in eq.
    exact eq.
Qed.

Instance rat_mult : Mult rat := {
    mult := binary_self_op rat_mult_wd;
}.

Lemma rat_mult_comm : ∀ a b, a * b = b * a.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold mult; equiv_simpl.
    do 2 rewrite nat1_mult_eq.
    rewrite (mult_comm a1).
    rewrite (mult_comm (nat_suc a2)).
    reflexivity.
Qed.
Instance rat_mult_comm_class : MultComm rat := {
    mult_comm := rat_mult_comm;
}.

Lemma rat_mult_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold mult; equiv_simpl.
    do 4 rewrite nat1_mult_eq.
    do 2 rewrite mult_assoc.
    reflexivity.
Qed.
Instance rat_mult_assoc_class : MultAssoc rat := {
    mult_assoc := rat_mult_assoc;
}.

Lemma rat_ldist : ∀ a b c, a * (b + c) = a * b + a * c.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold mult, plus; equiv_simpl.
    repeat rewrite nat1_mult_eq.
    rewrite ldist.
    do 2 rewrite rdist.
    repeat rewrite <- mult_assoc.
    do 4 rewrite nat_to_int_mult.
    mult_bring_left (nat_suc a2).
    mult_bring_right (nat_suc c2).
    reflexivity.
Qed.
Instance rat_ldist_class : Ldist rat := {
    ldist := rat_ldist;
}.

Instance rat_one : One rat := {
    one := int_to_rat 1
}.

Theorem rat_mult_lid : ∀ a, 1 * a = a.
    intros a.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold one; cbn.
    unfold int_to_rat, mult; equiv_simpl.
    rewrite nat1_mult_eq.
    change (nat_suc 0) with (one (U := nat)).
    do 2 rewrite mult_lid.
    reflexivity.
Qed.
Instance rat_mult_lid_class : MultLid rat := {
    mult_lid := rat_mult_lid;
}.
(* end hide *)
Notation "⊘ a" := (
    match (trichotomy 0 (fst a)) with
    | semi_or_left comps =>
        match comps with
        | strong_or_left comp =>
            (nat_to_int (nat_suc (snd a)), ex_val (int_pos_nat1_ex _ comp))
        | strong_or_right comp => (zero, one)
        end
    | semi_or_right comp =>
        (-nat_to_int (nat_suc (snd a)), ex_val (int_neg_nat1_ex _ comp))
    end
) : rat_scope.

(* begin hide *)
Lemma rat_inv_wd : ∀ a b, a ~ b → ⊘a ~ ⊘b.
    intros [a1 a2] [b1 b2] eq.
    cbn in *.
    destruct (trichotomy 0 a1) as [[a1_pos|a1_zero]|a1_neg].
    all: destruct (trichotomy 0 b1) as [[b1_pos|b1_zero]|b1_neg].
    all: cbn.
    -   rewrite_ex_val b1' b1_eq.
        rewrite_ex_val a1' a1_eq.
        rewrite <- a1_eq, <- b1_eq.
        symmetry.
        rewrite mult_comm, (mult_comm _ b1).
        exact eq.
    -   subst b1.
        rewrite mult_lanni in eq.
        symmetry in eq.
        apply int_mult_0 in eq as [contr|contr].
        +   subst.
            destruct a1_pos; contradiction.
        +   contradiction (nat_nz_int _ contr).
    -   exfalso.
        apply lt_rmult_pos with (nat_to_int (nat_suc b2)) in a1_pos.
        2: apply nat1_to_int_pos.
        apply lt_rmult_pos with (nat_to_int (nat_suc a2)) in b1_neg.
        2: apply nat1_to_int_pos.
        rewrite mult_lanni in a1_pos.
        rewrite mult_lanni in b1_neg.
        pose proof (trans b1_neg a1_pos) as ltq.
        rewrite eq in ltq.
        destruct ltq; contradiction.
    -   subst a1.
        rewrite mult_lanni in eq.
        apply int_mult_0 in eq as [contr|contr].
        +   subst.
            destruct b1_pos; contradiction.
        +   contradiction (nat_nz_int _ contr).
    -   reflexivity.
    -   subst a1.
        rewrite mult_lanni in eq.
        apply int_mult_0 in eq as [contr|contr].
        +   subst.
            destruct b1_neg; contradiction.
        +   contradiction (nat_nz_int _ contr).
    -   exfalso.
        apply lt_rmult_pos with (nat_to_int (nat_suc b2)) in a1_neg.
        2: apply nat1_to_int_pos.
        apply lt_rmult_pos with (nat_to_int (nat_suc a2)) in b1_pos.
        2: apply nat1_to_int_pos.
        rewrite mult_lanni in a1_neg.
        rewrite mult_lanni in b1_pos.
        pose proof (trans a1_neg b1_pos) as ltq.
        rewrite eq in ltq.
        destruct ltq; contradiction.
    -   subst b1.
        rewrite mult_lanni in eq.
        symmetry in eq.
        apply int_mult_0 in eq as [contr|contr].
        +   subst.
            destruct a1_neg; contradiction.
        +   contradiction (nat_nz_int _ contr).
    -   rewrite_ex_val b1' b1_eq.
        rewrite_ex_val a1' a1_eq.
        do 2 rewrite mult_lrneg.
        rewrite <- a1_eq, <- b1_eq.
        symmetry.
        rewrite mult_comm, (mult_comm _ b1).
        exact eq.
Qed.

Instance rat_inv : Div rat := {
    div := unary_self_op rat_inv_wd;
}.

Lemma rat_mult_linv : ∀ a, 0 ≠ a → div a * a = 1.
    intros a a_nz.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold one; cbn.
    unfold div, mult, int_to_rat; equiv_simpl.
    unfold zero in a_nz; cbn in a_nz.
    unfold int_to_rat in a_nz; equiv_simpl in a_nz.
    rewrite mult_lanni in a_nz.
    destruct (trichotomy 0 a1) as [[a1_pos|a1_z]|a1_neg]; cbn.
    -   rewrite_ex_val a1' a1_eq.
        change (nat_to_int (nat_suc 0)) with (one (U := int)).
        rewrite mult_lid, mult_rid.
        rewrite nat1_mult_eq.
        rewrite <- nat_to_int_mult.
        rewrite <- a1_eq.
        apply comm.
    -   rewrite <- a1_z in a_nz.
        rewrite mult_lanni in a_nz.
        contradiction.
    -   rewrite_ex_val a1' a1_eq.
        change (nat_to_int (nat_suc 0)) with (one (U := int)).
        rewrite mult_lid, mult_rid.
        rewrite a1_eq.
        rewrite mult_lneg, mult_rneg.
        rewrite neg_neg.
        rewrite nat1_mult_eq.
        rewrite nat_to_int_mult.
        rewrite comm.
        reflexivity.
Qed.
Instance rat_mult_linv_class : MultLinv rat := {
    mult_linv := rat_mult_linv
}.

Theorem rat_not_trivial : 0 ≠ 1.
    intros contr.
    unfold zero, one in contr; cbn in contr.
    unfold int_to_rat in contr; equiv_simpl in contr.
    rewrite mult_lanni, mult_lid in contr.
    change (nat_to_int (nat_suc 0)) with (one (U := int)) in contr.
    apply not_trivial in contr.
    exact contr.
Qed.
Instance rat_not_trivial_class : NotTrivial rat := {
    not_trivial := rat_not_trivial;
}.

Close Scope rat_scope.
(* end hide *)
Theorem int_to_rat_mult : ∀ a b,
        int_to_rat a * int_to_rat b = int_to_rat (a * b).
    intros a b.
    unfold mult at 1, int_to_rat; equiv_simpl.
    rewrite nat1_mult_eq.
    change (nat_suc 0) with (one (U := nat)).
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem nat_to_rat_mult : ∀ a b,
        nat_to_rat a * nat_to_rat b = nat_to_rat (a * b).
    intros a b.
    unfold nat_to_rat.
    rewrite int_to_rat_mult.
    rewrite nat_to_int_mult.
    reflexivity.
Qed.
