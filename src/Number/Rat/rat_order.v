Require Import init.

Require Export rat_base.
Require Import rat_plus.
Require Import rat_mult.

Require Import int.
Require Import nat.
Require Import set.
Require Export order_mult.
Require Export nat_abstract.

Notation "a ≦ b" :=
    (fst a * nat_to_int (nat_suc (snd b)) <=
     fst b * nat_to_int (nat_suc (snd a))) : rat_scope.

(* begin hide *)
Open Scope rat_scope.

Lemma rat_le_wd_1 : ∀ a b c d, a ~ b → c ~ d → a ≦ c → b ≦ d.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd ac.
    cbn in *.
    apply le_rmult_pos with (nat_to_int (nat_suc b2)) in ac.
    2: apply nat1_to_int_pos.
    mult_bring_left (nat_to_int (nat_suc b2)) in ac.
    mult_bring_left a1 in ac.
    rewrite mult_assoc in ac.
    rewrite ab in ac.
    apply le_rmult_pos with (nat_to_int (nat_suc d2)) in ac.
    2: apply nat1_to_int_pos.
    mult_bring_left (nat_to_int (nat_suc d2)) in ac.
    mult_bring_left c1 in ac.
    rewrite (mult_assoc c1) in ac.
    rewrite cd in ac.
    mult_bring_right (nat_to_int (nat_suc c2)) in ac.
    apply le_mult_rcancel_pos in ac.
    2: apply nat1_to_int_pos.
    apply le_mult_rcancel_pos in ac.
    2: apply nat1_to_int_pos.
    rewrite mult_comm in ac.
    exact ac.
Qed.
Lemma rat_le_wd : ∀ a b c d, a ~ b → c ~ d → (a ≦ c) = (b ≦ d).
    intros a b c d ab cd.
    apply propositional_ext.
    split; apply rat_le_wd_1; try assumption; symmetry; assumption.
Qed.

Instance rat_order : Order rat := {
    le := binary_op rat_le_wd;
}.

Lemma rat_le_connex : ∀ a b, {a <= b} + {b <= a}.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold le; equiv_simpl.
    apply connex.
Qed.
Instance rat_le_connex_class : Connex le := {
    connex := rat_le_connex
}.

Lemma rat_le_antisymmetric : ∀ a b, a <= b → b <= a → a = b.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold le; equiv_simpl.
    apply antisym.
Qed.
Instance rat_le_antisym_class : Antisymmetric le := {
    antisym := rat_le_antisymmetric
}.

Lemma rat_le_transitive : ∀ a b c, a <= b → b <= c → a <= c.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold le; equiv_simpl.
    intros ab bc.
    apply le_rmult_pos with (nat_to_int (nat_suc c2)) in ab.
    2: apply nat1_to_int_pos.
    apply le_rmult_pos with (nat_to_int (nat_suc a2)) in bc.
    2: apply nat1_to_int_pos.
    rewrite <- (mult_assoc b1) in ab.
    rewrite (mult_comm (nat_to_int (nat_suc a2))) in ab.
    rewrite mult_assoc in ab.
    pose proof (trans ab bc) as eq.
    mult_bring_right (nat_to_int (nat_suc b2)) in eq.
    apply le_mult_rcancel_pos in eq.
    2: apply nat1_to_int_pos.
    exact eq.
Qed.

Instance rat_le_trans_class : Transitive le := {
    trans := rat_le_transitive;
}.

Lemma rat_le_lplus : ∀ a b c, a <= b → c + a <= c + b.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold le, plus; equiv_simpl.
    intros ab.
    do 2 rewrite rdist.
    do 4 rewrite <- mult_assoc.
    do 2 rewrite nat1_mult_eq.
    do 4 rewrite nat_to_int_mult.
    rewrite (mult_comm (nat_suc a2)).
    rewrite (mult_comm (nat_suc c2)).
    rewrite <- (mult_assoc (nat_suc b2)).
    apply le_lplus.
    mult_bring_right (nat_suc c2).
    do 2 rewrite <- (mult_assoc _ (nat_suc c2)).
    do 2 rewrite <- (nat_to_int_mult _ (nat_suc c2 * nat_suc c2)).
    do 2 rewrite mult_assoc.
    apply le_rmult_pos.
    apply nat_to_int_pos.
    exact ab.
Qed.

Instance rat_le_lplus_class : OrderLplus rat := {
    le_lplus := rat_le_lplus;
}.

Lemma rat_le_mult : ∀ a b, 0 <= a → 0 <= b → 0 <= a * b.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold zero; cbn.
    unfold le, mult, int_to_rat; equiv_simpl.
    rewrite nat1_mult_eq.
    do 3 rewrite mult_lanni.
    change (nat_to_int (nat_suc 0)) with (one (U := int)).
    do 3 rewrite mult_rid.
    apply le_mult.
Qed.

Instance rat_le_mult_class : OrderMult rat := {
    le_mult := rat_le_mult;
}.

Close Scope rat_scope.
(* end hide *)
Theorem int_to_rat_le : ∀ a b, int_to_rat a <= int_to_rat b ↔ a <= b.
    intros a b.
    unfold int_to_rat, le at 1; equiv_simpl.
    change (nat_to_int (nat_suc 0)) with (one (U := int)).
    do 2 rewrite mult_rid.
    reflexivity.
Qed.
Theorem nat_to_rat_le : ∀ a b, nat_to_rat a <= nat_to_rat b ↔ a <= b.
    intros a b.
    unfold nat_to_rat.
    rewrite int_to_rat_le.
    apply nat_to_int_le.
Qed.
Theorem int_to_rat_lt : ∀ a b, int_to_rat a < int_to_rat b ↔ a < b.
    intros a b.
    split.
    -   intros [leq neq].
        split.
        +   rewrite int_to_rat_le in leq.
            exact leq.
        +   intro contr; subst; contradiction.
    -   intros [leq neq].
        split.
        +   rewrite int_to_rat_le.
            exact leq.
        +   intro contr.
            apply int_to_rat_eq in contr; contradiction.
Qed.
Theorem nat_to_rat_lt : ∀ a b, nat_to_rat a < nat_to_rat b ↔ a < b.
    intros a b.
    unfold nat_to_rat.
    rewrite int_to_rat_lt.
    apply nat_to_int_lt.
Qed.

Theorem nat_to_abstract_rat : ∀ a, nat_to_abstract a = nat_to_rat a.
    nat_induction a.
    -   rewrite nat_to_abstract_zero.
        reflexivity.
    -   cbn.
        rewrite IHa.
        change (nat_suc a) with (1 + a).
        rewrite <- nat_to_rat_plus.
        reflexivity.
Qed.

(* begin hide *)
Theorem rat_archimedean : ∀ x : rat, ∃ n, x < nat_to_abstract n.
    intros x.
    classic_case (0 < x) as [x_pos|x_neg].
    -   equiv_get_value x.
        destruct x as [a b].
        destruct x_pos as [x_pos x_neq].
        unfold zero in x_pos; cbn in x_pos.
        unfold int_to_rat, le in x_pos; equiv_simpl in x_pos.
        change (nat_to_int (nat_suc 0)) with (one (U := int)) in x_pos.
        rewrite mult_lanni, mult_rid in x_pos.
        unfold zero in x_neq; cbn in x_neq.
        unfold int_to_rat in x_neq; equiv_simpl in x_neq.
        change (nat_to_int (nat_suc 0)) with (one (U := int)) in x_neq.
        rewrite mult_lanni, mult_rid in x_neq.
        pose proof (nat_to_int_ex _ x_pos) as [n n_eq].
        exists (n + 1).
        rewrite nat_to_abstract_rat.
        assert (a < a * nat_to_int (nat_suc b) + nat_to_int (nat_suc b))
            as ltq.
        {
            assert (a <= a * nat_to_int (nat_suc b)) as leq.
            {
                rewrite <- (mult_rid a) at 1.
                apply le_lmult_pos; try exact x_pos.
                apply nat1_to_int_pos1.
            }
            apply (le_lt_trans leq).
            rewrite <- (plus_rid (a * _)) at 1.
            apply lt_lplus.
            apply nat1_to_int_pos.
        }
        split; unfold nat_to_rat, int_to_rat, le; equiv_simpl.
        all: change (nat_to_int (nat_suc 0)) with (one (U := int)).
        all: rewrite mult_rid.
        all: rewrite <- nat_to_int_plus.
        all: rewrite rdist.
        all: change (nat_to_int 1) with (one (U := int)).
        all: rewrite mult_lid.
        all: rewrite n_eq.
        all: apply ltq.
    -   exists 1.
        rewrite nlt_le in x_neg.
        rewrite nat_to_abstract_rat.
        change (nat_to_rat 1) with 1.
        apply (le_lt_trans x_neg).
        exact one_pos.
Qed.

Definition rat_arch := field_impl_arch1 rat_archimedean.
(* end hide *)
(* begin show *)
Existing Instance rat_arch.
(* end show *)
(* begin hide *)
Close Scope rat_scope.
(* end hide *)
