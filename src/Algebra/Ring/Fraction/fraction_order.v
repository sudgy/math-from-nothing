Require Import init.

Require Import set.
Require Export order_mult.

Require Export fraction_base.
Require Import fraction_plus.
Require Import fraction_mult.
Require Import nat_abstract.

Section FractionOrder.

Context (U : Type) `{
    UP : Plus U,
    UN : Neg U,
    UZ : Zero U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @Ldist U UP UM,
    @MultAssoc U UM,
    @MultComm U UM,
    @MultLid U UM UO,
    @MultLcancel U UZ UM,
    NotTrivial U,
    UL : Order U,
    @Connex U le,
    @Antisymmetric U le,
    @Transitive U le,
    @OrderLplus U UP UL,
    @OrderMult U UZ UM UL,
    @OrderMultLcancel U UZ UM UL,
    @Archimedean U UP UZ UL
}.

Local Infix "~" := (eq_equal (frac_equiv U)).

Existing Instance frac_plus.
Existing Instance frac_zero.
Existing Instance frac_neg.
Existing Instance frac_plus_assoc.
Existing Instance frac_plus_comm.
Existing Instance frac_plus_lid.
Existing Instance frac_plus_linv.
Existing Instance frac_mult.
Existing Instance frac_one.
Existing Instance frac_div.
Existing Instance frac_ldist.
Existing Instance frac_mult_assoc.
Existing Instance frac_mult_comm.
Existing Instance frac_mult_lid.
Existing Instance frac_mult_linv.
Existing Instance frac_not_trivial.

Theorem frac_pos_ex : ∀ (x : frac U), ∃ a b,
    0 < [b|] ∧ x = to_equiv_type (frac_equiv U) (a, b).
Proof.
    intros x.
    equiv_get_value x.
    destruct x as [a [b b_nz]].
    classic_case (0 <= b) as [b_pos|b_neg].
    -   exists a, [b|b_nz].
        split.
        +   split; assumption.
        +   reflexivity.
    -   assert (0 ≠ -b) as b'_nz.
        {
            intros contr.
            apply (f_equal neg) in contr.
            rewrite neg_zero, neg_neg in contr.
            contradiction.
        }
        exists (-a), [-b|b'_nz].
        split.
        +   rewrite nle_lt in b_neg.
            apply neg_pos2 in b_neg.
            exact b_neg.
        +   equiv_simpl.
            unfold frac_eq; cbn.
            rewrite mult_lneg, mult_rneg.
            reflexivity.
Qed.

Theorem frac_pos_ex_div : ∀ (x : frac U), ∃ (a b : U),
    0 < b ∧ x = to_frac U a / to_frac U b.
Proof.
    intros x.
    pose proof (frac_pos_ex x) as [a [[b b_nz] [b_pos x_eq]]].
    exists a, b.
    split.
    -   exact b_pos.
    -   rewrite x_eq.
        unfold mult, div; equiv_simpl.
        unfold frac_eq; cbn.
        destruct (strong_excluded_middle (0 = b)) as [b_z|b_nz'];
            [>contradiction|]; cbn.
        rewrite mult_lid, mult_rid.
        reflexivity.
Qed.

Let frac_pos_base (a : frac_base U) := 0 <= fst a * [snd a|].

Lemma frac_pos_wd_1 : ∀ a b, a ~ b → frac_pos_base a → frac_pos_base b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    unfold frac_pos_base; cbn in *.
    unfold frac_eq in eq; cbn in eq.
    intros a_pos.
    apply (le_lmult_pos ([b2|] * [b2|])) in a_pos.
    2: apply square_pos.
    rewrite mult_ranni in a_pos.
    rewrite mult_assoc in a_pos.
    rewrite <- (mult_assoc [b2|]) in a_pos.
    rewrite (mult_comm _ a1) in a_pos.
    rewrite eq in a_pos.
    rewrite mult_assoc in a_pos.
    rewrite <- mult_assoc in a_pos.
    rewrite <- (mult_lanni ([a2|] * [a2|])) in a_pos at 1.
    apply le_mult_rcancel_pos in a_pos.
    -   rewrite mult_comm.
        exact a_pos.
    -   split; [>apply square_pos|].
        apply mult_nz; apply [|a2].
Qed.

Lemma frac_pos_wd : ∀ a b, a ~ b → frac_pos_base a = frac_pos_base b.
Proof.
    intros a b eq.
    apply propositional_ext.
    split; apply frac_pos_wd_1.
    -   exact eq.
    -   symmetry.
        exact eq.
Qed.

Definition frac_pos := unary_op frac_pos_wd.

Local Instance frac_order : Order (frac U) := {
    le a b := frac_pos (b - a)
}.

Theorem frac_pos_zero : ∀ a, 0 <= a ↔ frac_pos a.
Proof.
    intros a.
    equiv_get_value a.
    unfold le; cbn.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem frac_le : ∀ a1 a2 b1 b2, 0 < [a2|] → 0 < [b2|] →
    (to_equiv_type (frac_equiv U) (a1, a2) <=
     to_equiv_type (frac_equiv U) (b1, b2)) ↔
    (a1 * [b2|] <= b1 * [a2|]).
Proof.
    intros a1 a2 b1 b2 a2_pos b2_pos.
    unfold le at 1; cbn.
    unfold frac_pos, plus, neg; equiv_simpl.
    unfold frac_pos_base; cbn.
    rewrite <- (le_plus_0_anb_b_a (b1 * [a2|])).
    rewrite mult_lneg.
    split.
    -   intros leq.
        apply (le_mult_rcancel_pos ([b2|] * [a2|])).
        +   apply lt_mult; assumption.
        +   rewrite mult_lanni.
            exact leq.
    -   intros leq.
        apply (le_rmult_pos ([b2|] * [a2|])) in leq.
        +   rewrite mult_lanni in leq.
            exact leq.
        +   apply lt_mult; assumption.
Qed.
Theorem frac_lt : ∀ a1 a2 b1 b2, 0 < [a2|] → 0 < [b2|] →
    (to_equiv_type (frac_equiv U) (a1, a2) <
     to_equiv_type (frac_equiv U) (b1, b2)) ↔
    (a1 * [b2|] < b1 * [a2|]).
Proof.
    intros a1 a2 b1 b2 a2_pos b2_pos.
    unfold strict.
    rewrite frac_le by assumption.
    equiv_simpl.
    unfold frac_eq; cbn.
    reflexivity.
Qed.

Local Program Instance frac_le_connex : Connex le.
Next Obligation.
    apply or_to_strong.
    pose proof (frac_pos_ex x) as [a1 [a2 [a2_pos a_eq]]].
    pose proof (frac_pos_ex y) as [b1 [b2 [b2_pos b_eq]]].
    subst x y.
    do 2 rewrite frac_le by assumption.
    destruct (connex (a1 * [b2|]) (b1 * [a2|])) as [leq|leq].
    -   left; exact leq.
    -   right; exact leq.
Qed.

Local Program Instance frac_le_antisym : Antisymmetric le.
Next Obligation.
    revert H16 H17.
    pose proof (frac_pos_ex x) as [a1 [a2 [a2_pos a_eq]]].
    pose proof (frac_pos_ex y) as [b1 [b2 [b2_pos b_eq]]].
    subst x y.
    do 2 rewrite frac_le by assumption.
    equiv_simpl.
    apply antisym.
Qed.

Local Program Instance frac_le_trans : Transitive le.
Next Obligation.
    revert H16 H17.
    pose proof (frac_pos_ex x) as [a1 [a2 [a2_pos a_eq]]].
    pose proof (frac_pos_ex y) as [b1 [b2 [b2_pos b_eq]]].
    pose proof (frac_pos_ex z) as [c1 [c2 [c2_pos c_eq]]].
    subst x y z.
    do 3 rewrite frac_le by assumption.
    intros ab bc.
    apply le_rmult_pos with [c2|] in ab.
    2: apply c2_pos.
    apply le_rmult_pos with [a2|] in bc.
    2: apply a2_pos.
    rewrite <- (mult_assoc b1) in ab.
    rewrite (mult_comm [a2|]) in ab.
    rewrite mult_assoc in ab.
    pose proof (trans ab bc) as eq.
    mult_bring_right [b2|] in eq.
    apply le_mult_rcancel_pos in eq.
    2: apply b2_pos.
    exact eq.
Qed.

Local Program Instance frac_le_lplus : OrderLplus (frac U).
Next Obligation.
    revert H16.
    pose proof (frac_pos_ex a) as [a1 [a2 [a2_pos a_eq]]].
    pose proof (frac_pos_ex b) as [b1 [b2 [b2_pos b_eq]]].
    pose proof (frac_pos_ex c) as [c1 [c2 [c2_pos c_eq]]].
    subst a b c.
    unfold plus; equiv_simpl.
    rewrite frac_le by assumption.
    intros ab.
    rewrite frac_le; cbn.
    2, 3: apply lt_mult; assumption.
    do 2 rewrite rdist.
    do 4 rewrite <- mult_assoc.
    rewrite (mult_comm [a2|]).
    rewrite (mult_comm [c2|]).
    rewrite <- (mult_assoc [b2|]).
    apply le_lplus.
    mult_bring_right [c2|].
    do 2 rewrite <- (mult_assoc _ [c2|]).
    apply le_rmult_pos.
    -   apply lt_mult; exact c2_pos.
    -   exact ab.
Qed.

Local Program Instance frac_le_mult : OrderMult (frac U).
Next Obligation.
    revert H16 H17.
    do 3 rewrite frac_pos_zero.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold frac_pos, mult; equiv_simpl.
    unfold frac_pos_base; cbn.
    intros leq1 leq2.
    pose proof (le_mult leq1 leq2) as leq.
    rewrite <- mult_assoc in leq.
    rewrite (mult_assoc [a2|]) in leq.
    rewrite (mult_comm _ b1) in leq.
    do 2 rewrite mult_assoc in leq.
    rewrite mult_assoc.
    exact leq.
Qed.

Theorem to_frac_le : ∀ a b, to_frac U a <= to_frac U b ↔ a <= b.
Proof.
    intros a b.
    unfold to_frac.
    rewrite frac_le by apply one_pos; cbn.
    do 2 rewrite mult_rid.
    reflexivity.
Qed.
Theorem to_frac_lt : ∀ a b, to_frac U a < to_frac U b ↔ a < b.
Proof.
    intros a b.
    split.
    -   intros [leq neq].
        split.
        +   rewrite to_frac_le in leq.
            exact leq.
        +   intro contr; subst; contradiction.
    -   intros [leq neq].
        split.
        +   rewrite to_frac_le.
            exact leq.
        +   intro contr.
            apply to_frac_eq in contr; contradiction.
Qed.

(* begin hide *)
Theorem frac_archimedean : ∀ x : frac U, ∃ n, x < from_nat n.
Proof.
    intros x.
    classic_case (0 < x) as [x_pos|x_neg].
    -   pose proof (frac_pos_ex x) as [a [b [b_pos x_eq]]].
        destruct x_pos as [x_pos x_neq].
        rewrite (frac_pos_zero x) in x_pos.
        subst x.
        unfold frac_pos in x_pos; equiv_simpl in x_pos.
        unfold frac_pos_base in x_pos; cbn in x_pos.
        rewrite <- (mult_lanni [b|]) in x_pos at 1.
        apply le_mult_rcancel_pos in x_pos; [>|exact b_pos].
        unfold zero in x_neq; cbn in x_neq.
        unfold to_frac in x_neq; equiv_simpl in x_neq.
        unfold frac_eq in x_neq; cbn in x_neq.
        rewrite mult_lanni, mult_rid in x_neq.
        pose proof (archimedean a [b|] (make_and x_pos x_neq) b_pos)
            as [n n_ltq].
        exists n.
        apply (lt_mult_rcancel_pos (to_frac U [b|])).
        1: {
            unfold zero; cbn.
            rewrite to_frac_lt.
            exact b_pos.
        }
        assert (to_equiv_type (frac_equiv U) (a, b) * to_frac U [b|] =
            to_frac U a) as eq.
        {
            unfold to_frac, mult at 1; equiv_simpl.
            unfold frac_eq; cbn.
            do 2 rewrite mult_rid.
            reflexivity.
        }
        rewrite eq; clear eq.
        assert (from_nat n * to_frac U [b|] = to_frac U (n × [b|]))as eq.
        {
            clear n_ltq.
            nat_induction n.
            -   rewrite from_nat_zero.
                unfold zero at 3; cbn.
                rewrite mult_lanni.
                reflexivity.
            -   cbn.
                rewrite rdist.
                rewrite mult_lid.
                rewrite to_frac_plus.
                apply lplus.
                exact IHn.
        }
        rewrite eq; clear eq.
        rewrite to_frac_lt.
        exact n_ltq.
    -   exists 1.
        rewrite nlt_le in x_neg.
        apply (le_lt_trans x_neg).
        rewrite from_nat_one.
        exact one_pos.
Qed.

Definition frac_arch := field_impl_arch1 frac_archimedean.

End FractionOrder.
