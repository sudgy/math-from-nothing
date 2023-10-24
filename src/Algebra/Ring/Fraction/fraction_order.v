Require Import init.

Require Import set.
Require Export order_mult.

Require Export fraction_base.
Require Export fraction_plus.
Require Export fraction_mult.
Require Import nat.
Require Export ordered_domain_category.

Section FractionOrder.

Context U `{OrderedFieldClass U, @Archimedean U UP UZ UO}.

Local Infix "~" := (eq_equal (frac_equiv U)).

Local Existing Instances frac_plus frac_zero frac_neg frac_plus_assoc
    frac_plus_comm frac_plus_lid frac_plus_linv frac_mult frac_one frac_div
    frac_ldist frac_mult_assoc frac_mult_comm frac_mult_lid frac_mult_linv
    frac_not_trivial to_frac_inj to_frac_plus.

Theorem frac_pos_ex : ∀ (x : frac_type U), ∃ a b,
    0 < [b|] ∧ x = to_equiv (frac_equiv U) (a, b).
Proof.
    intros x.
    equiv_get_value x.
    destruct x as [a [b b_nz]].
    classic_case (0 ≤ b) as [b_pos|b_neg].
    -   exists a, [b|b_nz].
        split.
        +   split; assumption.
        +   reflexivity.
    -   pose proof b_nz as b'_nz.
        rewrite neg_nz in b'_nz.
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

Theorem frac_pos_ex_div : ∀ (x : frac_type U), ∃ (a b : U),
    0 < b ∧ x = to_frac U a / to_frac U b.
Proof.
    intros x.
    pose proof (frac_pos_ex x) as [a [[b b_nz] [b_pos x_eq]]].
    exists a, b.
    split; [>exact b_pos|].
    rewrite x_eq.
    apply to_frac_div.
    assumption.
Qed.

Let frac_pos_base (a : frac_base U) := 0 ≤ fst a * [snd a|].

Lemma frac_pos_wd_1 : ∀ a b, a ~ b → frac_pos_base a → frac_pos_base b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    unfold frac_pos_base; cbn in *.
    unfold frac_eq in eq; cbn in eq.
    intros a_pos.
    apply (le_mult (square_pos [b2|])) in a_pos.
    rewrite mult_4 in a_pos.
    rewrite mult_assoc in a_pos.
    rewrite <- (mult_assoc [b2|]) in a_pos.
    rewrite eq in a_pos.
    rewrite mult_assoc in a_pos.
    rewrite <- mult_assoc in a_pos.
    rewrite <- (mult_lanni ([a2|] * [a2|])) in a_pos at 1.
    apply le_mult_rcancel_pos in a_pos.
    -   rewrite mult_comm.
        exact a_pos.
    -   split; [>apply square_pos|].
        apply mult_nz; exact [|a2].
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

Local Instance frac_order : Order (frac_type U) := {
    le a b := frac_pos (b - a)
}.

Theorem frac_pos_zero : ∀ a, 0 ≤ a ↔ frac_pos a.
Proof.
    intros a.
    equiv_get_value a.
    unfold le; cbn.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem frac_le : ∀ a1 a2 b1 b2, 0 < [a2|] → 0 < [b2|] →
    (to_equiv (frac_equiv U) (a1, a2) ≤ to_equiv (frac_equiv U) (b1, b2)) ↔
    (a1 * [b2|] ≤ b1 * [a2|]).
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
    (to_equiv (frac_equiv U) (a1, a2) < to_equiv (frac_equiv U) (b1, b2)) ↔
    (a1 * [b2|] < b1 * [a2|]).
Proof.
    intros a1 a2 b1 b2 a2_pos b2_pos.
    unfold strict.
    rewrite frac_le by assumption.
    equiv_simpl.
    unfold frac_eq; cbn.
    reflexivity.
Qed.

Local Instance frac_le_connex : Connex le.
Proof.
    split.
    intros a b.
    apply or_to_strong.
    pose proof (frac_pos_ex a) as [a1 [a2 [a2_pos a_eq]]].
    pose proof (frac_pos_ex b) as [b1 [b2 [b2_pos b_eq]]].
    subst a b.
    do 2 rewrite frac_le by assumption.
    destruct (connex (a1 * [b2|]) (b1 * [a2|])) as [leq|leq].
    -   left; exact leq.
    -   right; exact leq.
Qed.

Local Instance frac_le_antisym : Antisymmetric le.
Proof.
    split.
    intros a b.
    pose proof (frac_pos_ex a) as [a1 [a2 [a2_pos a_eq]]].
    pose proof (frac_pos_ex b) as [b1 [b2 [b2_pos b_eq]]].
    subst a b.
    do 2 rewrite frac_le by assumption.
    equiv_simpl.
    unfold frac_eq; cbn.
    apply antisym.
Qed.

Local Instance frac_le_trans : Transitive le.
Proof.
    split.
    intros a b c.
    pose proof (frac_pos_ex a) as [a1 [a2 [a2_pos a_eq]]].
    pose proof (frac_pos_ex b) as [b1 [b2 [b2_pos b_eq]]].
    pose proof (frac_pos_ex c) as [c1 [c2 [c2_pos c_eq]]].
    subst a b c.
    do 3 rewrite frac_le by assumption.
    intros ab bc.
    apply le_lmult_pos with [c2|] in ab; [>|apply c2_pos].
    apply le_rmult_pos with [a2|] in bc; [>|apply a2_pos].
    rewrite (mult_3 _ b1) in ab.
    do 2 rewrite <- mult_assoc in bc.
    pose proof (trans ab bc) as eq.
    rewrite (mult_comm [b2|]) in eq.
    do 2 rewrite mult_assoc in eq.
    apply le_mult_rcancel_pos in eq; [>|apply b2_pos].
    rewrite mult_comm.
    exact eq.
Qed.

Local Instance frac_le_lplus : OrderLplus (frac_type U).
Proof.
    split.
    intros a b c.
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
    do 2 rewrite (mult_comm [c2|]).
    rewrite mult_4.
    apply le_lplus.
    do 2 rewrite (mult_4 _ [c2|]).
    apply le_rmult_pos; [>|exact ab].
    apply lt_mult; exact c2_pos.
Qed.

Local Instance frac_le_mult : OrderMult (frac_type U).
Proof.
    split.
    intros a b.
    do 3 rewrite frac_pos_zero.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold frac_pos, mult; equiv_simpl.
    unfold frac_pos_base; cbn.
    intros leq1 leq2.
    rewrite mult_4.
    apply le_mult; assumption.
Qed.

Local Instance to_frac_le : HomomorphismLe (to_frac U).
Proof.
    split.
    intros a b ab.
    unfold to_frac.
    rewrite frac_le by apply one_pos; cbn.
    do 2 rewrite mult_rid.
    exact ab.
Qed.

Local Instance frac_arch : Archimedean (frac_type U).
Proof.
    apply field_impl_arch1.
    intros x x_pos.
    pose proof (frac_pos_ex x) as [a [b [b_pos x_eq]]].
    destruct x_pos as [x_pos x_neq].
    rewrite frac_pos_zero in x_pos.
    subst x.
    unfold frac_pos in x_pos; equiv_simpl in x_pos.
    unfold frac_pos_base in x_pos; cbn in x_pos.
    rewrite <- (mult_lanni [b|]) in x_pos at 1.
    apply le_mult_rcancel_pos in x_pos; [>|exact b_pos].
    unfold zero in x_neq; cbn in x_neq.
    unfold to_frac in x_neq; equiv_simpl in x_neq.
    unfold frac_eq in x_neq; cbn in x_neq.
    rewrite mult_lanni, mult_rid in x_neq.
    pose proof (archimedean a [b|] (make_and x_pos x_neq) b_pos) as [n n_ltq].
    exists n.
    rewrite (to_frac_div U).
    rewrite <- lt_mult_rrmove_pos.
    2: {
        unfold zero; cbn.
        rewrite <- homo_lt2.
        exact b_pos.
    }
    replace (from_nat n * to_frac U [b|]) with (to_frac U (n × [b|])).
    2: {
        clear n_ltq.
        rewrite <- nat_mult_from.
        nat_induction n.
        -   do 2 rewrite nat_mult_lanni.
            reflexivity.
        -   do 2 rewrite nat_mult_suc.
            rewrite <- IHn.
            apply homo_plus.
    }
    rewrite <- homo_lt2.
    exact n_ltq.
Qed.

End FractionOrder.
