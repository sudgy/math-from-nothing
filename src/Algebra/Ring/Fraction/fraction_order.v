Require Import init.

Require Import set.
Require Export order_mult.

Require Export fraction_base.
Require Export fraction_plus.
Require Export fraction_mult.
Require Import nat.
Require Export ordered_domain_category.
Require Import order_cone.

Section FractionOrder.

Context U `{OrderedDomainClass U, @Archimedean U UP UZ UO}.

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

Let p := unary_op frac_pos_wd.

Lemma frac_pos_simpl : ∀ a b, 0 < [b|] →
    p (to_equiv (frac_equiv U) (a, b)) ↔ 0 ≤ a.
Proof.
    intros a b b_pos.
    unfold p; equiv_simpl.
    unfold frac_pos_base; cbn.
    split.
    -   intros leq.
        rewrite <- (mult_lanni [b|]) in leq at 1.
        apply le_mult_rcancel_pos in leq; [>|exact b_pos].
        exact leq.
    -   intros leq.
        rewrite <- (mult_lanni [b|]) at 1.
        apply le_rmult_pos; [>apply b_pos|].
        exact leq.
Qed.

(* These are done as lemmas because #[refine] won't allow the proof terms to be
opaque, and using Program is really slow for some reason. *)
Lemma frac_cone_plus : ∀ a b, p a → p b → p (a + b).
Proof.
    intros a b.
    pose proof (frac_pos_ex a) as [a1 [a2 [a2_pos a_eq]]]; subst a.
    pose proof (frac_pos_ex b) as [b1 [b2 [b2_pos b_eq]]]; subst b.
    unfold plus; cbn.
    rewrite binary_op_eq; cbn.
    rewrite frac_pos_simpl by exact a2_pos.
    rewrite frac_pos_simpl by exact b2_pos.
    rewrite frac_pos_simpl by exact (lt_mult a2_pos b2_pos).
    intros a1_pos b1_pos.
    destruct a2_pos, b2_pos.
    apply le_pos_plus; apply le_mult; assumption.
Qed.

Lemma frac_cone_mult : ∀ a b, p a → p b → p (a * b).
Proof.
    intros a b.
    pose proof (frac_pos_ex a) as [a1 [a2 [a2_pos a_eq]]]; subst a.
    pose proof (frac_pos_ex b) as [b1 [b2 [b2_pos b_eq]]]; subst b.
    unfold mult; cbn.
    rewrite binary_op_eq; cbn.
    rewrite frac_pos_simpl by exact a2_pos.
    rewrite frac_pos_simpl by exact b2_pos.
    rewrite frac_pos_simpl by exact (lt_mult a2_pos b2_pos).
    apply le_mult.
Qed.

Lemma frac_cone_square : ∀ a, p (a * a).
Proof.
    intros a.
    pose proof (frac_pos_ex a) as [a1 [a2 [a2_pos a_eq]]]; subst a.
    unfold mult; cbn.
    rewrite binary_op_eq; cbn.
    rewrite frac_pos_simpl by exact (lt_mult a2_pos a2_pos).
    apply square_pos.
Qed.

Lemma frac_cone_neg : ¬p (-1).
Proof.
    unfold neg, one; cbn.
    rewrite unary_op_eq; cbn.
    rewrite frac_pos_simpl by exact one_pos.
    rewrite nle_lt.
    apply pos_neg2.
    exact one_pos.
Qed.

Lemma frac_cone_all : ∀ a, {p a} + {p (-a)}.
Proof.
    intros a.
    apply or_to_strong.
    pose proof (frac_pos_ex a) as [a1 [a2 [a2_pos a_eq]]]; subst a.
    rewrite frac_pos_simpl by exact a2_pos.
    unfold neg; cbn.
    rewrite unary_op_eq; cbn.
    rewrite frac_pos_simpl by exact a2_pos.
    rewrite <- neg_pos.
    destruct (connex 0 a1) as [leq|leq].
    -   left; exact leq.
    -   right; exact leq.
Qed.

Local Instance frac_cone : OrderCone (frac_type U) := {
    cone := unary_op frac_pos_wd;
    cone_plus := frac_cone_plus;
    cone_mult := frac_cone_mult;
    cone_square := frac_cone_square;
    cone_neg := frac_cone_neg;
    cone_all := frac_cone_all;
}.
Definition frac_order := cone_order : Order (frac_type U).
Definition frac_le_antisym := cone_le_antisym
    : Antisymmetric (le (U := frac_type U)).
Definition frac_le_trans := cone_le_transitive
    : Transitive (le (U := frac_type U)).
Definition frac_le_connex := cone_le_connex : Connex (le (U := frac_type U)).
Definition frac_le_lplus := cone_le_lplus : OrderLplus (frac_type U).
Definition frac_le_mult := cone_le_mult : OrderMult (frac_type U).

Theorem frac_pos_zero : ∀ a : frac_type U, 0 ≤ a ↔ cone a.
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
    fold p.
    unfold plus, neg; equiv_simpl.
    rewrite frac_pos_simpl by (exact (lt_mult b2_pos a2_pos)).
    rewrite mult_lneg.
    rewrite le_plus_0_anb_b_a.
    reflexivity.
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

Local Instance to_frac_le : HomomorphismLe (to_frac U).
Proof.
    split.
    intros a b ab.
    unfold to_frac.
    rewrite frac_le by exact one_pos; cbn.
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
    unfold cone in x_pos; equiv_simpl in x_pos.
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
