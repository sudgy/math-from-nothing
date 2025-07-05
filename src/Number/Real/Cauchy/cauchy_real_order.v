Require Import init.

Require Export cauchy_real_mult.
Require Export order_cone.

Definition real_pos_base (a : real_base) :=
    0 = to_equiv real_equiv a ∨
    ∃ N, ∀ i, N ≤ i → 0 ≤ a i.

Lemma real_pos_wd1 : ∀ a b, a ~ b → real_pos_base a → real_pos_base b.
Proof.
    intros a b ab [a_z|a_pos].
    {
        left.
        rewrite a_z.
        equiv_simpl.
        exact ab.
    }
    apply or_right.
    intros b_nz.
    assert (0 ≠ to_equiv real_equiv a) as a_nz.
    {
        intros contr.
        rewrite contr in b_nz.
        equiv_simpl in b_nz.
        contradiction.
    }
    apply cauchy_nz in a_nz as [ε [N1 [ε_pos a_nz]]].
    specialize (ab ε ε_pos) as [N2 ab].
    destruct a_pos as [N3 a_pos].
    exists (max N1 (max N2 N3)).
    intros i i_ge.
    specialize (a_pos i (trans (trans (rmax _ _) (rmax _ _)) i_ge)).
    specialize (ab i (trans (trans (lmax _ _) (rmax _ _)) i_ge)).
    specialize (a_nz i (trans (lmax _ _) i_ge)).
    rewrite abs_pos_eq in a_nz by exact a_pos.
    apply (le_lt_trans (abs_le_pos _)) in ab.
    rewrite <- lt_plus_rrmove in ab.
    pose proof (le_lt_trans a_nz ab) as ltq.
    rewrite <- lt_plus_0_a_b_ba in ltq.
    apply ltq.
Qed.

Lemma real_pos_wd : ∀ a b, a ~ b → real_pos_base a = real_pos_base b.
Proof.
    intros a b ab.
    apply propositional_ext.
    split; [>exact (real_pos_wd1 _ _ ab)|].
    apply eq_symmetric in ab.
    exact (real_pos_wd1 _ _ ab).
Qed.

Definition real_pos := unary_op real_pos_wd.

Lemma real_pos_plus : ∀ a b, real_pos a → real_pos b → real_pos (a + b).
Proof.
    intros a b.
    classic_case (0 = a) as [a_z|a_nz].
    {
        subst a.
        rewrite plus_lid.
        intros a_in b_in; exact b_in.
    }
    classic_case (0 = b) as [b_z|b_nz].
    {
        subst b.
        rewrite plus_rid.
        intros a_in b_in; exact a_in.
    }
    equiv_get_value a b.
    unfold real_pos, plus; equiv_simpl.
    intros [a_z|a_pos]; [>contradiction|].
    intros [b_z|b_pos]; [>contradiction|].
    right.
    destruct a_pos as [N1 a_pos].
    destruct b_pos as [N2 b_pos].
    exists (max N1 N2).
    intros i i_ge; cbn.
    specialize (a_pos i (trans (lmax N1 N2) i_ge)).
    specialize (b_pos i (trans (rmax N1 N2) i_ge)).
    apply le_pos_plus; assumption.
Qed.

Lemma real_pos_mult : ∀ a b, real_pos a → real_pos b → real_pos (a * b).
Proof.
    intros a b.
    classic_case (0 = a) as [a_z|a_nz].
    {
        subst a.
        rewrite mult_lanni.
        intros a_in b_in; exact a_in.
    }
    classic_case (0 = b) as [b_z|b_nz].
    {
        subst b.
        rewrite mult_ranni.
        intros a_in b_in; exact b_in.
    }
    equiv_get_value a b.
    unfold real_pos, mult; equiv_simpl.
    intros [a_z|a_pos]; [>contradiction|].
    intros [b_z|b_pos]; [>contradiction|].
    right.
    destruct a_pos as [N1 a_pos].
    destruct b_pos as [N2 b_pos].
    exists (max N1 N2).
    intros i i_ge; cbn.
    specialize (a_pos i (trans (lmax N1 N2) i_ge)).
    specialize (b_pos i (trans (rmax N1 N2) i_ge)).
    apply le_mult; assumption.
Qed.

Lemma real_pos_square : ∀ a, real_pos (a * a).
Proof.
    intros a.
    equiv_get_value a.
    unfold real_pos, mult; equiv_simpl.
    right; cbn.
    exists 0.
    intros i i_ge.
    apply square_pos.
Qed.

Lemma real_pos_neg : ¬real_pos (-1).
Proof.
    unfold real_pos, neg, one; cbn.
    unfold rat_to_real; equiv_simpl.
    unfold real_pos_base; cbn.
    unfold zero at 1; cbn.
    unfold rat_to_real; equiv_simpl.
    rewrite not_or.
    split.
    +   intros contr.
        specialize (contr 1 one_pos) as [N contr].
        specialize (contr N (refl N)).
        rewrite neg_neg, plus_lid in contr.
        rewrite abs_one in contr.
        destruct contr; contradiction.
    +   intros [N contr].
        specialize (contr N (refl N)).
        apply neg_pos in contr.
        destruct (le_lt_trans contr one_pos); contradiction.
Qed.

Lemma real_pos_all : ∀ a, {real_pos a} + {real_pos (-a)}.
Proof.
    intros a.
    equiv_get_value a.
    unfold real_pos, neg; equiv_simpl.
    apply or_to_strong.
    apply or_right.
    unfold real_pos_base; cbn.
    rewrite not_or.
    intros [a_nz a_neg].
    right.
    apply cauchy_nz in a_nz as [ε [N1 [ε_pos a_nz]]].
    destruct a as [a a_cauchy]; cbn in *.
    specialize (a_cauchy ε ε_pos) as [N2 a_cauchy].
    rewrite not_ex in a_neg.
    specialize (a_neg (max N1 N2)).
    rewrite not_all in a_neg.
    destruct a_neg as [n a_neg].
    rewrite not_impl, nle_lt in a_neg.
    destruct a_neg as [n_ge a_neg].
    specialize (a_nz n (trans (lmax N1 N2) n_ge)).
    exists (max N1 N2).
    intros i i_ge.
    specialize (a_cauchy i n (trans (rmax _ _) i_ge) (trans (rmax _ _) n_ge)).
    rewrite abs_neg_eq in a_nz by apply a_neg.
    apply (le_lt_trans (abs_le_pos _)) in a_cauchy.
    pose proof (lt_le_trans a_cauchy a_nz) as ltq.
    rewrite <- lt_plus_a_0_ab_b in ltq.
    apply neg_pos.
    apply ltq.
Qed.

Global Instance real_cone : OrderCone real := {
    cone := real_pos;
    cone_plus := real_pos_plus;
    cone_mult := real_pos_mult;
    cone_square := real_pos_square;
    cone_neg := real_pos_neg;
    cone_all := real_pos_all;
}.

Lemma real_lt : ∀ a b, to_equiv real_equiv a < to_equiv real_equiv b →
    ∃ ε N, 0 < ε ∧ ∀ i, N ≤ i → a i + ε < b i.
Proof.
    intros a b ltq.
    destruct ltq as [leq neq].
    unfold le in leq; equiv_simpl in leq.
    unfold neg, plus, real_pos in leq; equiv_simpl in leq.
    rewrite <- plus_0_anb_b_a in neq.
    unfold plus, neg in neq; equiv_simpl in neq.
    destruct leq as [eq|[N1 leq]]; [>contradiction|]; cbn in leq.
    pose proof (cauchy_nz (b ⊕ ⊖ a) neq) as [ε [N2 [ε_pos nz]]]; cbn in nz.
    exists (ε/2), (max N1 N2).
    split; [>apply half_pos; exact ε_pos|].
    intros i i_ge.
    specialize (nz i (trans (rmax _ _) i_ge)).
    specialize (leq i (trans (lmax _ _) i_ge)).
    rewrite abs_pos_eq in nz by exact leq.
    rewrite lt_plus_llmove.
    rewrite (plus_comm (-(a i))).
    apply (lt_le_trans2 nz).
    rewrite <- (plus_half ε) at 2.
    rewrite <- lt_plus_0_a_b_ab.
    apply half_pos.
    exact ε_pos.
Qed.

Lemma real_leq_seq : ∀ x (y : real_base),
    (∀ n, x ≤ rat_to_real (y n)) → x ≤ to_equiv real_equiv y.
Proof.
    intros x y leq.
    equiv_get_value x.
    unfold le; equiv_simpl.
    unfold real_pos, neg, plus; equiv_simpl.
    apply or_right.
    intros neq; cbn.
    apply cauchy_nz in neq as [ε [N1 [ε_pos ε_le]]]; cbn in ε_le.
    pose proof (r_cauchy y _ (half_pos ε_pos)) as [N2 cauchy].
    specialize (leq (max N1 N2)).
    unfold rat_to_real, le in leq; equiv_simpl in leq.
    unfold real_pos, neg, plus in leq; equiv_simpl in leq.
    destruct leq as [eq|leq].
    -   unfold zero in eq; cbn in eq.
        unfold rat_to_real in eq; equiv_simpl in eq.
        specialize (eq _ (half_pos ε_pos)) as [N3 ε_gt].
        pose (i := max (max N1 N2) N3).
        specialize (ε_le i).
        prove_parts ε_le; [>apply (trans (lmax N1 N2)); apply lmax|].
        specialize (cauchy i (max N1 N2)).
        prove_parts cauchy.
        1: apply (trans (rmax N1 N2)); apply lmax.
        1: apply rmax.
        specialize (ε_gt i (rmax _ _)).
        rewrite abs_minus, neg_zero, plus_rid in ε_gt.
        pose proof (lt_lrplus cauchy ε_gt) as ltq.
        rewrite plus_half in ltq.
        apply (le_lt_trans (abs_tri _ _)) in ltq.
        rewrite plus_assoc in ltq.
        rewrite plus_rlinv in ltq.
        contradiction (irrefl _ (lt_le_trans ltq ε_le)).
    -   destruct leq as [N3 leq].
        cbn in leq.
        pose (N := max (max N1 N2) N3).
        exists N.
        intros i i_ge.
        specialize (cauchy (max N1 N2) i (rmax _ _)).
        prove_parts cauchy.
        1: apply (trans2 i_ge); apply (trans (rmax N1 N2)); apply lmax.
        specialize (leq i (trans (rmax _ _) i_ge)).
        specialize (ε_le i (trans (trans (lmax _ _) (lmax _ _)) i_ge)).
        pose proof (average_leq2 _ _ ε_pos) as ε2_lt.
        rewrite plus_lid in ε2_lt.
        apply (trans2 ε2_lt) in cauchy.
        rewrite le_plus_0_anb_b_a in leq.
        apply (le_lt_trans (abs_le_pos _)) in cauchy.
        order_contradiction neg.
        rewrite abs_neg_eq in ε_le by apply neg.
        rewrite neg_plus, neg_neg, plus_comm in ε_le.
        pose proof (lt_le_trans cauchy ε_le) as ltq.
        apply lt_plus_rcancel in ltq.
        contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

Definition real_order := cone_order.
Definition real_le_connex := cone_le_connex.
Definition real_le_antisym := cone_le_antisym.
Definition real_le_trans := cone_le_transitive.
Definition real_le_lplus := cone_le_lplus.
Definition real_le_mult := cone_le_mult.
