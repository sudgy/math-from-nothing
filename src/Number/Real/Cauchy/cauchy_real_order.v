Require Import init.

Require Export cauchy_real_mult.
Require Export order_cone.

Definition real_pos_base (a : real_base) :=
    0 = to_equiv_type real_equiv a ∨
    ∃ N, ∀ i, N <= i → 0 <= r_seq a i.

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
    assert (0 ≠ to_equiv_type real_equiv a) as a_nz.
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

#[refine]
Global Instance real_cone : OrderCone real := {
    cone := unary_op real_pos_wd
}.
Proof.
-   intros a b.
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
    unfold plus; equiv_simpl.
    intros [a_z|a_pos] [b_z|b_pos];
        [>contradiction|contradiction|contradiction|].
    right.
    destruct a_pos as [N1 a_pos].
    destruct b_pos as [N2 b_pos].
    exists (max N1 N2).
    intros i i_ge; cbn.
    specialize (a_pos i (trans (lmax N1 N2) i_ge)).
    specialize (b_pos i (trans (rmax N1 N2) i_ge)).
    apply le_pos_plus; assumption.
-   intros a b.
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
    unfold mult; equiv_simpl.
    intros [a_z|a_pos] [b_z|b_pos];
        [>contradiction|contradiction|contradiction|].
    right.
    destruct a_pos as [N1 a_pos].
    destruct b_pos as [N2 b_pos].
    exists (max N1 N2).
    intros i i_ge; cbn.
    specialize (a_pos i (trans (lmax N1 N2) i_ge)).
    specialize (b_pos i (trans (rmax N1 N2) i_ge)).
    apply le_mult; assumption.
-   intros a.
    equiv_get_value a.
    unfold mult; equiv_simpl.
    right; cbn.
    exists 0.
    intros i i_ge.
    apply square_pos.
-   unfold neg, one; cbn.
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
-   intros a.
    equiv_get_value a.
    unfold neg; equiv_simpl.
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
    exists (max N1 N2).
    intros i i_ge.
    specialize (a_nz n (trans (lmax N1 N2) n_ge)).
    specialize (a_cauchy i n (trans (rmax _ _) i_ge) (trans (rmax _ _) n_ge)).
    rewrite abs_neg_eq in a_nz by apply a_neg.
    apply (le_lt_trans (abs_le_pos _)) in a_cauchy.
    pose proof (lt_le_trans a_cauchy a_nz) as ltq.
    rewrite <- lt_plus_a_0_ab_b in ltq.
    apply neg_pos.
    apply ltq.
Qed.

Definition real_order := cone_order.
Definition real_le_connex := cone_le_connex.
Definition real_le_antisym := cone_le_antisym.
Definition real_le_trans := cone_le_transitive.
Definition real_le_lplus := cone_le_lplus.
Definition real_le_mult := cone_le_mult.
