Require Import init.

Require Export cauchy_real_base.

Lemma cauchy_plus : ∀ a b : real_base, cauchy_seq (λ n, r_seq a n + r_seq b n).
Proof.
    intros [a a_cauchy] [b b_cauchy]; cbn.
    intros ε ε_pos.
    pose proof (half_pos ε_pos) as ε2_pos.
    specialize (a_cauchy _ ε2_pos) as [N1 a_cauchy].
    specialize (b_cauchy _ ε2_pos) as [N2 b_cauchy].
    exists (max N1 N2).
    intros i j i_ge j_ge.
    specialize (a_cauchy i j (trans (lmax _ _) i_ge) (trans (lmax _ _) j_ge)).
    specialize (b_cauchy i j (trans (rmax _ _) i_ge) (trans (rmax _ _) j_ge)).
    pose proof (lt_lrplus a_cauchy b_cauchy) as ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans (abs_tri _ _)) in ltq.
    applys_eq ltq.
    apply f_equal.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply plus_comm.
Qed.

Lemma cauchy_neg : ∀ a : real_base, cauchy_seq (λ n, -r_seq a n).
Proof.
    intros [a a_cauchy] ε ε_pos; cbn.
    specialize (a_cauchy ε ε_pos) as [N a_cauchy].
    exists N.
    intros i j.
    rewrite abs_minus.
    rewrite neg_neg, plus_comm.
    apply a_cauchy.
Qed.

Notation "a ⊕ b" := (make_real _ (cauchy_plus a b)) : real_scope.
Notation "⊖ a" := (make_real _ (cauchy_neg a)) : real_scope.

Open Scope real_scope.

Lemma real_plus_wd : ∀ a b c d, a ~ b → c ~ d → a ⊕ c ~ b ⊕ d.
Proof.
    intros [a a_cauchy] [b b_cauchy] [c c_cauchy] [d d_cauchy] ab cd ε ε_pos.
    cbn in *.
    pose proof (half_pos ε_pos) as ε2_pos.
    specialize (ab _ ε2_pos) as [N1 ab].
    specialize (cd _ ε2_pos) as [N2 cd].
    exists (max N1 N2).
    intros i i_ge.
    specialize (ab i (trans (lmax N1 N2) i_ge)).
    specialize (cd i (trans (rmax N1 N2) i_ge)).
    pose proof (lt_lrplus ab cd) as ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans (abs_tri _ _)) in ltq.
    applys_eq ltq.
    apply f_equal.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply plus_comm.
Qed.

Lemma real_neg_wd : ∀ a b, a ~ b → ⊖a ~ ⊖b.
Proof.
    intros [a a_cauchy] [b b_cauchy] ab ε ε_pos; cbn in *.
    specialize (ab ε ε_pos) as [N ab].
    exists N.
    intros n.
    rewrite abs_minus.
    rewrite neg_neg, plus_comm.
    apply ab.
Qed.

Global Instance real_plus : Plus real := {
    plus := binary_op (binary_self_wd real_plus_wd)
}.

Global Instance real_zero : Zero real := {
    zero := rat_to_real 0
}.

Global Instance real_neg : Neg real := {
    neg := unary_op (unary_self_wd real_neg_wd)
}.

Global Instance real_plus_assoc : PlusAssoc real.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold plus; equiv_simpl.
    intros ε ε_pos.
    exists 0.
    intros i i_ge.
    rewrite plus_assoc.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Global Instance real_plus_comm : PlusComm real.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold plus; equiv_simpl.
    intros ε ε_pos.
    exists 0.
    intros i i_ge.
    rewrite (plus_comm (r_seq a i)).
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Global Instance real_plus_lid : PlusLid real.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold plus, zero; equiv_simpl.
    intros ε ε_pos.
    exists 0.
    intros i i_ge.
    rewrite plus_lid.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Global Instance real_plus_linv : PlusLinv real.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold plus, neg, zero; cbn.
    unfold rat_to_real; equiv_simpl.
    intros ε ε_pos.
    exists 0.
    intros i i_ge.
    rewrite plus_linv.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.
