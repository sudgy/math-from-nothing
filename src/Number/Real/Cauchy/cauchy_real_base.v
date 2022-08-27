Require Import init.

Require Export rat.
Require Export order_self_abs.
Require Export order_minmax.
Require Export set.

Notation "| a |" := (abs a) (at level 30).

Declare Scope real_scope.
Delimit Scope real_scope with real.

Definition cauchy_seq (a : nat → rat) :=
    ∀ ε, 0 < ε → ∃ N, ∀ i j, N <= i → N <= j → |a i - a j| < ε.

Record real_base := make_real {
    r_seq : nat → rat;
    r_cauchy : cauchy_seq r_seq;
}.

Section RealEquiv.

Let real_eq (a b : real_base) :=
    ∀ ε, 0 < ε → ∃ N, ∀ i, N <= i → |r_seq a i - r_seq b i| < ε.

Local Infix "~" := real_eq.

Instance real_eq_reflexive : Reflexive real_eq.
Proof.
    split.
    intros a ε ε_pos.
    exists 0.
    intros i i_pos.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Instance real_eq_symmetric : Symmetric real_eq.
Proof.
    split.
    intros a b ab ε ε_pos.
    specialize (ab ε ε_pos) as [N ab].
    exists N.
    intros i i_ge.
    rewrite abs_minus.
    exact (ab i i_ge).
Qed.

Instance real_eq_transitive : Transitive real_eq.
Proof.
    split.
    intros a b c ab bc ε ε_pos.
    pose proof (half_pos ε_pos) as ε2_pos.
    specialize (ab _ ε2_pos) as [N1 ab].
    specialize (bc _ ε2_pos) as [N2 bc].
    exists (max N1 N2).
    intros i i_ge.
    specialize (ab i (trans (lmax N1 N2) i_ge)).
    specialize (bc i (trans (rmax N1 N2) i_ge)).
    pose proof (lt_lrplus ab bc) as ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans2 ltq).
    apply (trans2 (abs_tri _ _)).
    rewrite plus_assoc.
    rewrite plus_rlinv.
    apply refl.
Qed.

End RealEquiv.

Definition real_equiv := make_equiv _
    real_eq_reflexive real_eq_symmetric real_eq_transitive.
Notation "a ~ b" := (eq_equal real_equiv a b) : int_scope.

Notation "'real'" := (equiv_type real_equiv).

Lemma rat_to_real_cauchy : ∀ q : rat, cauchy_seq (λ _, q).
Proof.
    intros q ε ε_pos.
    exists 0.
    intros i j i_ge j_ge.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Definition rat_to_real (q : rat) :=
    to_equiv_type real_equiv (make_real _ (rat_to_real_cauchy q)).
