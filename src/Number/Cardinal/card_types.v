Require Import init.

Require Import set.
Require Import card.
Require Import nat.
Require Import int.
Require Import rat.

Open Scope card_scope.

Section EquivCard.

Context {U : Type}.

Theorem equiv_card_le : ∀ E : equivalence U, |equiv_type E| ≤ |U|.
Proof.
    intros E.
    unfold le; equiv_simpl.
    exists from_equiv.
    split.
    intros a b eq.
    apply (f_equal (to_equiv E)) in eq.
    do 2 rewrite from_equiv_eq in eq.
    exact eq.
Qed.

End EquivCard.

Theorem int_size : |int| = |nat|.
Proof.
    apply antisym.
    -   apply (trans (equiv_card_le _)).
        rewrite card_mult_type.
        rewrite card_mult_idemp by apply refl.
        apply refl.
    -   unfold le; equiv_simpl.
        exists from_nat.
        exact from_nat_inj.
Qed.

Theorem rat_size : |rat| = |nat|.
Proof.
    apply antisym.
    -   apply (trans (equiv_card_le _)).
        rewrite card_mult_type.
        rewrite <- (card_mult_idemp (|nat|)) by apply refl.
        apply le_lrmult.
        +   rewrite int_size.
            apply refl.
        +   apply (trans (card_sub_le int (λ x, 0 ≠ x))).
            rewrite int_size.
            apply refl.
    -   unfold le; equiv_simpl.
        exists from_nat.
        apply from_nat_inj.
Qed.

Section DenseInfinite.

Context {U} `{TotalOrder U, @Dense U (strict le)}.

Theorem dense_open_infinite :
    ∀ a b, a < b → infinite (|set_type (open_interval a b)|).
Proof.
    intros a b ab.
    apply all_greater_inf_set.
    {
        pose proof (dense a b ab) as ex.
        exact ex.
    }
    intros [x [x_gt x_lt]]; cbn.
    pose proof (dense x b x_lt) as [y [y_gt y_lt]].
    exists [y|make_and (trans x_gt y_gt) y_lt]; cbn.
    exact y_gt.
Qed.

Theorem dense_closed_infinite :
    ∀ a b, a < b → infinite (|set_type (closed_interval a b)|).
Proof.
    intros a b ab.
    apply (trans (dense_open_infinite a b ab)).
    apply card_subs_le.
    intros x [x_ge x_lt].
    split.
    -   apply x_ge.
    -   apply x_lt.
Qed.

End DenseInfinite.

Section CardArch.

Context {U} `{OrderedFieldClass U, @Archimedean U UP UZ UO}.

Theorem arch_ordered_size : |U| ≤ 2 ^ |nat|.
Proof.
    rewrite <- rat_size.
    rewrite <- power_set_size.
    unfold le; equiv_simpl.
    exists (λ x : U, (λ q : rat, from_rat q < x)).
    cut (∀ a b : U, a ≤ b →
        ((λ q : rat, from_rat q < a) = (λ q : rat, from_rat q < b)
        → a = b)).
    {
        intros wlog.
        split.
        intros a b eq.
        destruct (connex a b) as [leq|leq].
        +   apply wlog; assumption.
        +   symmetry in eq.
            symmetry.
            apply wlog; assumption.
    }
    intros a b leq eq.
    classic_contradiction neq.
    pose proof (rat_dense_in_arch a b (make_and leq neq)) as [r [r_gt r_lt]].
    pose proof (func_eq _ _ eq r) as eq2.
    cbn in eq2.
    rewrite <- eq2 in r_lt.
    contradiction (irrefl _ (trans r_gt r_lt)).
Qed.

End CardArch.

Close Scope card_scope.
