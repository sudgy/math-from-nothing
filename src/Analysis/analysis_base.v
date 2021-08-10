Require Import init.

Require Export real.
Require Import order_abs.

#[universes(template)]
Class Metric U := {
    d : U → U → real;
    d_ind : ∀ x y, 0 = d x y ↔ x = y;
    d_sym : ∀ x y, d x y = d y x;
    d_tri : ∀ x y z, d x z <= d x y + d y z;
}.

(* begin hide *)
Section MetricBase.

Context {U} `{Metric U}.
(* end hide *)

Theorem d_zero : ∀ x, d x x = 0.
    intros x.
    symmetry.
    rewrite d_ind.
    reflexivity.
Qed.

Theorem d_pos : ∀ x y, 0 <= d x y.
    intros x y.
    pose proof (d_tri x y x) as eq.
    rewrite d_zero in eq.
    rewrite (d_sym y x) in eq.
    rewrite <- (mult_lid (d x y)) in eq.
    rewrite <- rdist in eq.
    apply le_lmult_pos with (div 2) in eq.
    2: apply div_pos; exact two_pos.
    rewrite mult_ranni in eq.
    rewrite mult_assoc, mult_linv, mult_lid in eq by apply two_pos.
    exact eq.
Qed.

Theorem d_neq_pos : ∀ x y, x ≠ y → 0 < d x y.
    intros x y neq.
    split.
    -   apply d_pos.
    -   intro contr.
        rewrite d_ind in contr.
        contradiction.
Qed.

Theorem d_reverse_tri : ∀ x y z, |d x y - d x z| <= d y z.
    intros x y z.
    apply abs_le.
    split.
    -   apply le_plus_lcancel with (-d x y).
        rewrite plus_assoc, plus_linv, plus_lid.
        rewrite <- neg_plus.
        apply le_neg.
        apply d_tri.
    -   apply le_plus_rcancel with (d x z).
        rewrite <- plus_assoc, plus_linv, plus_rid.
        rewrite plus_comm.
        rewrite (d_sym y z).
        apply d_tri.
Qed.

(* begin hide *)
End MetricBase.
(* end hide *)

Section AbsMetric.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    UA : AbsoluteValue U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    @Ldist U UP UM,
    @Rdist U UP UM,
    @MultLid U UM UO,
    @MultRid U UM UO,
    @NotTrivial U UZ UO,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP
}.

Program Instance abs_metric : Metric U := {
    d a b := |a - b|
}.
Next Obligation.
    split.
    -   intro eq.
        apply (abs_def (x - y)) in eq.
        symmetry in eq.
        apply plus_lrneg_eq.
        exact eq.
    -   intro eq.
        rewrite eq.
        rewrite plus_rinv.
        exact abs_zero.
Qed.
Next Obligation.
    apply abs_minus.
Qed.
Next Obligation.
    rewrite <- (plus_rlinv x y) at 1.
    rewrite <- plus_assoc.
    apply abs_tri.
Qed.

End AbsMetric.

Definition real_metric := (abs_metric (U := real)).

Theorem metric_eq {U} : ∀ M1 M2 : Metric U,
        (∀ a b, @d U M1 a b = @d U M2 a b) → M1 = M2.
    intros [d1 d1_ind d1_sym d1_tri] [d2 d2_ind d2_sym d2_tri] d_eq.
    assert (d1 = d2) as eq.
    {
        unfold d in d_eq; cbn in d_eq.
        apply functional_ext.
        intros x.
        apply functional_ext.
        intros y.
        apply d_eq.
    }
    subst.
    rewrite (proof_irrelevance d1_ind d2_ind).
    rewrite (proof_irrelevance d1_sym d2_sym).
    rewrite (proof_irrelevance d1_tri d2_tri).
    reflexivity.
Qed.
