Require Import init.

Require Export order_mult.
Require Export real.
Require Export linear_base.

#[universes(template)]
Class AbsoluteValue U := {
    abs : U → real;
}.
Notation "| a |" := (abs a) (at level 30).
Arguments abs : simpl never.

Global Instance real_abs : AbsoluteValue real := {
    abs a := If 0 ≤ a then a else (-a)
}.

Class AbsDefinite U `{AbsoluteValue U, Zero U} := {
    abs_def : ∀ x : U, 0 = |x| ↔ 0 = x
}.
Class AbsPositive U `{AbsoluteValue U} := {
    abs_pos : ∀ x : U, 0 ≤ |x|
}.
Class AbsMult U `{AbsoluteValue U, Mult U} := {
    abs_mult : ∀ a b : U, |a * b| = |a| * |b|
}.
Class AbsCauchySchwarz U `{AbsoluteValue U, Mult U} := {
    abs_cs : ∀ a b : U, |a * b| ≤ |a| * |b|
}.
Class AbsTriangle U `{AbsoluteValue U, Plus U} := {
    abs_tri : ∀ a b : U, |a + b| ≤ |a| + |b|;
}.
Class AbsScalar U `{AbsoluteValue U, ScalarMult real U} := {
    abs_scalar : ∀ (a : real) (v : U), |a · v| = |a| * |v|
}.
Class AbsNeg U `{AbsoluteValue U, Neg U} := {
    abs_neg : ∀ (a : U), | -a| = |a|
}.
Definition cauchy_schwarz {U} `{AbsoluteValue U} f
    := ∀ u v, |f u v| ≤ |u| * |v|.

Class NormedSpaceClass V `{
    MG : AbelianGroupClass V,
    SM : ScalarMult real V,
    SMC : @ScalarComp real V real_mult SM,
    SME : @ScalarId real V real_one SM,
    SML : @ScalarLdist real V UP SM,
    SMR : @ScalarRdist real V real_plus UP SM,
    VA : AbsoluteValue V,
    VAD : @AbsDefinite V VA UZ,
    VAP : @AbsPositive V VA,
    VAS : @AbsScalar V VA SM,
    VAT : @AbsTriangle V VA UP
}.

(* begin hide *)
Section Abs.

Context {U : Type} `{
    OrderedFieldClass U,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsPositive U UA,
    @AbsMult U UA UM,
    @AbsTriangle U UA UP,
    @AbsNeg U UA UN
}.
(* end hide *)
Theorem abs_zero : 0 = |0|.
Proof.
    apply abs_def.
    reflexivity.
Qed.

Theorem abs_nz : ∀ x, 0 ≠ |x| ↔ 0 ≠ x.
Proof.
    intros x.
    split; intros neq eq.
    -   apply abs_def in eq.
        contradiction.
    -   apply abs_def in eq.
        contradiction.
Qed.

Theorem abs_pos2 : ∀ {x}, 0 ≠ x → 0 < |x|.
Proof.
    intros x x_nz.
    split.
    -   apply abs_pos.
    -   rewrite abs_def.
        exact x_nz.
Qed.

Theorem abs_one : |1| = 1.
Proof.
    pose proof (Logic.eq_refl (|1 * 1|)) as eq.
    rewrite mult_rid in eq at 2.
    rewrite abs_mult in eq.
    rewrite <- (mult_rid (|1|)) in eq at 3.
    apply mult_lcancel in eq.
    -   exact eq.
    -   intro contr.
        apply abs_def in contr.
        apply not_trivial_one in contr.
        exact contr.
Qed.

Theorem abs_minus_one : | -(1)| = 1.
Proof.
    pose proof (Logic.eq_refl (| -(1) * -(1)|)) as eq.
    rewrite abs_mult in eq at 1.
    rewrite mult_lneg, mult_rneg, neg_neg in eq.
    rewrite mult_lid in eq.
    rewrite abs_one in eq.
    apply square_one_one in eq as [eq|eq].
    -   exact eq.
    -   pose proof (abs_pos (-(1))) as leq.
        rewrite eq in leq.
        apply le_neg in leq.
        rewrite neg_neg, neg_zero in leq.
        pose proof (le_lt_trans leq one_pos) as [C0 C1]; contradiction.
Qed.

Theorem abs_minus : ∀ a b, |a - b| = |b - a|.
Proof.
    intros a b.
    rewrite <- abs_neg.
    rewrite neg_plus, neg_neg.
    rewrite plus_comm.
    reflexivity.
Qed.

Theorem abs_div : ∀ a, 0 ≠ a → /|a| = |/a|.
Proof.
    intros a a_nz.
    pose proof (rand (abs_nz a) a_nz) as a_nz2.
    apply mult_rcancel with (|a|).
    1: exact a_nz2.
    rewrite mult_linv by exact a_nz2.
    rewrite <- abs_mult.
    rewrite mult_linv by exact a_nz.
    rewrite abs_one.
    reflexivity.
Qed.

Global Program Instance abs_mult_neg : AbsNeg U.
Next Obligation.
    rewrite <- (mult_lid a).
    rewrite <- mult_lneg.
    do 2 rewrite abs_mult.
    apply f_equal2; try reflexivity.
    rewrite abs_one.
    apply abs_minus_one.
Qed.
Global Program Instance abs_mult_cs : AbsCauchySchwarz U.
Next Obligation.
    rewrite abs_mult.
    apply refl.
Qed.
(* begin hide *)
End Abs.

Section RealAbs.

Global Program Instance real_abs_pos : AbsPositive real.
Next Obligation.
    unfold abs; cbn.
    case_if.
    exact l.
    rewrite nle_lt in n.
    apply lt_neg in n.
    rewrite neg_zero in n.
    apply n.
Qed.
Global Program Instance real_abs_def : AbsDefinite real.
Next Obligation.
    unfold abs; cbn.
    case_if.
    -   reflexivity.
    -   clear n.
        split; intro eq.
        +   apply neg_eq in eq.
            rewrite neg_zero, neg_neg in eq.
            exact eq.
        +   subst.
            symmetry; apply neg_zero.
Qed.
Global Program Instance real_abs_mult : AbsMult real.
Next Obligation.
    unfold abs; cbn.
    repeat case_if.
    -   reflexivity.
    -   rewrite nle_lt in n.
        classic_case (0 = a) as [a_z|a_nz].
        +   subst.
            do 2 rewrite mult_lanni.
            reflexivity.
        +   assert (0 < a) as a_pos by (split; assumption).
            apply lt_lmult_pos with a in n.
            2: exact a_pos.
            rewrite mult_ranni in n.
            pose proof (lt_le_trans n l) as [C0 C1]; contradiction.
    -   rewrite nle_lt in n.
        classic_case (0 = b) as [b_z|b_nz].
        +   subst.
            do 2 rewrite mult_ranni.
            reflexivity.
        +   assert (0 < b) as b_pos by (split; assumption).
            apply lt_rmult_pos with b in n.
            2: exact b_pos.
            rewrite mult_lanni in n.
            pose proof (lt_le_trans n l) as [C0 C1]; contradiction.
    -   rewrite mult_rneg, mult_lneg.
        rewrite neg_neg.
        reflexivity.
    -   pose proof (le_mult l l0).
        contradiction.
    -   rewrite mult_rneg.
        reflexivity.
    -   rewrite mult_lneg.
        reflexivity.
    -   rewrite nle_lt in n, n0, n1.
        apply lt_neg in n0, n1.
        rewrite neg_zero in n0, n1.
        pose proof (lt_mult n0 n1) as ltq.
        rewrite mult_lneg, mult_rneg, neg_neg in ltq.
        pose proof (trans n ltq) as [C0 C1]; contradiction.
Qed.
Global Program Instance real_abs_tri : AbsTriangle real.
Next Obligation.
    unfold abs; cbn.
    repeat case_if.
    -   apply refl.
    -   rewrite nle_lt in n.
        pose proof (land (lt_neg _ _) n) as b'_pos.
        rewrite neg_zero in b'_pos.
        apply lt_lplus with a in b'_pos.
        apply lt_lplus with a in n.
        rewrite plus_rid in n, b'_pos.
        apply (trans n b'_pos).
    -   rewrite nle_lt in n.
        pose proof (land (lt_neg _ _) n) as a'_pos.
        rewrite neg_zero in a'_pos.
        apply lt_rplus with b in a'_pos.
        apply lt_rplus with b in n.
        rewrite plus_lid in n, a'_pos.
        apply (trans n a'_pos).
    -   rewrite nle_lt in n, n0.
        pose proof (lt_lrplus n n0) as ltq.
        rewrite plus_lid in ltq.
        pose proof (land (lt_neg _ _) ltq) as ltq2.
        rewrite neg_plus in ltq2.
        rewrite neg_zero in ltq2.
        apply (trans ltq ltq2).
    -   pose proof (le_lrplus l l0) as leq.
        rewrite plus_lid in leq.
        pose proof (land (le_neg _ _) leq) as leq2.
        rewrite neg_zero in leq2.
        apply (trans leq2 leq).
    -   rewrite nle_lt in n, n0.
        rewrite <- (neg_neg a) at 2.
        rewrite <- neg_plus.
        rewrite <- le_neg.
        apply le_rplus.
        pose proof (land (le_neg _ _) l) as leq.
        rewrite neg_zero in leq.
        exact (trans leq l).
    -   rewrite nle_lt in n, n0.
        rewrite <- (neg_neg b) at 2.
        rewrite <- neg_plus.
        rewrite <- le_neg.
        apply le_lplus.
        pose proof (land (le_neg _ _) l) as leq.
        rewrite neg_zero in leq.
        exact (trans leq l).
    -   rewrite neg_plus.
        apply refl.
Qed.
(* end hide *)
Theorem abs_le_pos : ∀ a, a ≤ |a|.
Proof.
    intros a.
    unfold abs; cbn.
    case_if.
    -   apply refl.
    -   rewrite nle_lt in n.
        pose proof (land (lt_neg _ _) n) as ltq.
        rewrite neg_zero in ltq.
        apply (trans n ltq).
Qed.

Theorem abs_le_neg : ∀ a, -a ≤ |a|.
Proof.
    intros a.
    unfold abs; cbn.
    case_if.
    -   pose proof (land (le_neg _ _) l) as leq.
        rewrite neg_zero in leq.
        apply (trans leq l).
    -   apply refl.
Qed.

Theorem abs_le : ∀ a b, |a| ≤ b ↔ -b ≤ a ∧ a ≤ b.
Proof.
    intros a b.
    unfold abs; cbn.
    case_if; split.
    -   intros leq; split; try assumption.
        apply le_neg in leq.
        pose proof (land (le_neg _ _) l) as leq2.
        rewrite neg_zero in leq2.
        exact (trans leq (trans leq2 l)).
    -   intros [C0 C1]; assumption.
    -   intros leq; split.
        +   apply le_neg in leq.
            rewrite neg_neg in leq.
            exact leq.
        +   rewrite nle_lt in n.
            pose proof (land (lt_neg _ _) n) as ltq.
            rewrite neg_zero in ltq.
            apply (lt_le_trans (trans n ltq) leq).
    -   intros [leq1 leq2].
        apply le_neg in leq1.
        rewrite neg_neg in leq1.
        exact leq1.
Qed.

Theorem abs_lt : ∀ a b, |a| < b ↔ -b < a ∧ a < b.
Proof.
    intros a b.
    split.
    -   intros [leq neq].
        apply abs_le in leq as [leq1 leq2].
        repeat split; try assumption; intro; subst.
        +   apply neq.
            rewrite abs_neg.
            unfold abs; cbn; case_if; try reflexivity.
            rewrite nle_lt in n.
            pose proof (le_lt_trans leq2 n) as ltq.
            apply lt_neg in ltq.
            rewrite neg_neg, neg_zero in ltq.
            pose proof (trans n ltq) as [C0 C1]; contradiction.
        +   apply neq.
            unfold abs; cbn; case_if; try reflexivity.
            rewrite nle_lt in n.
            pose proof (le_lt_trans leq1 n) as ltq.
            apply lt_neg in ltq.
            rewrite neg_neg, neg_zero in ltq.
            pose proof (trans n ltq) as [C0 C1]; contradiction.
    -   intros [[leq1 neq1] [leq2 neq2]].
        split.
        +   apply abs_le; split; assumption.
        +   intro contr; subst.
            unfold abs in *; cbn in *; case_if.
            *   contradiction.
            *   rewrite neg_neg in neq1.
                contradiction.
Qed.

Theorem abs_pos_eq : ∀ a, 0 ≤ a → |a| = a.
Proof.
    intros a a_pos.
    unfold abs; cbn.
    case_if.
    -   reflexivity.
    -   contradiction.
Qed.

Theorem abs_neg_eq : ∀ a, a ≤ 0 → |a| = -a.
Proof.
    intros a a_neg.
    rewrite <- abs_neg.
    apply abs_pos_eq.
    apply neg_pos.
    exact a_neg.
Qed.

(* begin hide *)
End RealAbs.

Section LinearAbs.

Context {U : Type} `{
    UP : Plus U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    UZ : Zero U,
    @PlusLid U UP UZ,
    @PlusRid U UP UZ,
    UN : Neg U,
    @PlusLinv U UP UZ UN,
    @PlusRinv U UP UZ UN,
    SM : ScalarMult real U,
    @ScalarId real U real_one SM,
    @ScalarRdist real U real_plus UP SM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsTriangle U UA UP,
    @AbsScalar U UA SM,
    @AbsPositive U UA
}.

(* end hide *)
Theorem abs_abs : ∀ x, | |x| | = |x|.
Proof.
    intros x.
    unfold abs at 1; cbn.
    case_if.
    -   reflexivity.
    -   exfalso; apply n.
        apply abs_pos.
Qed.
(* begin hide *)
Global Program Instance abs_scalar_neg : AbsNeg U.
Next Obligation.
    rewrite <- scalar_neg_one.
    rewrite abs_scalar.
    rewrite abs_minus_one.
    rewrite mult_lid.
    reflexivity.
Qed.

Global Program Instance abs_scalar_pos : AbsPositive U.
Next Obligation.
    pose proof (abs_tri x (-x)) as eq.
    rewrite abs_neg in eq.
    rewrite plus_rinv in eq.
    rewrite <- abs_zero in eq.
    apply le_rmult_pos with (/2) in eq.
    2: apply div_pos; exact two_pos.
    rewrite mult_lanni, rdist in eq.
    rewrite plus_half in eq.
    exact eq.
Qed.

End LinearAbs.
(* end hide *)
