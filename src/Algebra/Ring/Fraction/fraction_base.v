Require Import init.

Require Import set.
Require Import mult_ring.

Section FractionEquiv.

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
    NotTrivial U
}.

Definition frac_base := (U * set_type (λ x : U, 0 ≠ x))%type.

Definition frac_eq (a b : frac_base)
    := fst a * [snd b|] = fst b * [snd a|].
Local Infix "~" := frac_eq.

Local Program Instance frac_eq_reflexive : Reflexive frac_eq.
Next Obligation.
    unfold frac_eq.
    reflexivity.
Qed.

Local Program Instance frac_eq_symmetric : Symmetric frac_eq.
Next Obligation.
    unfold frac_eq in *.
    symmetry.
    assumption.
Qed.

Local Program Instance frac_eq_transitive : Transitive frac_eq.
Next Obligation.
    unfold frac_eq in *.
    rename H9 into eq1, H10 into eq2.
    destruct x as [x1 x2], y as [y1 y2], z as [z1 z2].
    destruct x2 as [x2 x2_nz], y2 as [y2 y2_nz], z2 as [z2 z2_nz].
    cbn in *.
    apply mult_lcancel with y2; [>exact y2_nz|].
    rewrite mult_assoc.
    rewrite (mult_comm y2 x1).
    rewrite eq1.
    rewrite <- mult_assoc.
    rewrite (mult_comm x2 z2).
    do 2 rewrite mult_assoc.
    apply rmult.
    rewrite eq2.
    apply mult_comm.
Qed.

Definition frac_equiv := make_equiv _
    frac_eq_reflexive frac_eq_symmetric frac_eq_transitive.

Definition to_frac (a : U)
    := to_equiv frac_equiv (a, [1|not_trivial_one]).

Theorem to_frac_eq : ∀ a b, to_frac a = to_frac b → a = b.
Proof.
    intros a b eq.
    unfold to_frac in eq.
    equiv_simpl in eq.
    unfold frac_eq in eq; cbn in eq.
    do 2 rewrite mult_rid in eq.
    exact eq.
Qed.

Local Program Instance frac_not_trivial : NotTrivial (equiv_type frac_equiv) := {
    not_trivial_a := to_frac 0;
    not_trivial_b := to_frac 1;
}.
Next Obligation.
    unfold to_frac; equiv_simpl.
    intros contr.
    unfold frac_eq in contr; cbn in contr.
    do 2 rewrite mult_rid in contr.
    exact (not_trivial_one contr).
Qed.

End FractionEquiv.

Notation "'frac' U" := (equiv_type (frac_equiv U)) (at level 1).
