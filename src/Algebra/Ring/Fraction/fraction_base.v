Require Import init.

Require Export set.
Require Export domain_category.

Section FractionEquiv.

Context U `{OrderedFieldClass U}.

Definition frac_base := (U * set_type (λ x : U, 0 ≠ x))%type.

Definition frac_eq (a b : frac_base)
    := fst a * [snd b|] = fst b * [snd a|].
Local Infix "~" := frac_eq.

Local Instance frac_eq_reflexive : Reflexive frac_eq.
Proof.
    split.
    intros x.
    unfold frac_eq.
    reflexivity.
Qed.

Local Instance frac_eq_symmetric : Symmetric frac_eq.
Proof.
    split.
    unfold frac_eq.
    intros x y eq.
    symmetry.
    exact eq.
Qed.

Local Instance frac_eq_transitive : Transitive frac_eq.
Proof.
    split.
    unfold frac_eq.
    intros [x1 x2] [y1 y2] [z1 z2] eq1 eq2.
    destruct x2 as [x2 x2_nz], y2 as [y2 y2_nz], z2 as [z2 z2_nz].
    cbn in *.
    apply mult_lcancel with y2; [>exact y2_nz|].
    do 2 rewrite mult_assoc.
    do 2 rewrite (mult_comm y2).
    rewrite eq1, <- eq2.
    do 2 rewrite <- mult_assoc.
    apply lmult.
    apply mult_comm.
Qed.

Definition frac_equiv := make_equiv _
    frac_eq_reflexive frac_eq_symmetric frac_eq_transitive.

Definition to_frac (a : U)
    := to_equiv frac_equiv (a, [1|not_trivial_one]).

Local Instance to_frac_inj : Injective to_frac.
Proof.
    split.
    intros a b eq.
    unfold to_frac in eq.
    equiv_simpl in eq.
    unfold frac_eq in eq; cbn in eq.
    do 2 rewrite mult_rid in eq.
    exact eq.
Qed.

#[refine]
Local Instance frac_not_trivial : NotTrivial (equiv_type frac_equiv) :={
    not_trivial_a := to_frac 0;
    not_trivial_b := to_frac 1;
}.
Proof.
    unfold to_frac; equiv_simpl.
    unfold frac_eq; cbn.
    do 2 rewrite mult_rid.
    exact not_trivial_one.
Qed.

End FractionEquiv.

Notation "'frac_type' U" := (equiv_type (frac_equiv U)) (at level 1).
