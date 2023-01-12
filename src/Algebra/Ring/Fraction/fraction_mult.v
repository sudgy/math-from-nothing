Require Import init.

Require Import set.
Require Export mult_field.

Require Export fraction_base.
Require Import fraction_plus.

Section FractionMult.

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

Local Infix "~" := (eq_equal (frac_equiv U)).

Let frac_mult_base (a b : frac_base U) :=
    (fst a * fst b, [[snd a|] * [snd b|] | mult_nz _ _ [|snd a] [|snd b]])
    : frac_base U.

Local Infix "⊗" := frac_mult_base.

Lemma frac_mult_wd : ∀ a b c d, a ~ b → c ~ d → a ⊗ c ~ b ⊗ d.
Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] eq1 eq2.
    cbn in *.
    unfold frac_eq in *.
    cbn in *.
    rewrite <- mult_assoc.
    rewrite (mult_assoc c1).
    rewrite (mult_comm c1).
    do 2 rewrite mult_assoc.
    rewrite eq1.
    do 3 rewrite <- mult_assoc.
    apply lmult.
    rewrite eq2.
    do 2 rewrite mult_assoc.
    apply rmult.
    apply mult_comm.
Qed.

Local Instance frac_mult : Mult (frac U) := {
    mult := binary_self_op frac_mult_wd;
}.

Local Program Instance frac_mult_comm : MultComm (frac U).
Next Obligation.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold mult; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite (mult_comm a1).
    rewrite (mult_comm [b2|]).
    reflexivity.
Qed.

Local Program Instance frac_mult_assoc : MultAssoc (frac U).
Next Obligation.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold mult; equiv_simpl.
    unfold frac_eq; cbn.
    do 5 rewrite mult_assoc.
    reflexivity.
Qed.

Local Existing Instance frac_plus.

Local Program Instance frac_ldist : Ldist (frac U).
Next Obligation.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold plus, mult; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite ldist.
    do 2 rewrite rdist.
    apply lrplus.
    -   rewrite (mult_comm [a2|] [c2|]) at 2.
        repeat rewrite <- mult_assoc.
        do 4 apply lmult.
        do 2 rewrite mult_assoc.
        apply rmult.
        apply mult_comm.
    -   rewrite (mult_comm [a2|] [b2|]) at 2.
        repeat rewrite <- mult_assoc.
        do 4 apply lmult.
        do 2 rewrite mult_assoc.
        apply rmult.
        apply mult_comm.
Qed.

Local Instance frac_one : One (frac U) := {
    one := to_frac U 1
}.

Local Program Instance frac_mult_lid : MultLid (frac U).
Next Obligation.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold one; cbn.
    unfold to_frac, mult; equiv_simpl.
    unfold frac_eq; cbn.
    do 2 rewrite mult_lid.
    reflexivity.
Qed.

Let frac_div_base (a : frac_base U) :=
    match (strong_excluded_middle (0 = fst a)) with
    | strong_or_left _ => a
    | strong_or_right H => ([snd a|], [fst a | H])
    end.

Local Notation "⊘ a" := (frac_div_base a).

Lemma frac_div_wd : ∀ a b, a ~ b → ⊘a ~ ⊘b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    destruct a2 as [a2 a2_nz], b2 as [b2 b2_nz].
    cbn in *.
    unfold frac_eq in *; cbn in *.
    unfold frac_div_base; cbn.
    destruct (strong_excluded_middle (0 = a1)) as [a1_z|a1_nz].
    all: destruct (strong_excluded_middle (0 = b1)) as [b1_z|b1_nz].
    all: cbn.
    -   exact eq.
    -   subst a1.
        rewrite mult_lanni in eq.
        rewrite <- (mult_ranni b1) in eq.
        apply mult_lcancel in eq; [>|exact b1_nz].
        contradiction.
    -   subst b1.
        rewrite mult_lanni in eq.
        rewrite <- (mult_ranni a1) in eq.
        apply mult_lcancel in eq; [>|exact a1_nz].
        symmetry in eq; contradiction.
    -   rewrite mult_comm.
        rewrite <- eq.
        apply mult_comm.
Qed.

Local Instance frac_div : Div (frac U) := {
    div := unary_self_op frac_div_wd;
}.

Local Existing Instance frac_zero.

Local Program Instance frac_mult_linv : MultLinv (frac U).
Next Obligation.
    rename H9 into nz.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold zero in nz; cbn in nz.
    unfold to_frac in nz; equiv_simpl in nz.
    unfold frac_eq in nz; cbn in nz.
    rewrite mult_lanni, mult_rid in nz.
    unfold one; cbn.
    unfold to_frac, div, mult; equiv_simpl.
    unfold frac_eq; cbn.
    unfold frac_div_base; cbn.
    destruct (strong_excluded_middle (0 = a1)) as [C0|C0]; [>contradiction|].
    cbn; clear C0.
    rewrite mult_lid, mult_rid.
    apply mult_comm.
Qed.

Local Program Instance rat_not_trivial_class : NotTrivial (frac U) := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Next Obligation.
    unfold zero, one; cbn.
    unfold to_frac; equiv_simpl.
    unfold frac_eq; cbn.
    do 2 rewrite mult_rid.
    apply not_trivial_one.
Qed.

Theorem to_frac_mult : ∀ a b, to_frac U (a * b) = to_frac U a * to_frac U b.
Proof.
    intros a b.
    unfold mult at 2, to_frac; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem to_frac_one : to_frac U 1 = 1.
Proof.
    reflexivity.
Qed.

End FractionMult.
