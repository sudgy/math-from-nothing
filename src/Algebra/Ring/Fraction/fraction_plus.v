Require Import init.

Require Import set.
Require Import mult_ring.
Require Export fraction_base.
Require Export plus_group.

Section FractionPlus.

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

Let frac_plus_base (a b : frac_base U) :=
    (fst a * [snd b|] + fst b * [snd a|],
     [[snd a|] * [snd b|] | mult_nz _ _ [|snd a] [|snd b]]) : frac_base U.

Local Infix "⊕" := frac_plus_base.

Lemma frac_plus_wd : ∀ a b c d, a ~ b → c ~ d → a ⊕ c ~ b ⊕ d.
Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd.
    destruct a2 as [a2 a2_nz], b2 as [b2 b2_nz], c2 as [c2 c2_nz],
             d2 as [d2 d2_nz].
    cbn in *.
    unfold frac_eq in *.
    cbn in *.
    do 2 rewrite rdist.
    apply lrplus.
    -   rewrite <- mult_assoc.
        rewrite (mult_comm c2).
        do 2 rewrite mult_assoc.
        rewrite ab.
        rewrite mult_assoc.
        apply rmult.
        do 2 rewrite <- mult_assoc.
        apply lmult.
        apply mult_comm.
    -   rewrite <- mult_assoc.
        rewrite (mult_comm a2).
        rewrite (mult_comm b2).
        do 2 rewrite mult_assoc.
        rewrite cd.
        do 3 rewrite <- mult_assoc.
        apply lmult.
        rewrite mult_comm.
        symmetry; apply mult_assoc.
Qed.

Local Instance frac_plus : Plus (frac U) := {
    plus := binary_op (binary_self_wd frac_plus_wd)
}.

Local Program Instance frac_plus_comm : PlusComm (frac U).
Next Obligation.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold plus; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite plus_comm.
    apply lmult.
    apply mult_comm.
Qed.

Local Program Instance frac_plus_assoc : PlusAssoc (frac U).
Next Obligation.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold plus; equiv_simpl.
    unfold frac_eq; cbn.
    repeat rewrite mult_assoc.
    do 3 apply rmult.
    do 2 rewrite rdist.
    rewrite <- plus_assoc.
    apply lplus.
    do 4 rewrite <- mult_assoc.
    apply lrplus.
    -   apply lmult.
        apply mult_comm.
    -   apply lmult.
        apply mult_comm.
Qed.

Local Instance frac_zero : Zero (frac U) := {
    zero := to_frac U 0
}.

Local Program Instance frac_plus_lid : PlusLid (frac U).
Next Obligation.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold zero; cbn.
    unfold to_frac, plus; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite mult_lanni.
    rewrite plus_lid.
    rewrite mult_lid, mult_rid.
    reflexivity.
Qed.

Local Notation "⊖ a" := (-fst a, snd a) (at level 35, right associativity).

Lemma frac_neg_wd : ∀ a b, a ~ b → ⊖a ~ ⊖b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    cbn in *.
    unfold frac_eq in *.
    cbn in *.
    do 2 rewrite mult_lneg.
    apply f_equal.
    exact eq.
Qed.

Global Instance frac_neg : Neg (frac U) := {
    neg := unary_op (unary_self_wd frac_neg_wd);
}.

Local Program Instance frac_plus_linv : PlusLinv (frac U).
Next Obligation.
    equiv_get_value a.
    destruct a as [a b].
    unfold zero; cbn.
    unfold neg, plus, to_frac; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite mult_lneg.
    rewrite plus_linv.
    do 2 rewrite mult_lanni.
    reflexivity.
Qed.

Theorem to_frac_plus : ∀ a b, to_frac U (a + b) = to_frac U a + to_frac U b.
Proof.
    intros a b.
    unfold to_frac, plus at 2; equiv_simpl.
    unfold frac_eq; cbn.
    do 5 rewrite mult_rid.
    reflexivity.
Qed.

Theorem to_frac_neg : ∀ a, to_frac U (-a) = -to_frac U a.
Proof.
    intros a.
    unfold to_frac, neg at 2; equiv_simpl.
    unfold frac_eq; cbn.
    reflexivity.
Qed.

Theorem to_frac_zero : to_frac U 0 = 0.
Proof.
    reflexivity.
Qed.

End FractionPlus.
