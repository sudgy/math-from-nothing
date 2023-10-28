Require Import init.

Require Import set.
Require Import mult_ring.
Require Export fraction_base.
Require Export plus_group.

Section FractionPlus.

Context U `{OrderedDomainClass U}.

Local Infix "~" := (eq_equal (frac_equiv U)).

Let frac_plus_base (a b : frac_base U) :=
    (fst a * [snd b|] + fst b * [snd a|],
     [[snd a|] * [snd b|] | mult_nz _ _ [|snd a] [|snd b]]) : frac_base U.

Local Infix "⊕" := frac_plus_base.

Lemma frac_plus_wd : ∀ a b c d, a ~ b → c ~ d → a ⊕ c ~ b ⊕ d.
Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd.
    destruct a2 as [a2 a2_nz], b2 as [b2 b2_nz],
             c2 as [c2 c2_nz], d2 as [d2 d2_nz].
    cbn in *.
    unfold frac_eq in *.
    cbn in *.
    do 2 rewrite rdist.
    apply lrplus.
    -   rewrite mult_4.
        rewrite ab.
        rewrite (mult_comm c2 d2).
        apply mult_4.
    -   rewrite (mult_comm b2 d2).
        rewrite mult_4.
        rewrite cd.
        rewrite (mult_comm a2 b2).
        rewrite mult_4.
        rewrite (mult_comm c2 a2).
        reflexivity.
Qed.

Local Instance frac_plus : Plus (frac_type U) := {
    plus := binary_op (binary_self_wd frac_plus_wd)
}.

Local Instance frac_plus_comm : PlusComm (frac_type U).
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold plus; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite plus_comm.
    apply lmult.
    apply mult_comm.
Qed.

Local Instance frac_plus_assoc : PlusAssoc (frac_type U).
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold plus; equiv_simpl.
    unfold frac_eq; cbn.
    do 6 rewrite mult_assoc.
    do 3 apply rmult.
    do 2 rewrite rdist.
    rewrite <- plus_assoc.
    apply lplus.
    do 4 rewrite <- mult_assoc.
    do 2 rewrite (mult_comm [a2|]).
    reflexivity.
Qed.

Local Instance frac_zero : Zero (frac_type U) := {
    zero := to_frac U 0
}.

Local Instance frac_plus_lid : PlusLid (frac_type U).
Proof.
    split.
    intros a.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold zero, plus, to_frac; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite mult_lanni.
    rewrite plus_lid.
    rewrite mult_lid, mult_rid.
    reflexivity.
Qed.

Local Notation "⊖ a" := (-fst a, snd a) (at level 35, right associativity).

Lemma frac_neg_wd : ∀ a b, a ~ b → ⊖a ~ ⊖b.
Proof.
    intros [a1 a2] [b1 b2].
    cbn.
    unfold frac_eq; cbn.
    intros eq.
    do 2 rewrite mult_lneg.
    apply f_equal.
    exact eq.
Qed.

Global Instance frac_neg : Neg (frac_type U) := {
    neg := unary_op (unary_self_wd frac_neg_wd);
}.

Local Instance frac_plus_linv : PlusLinv (frac_type U).
Proof.
    split.
    intros a.
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

Local Instance to_frac_plus : HomomorphismPlus (to_frac U).
Proof.
    split.
    intros a b.
    unfold to_frac, plus at 2; equiv_simpl.
    unfold frac_eq; cbn.
    do 5 rewrite mult_rid.
    reflexivity.
Qed.

End FractionPlus.
