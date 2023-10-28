Require Import init.

Require Import set.
Require Export mult_field.

Require Export fraction_base.
Require Export fraction_plus.

Section FractionMult.

Context U `{OrderedDomainClass U}.

Local Infix "~" := (eq_equal (frac_equiv U)).

Let frac_mult_base (a b : frac_base U) :=
    (fst a * fst b, [[snd a|] * [snd b|] | mult_nz _ _ [|snd a] [|snd b]])
    : frac_base U.

Local Infix "⊗" := frac_mult_base.

Lemma frac_mult_wd : ∀ a b c d, a ~ b → c ~ d → a ⊗ c ~ b ⊗ d.
Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2].
    cbn.
    unfold frac_eq in *; cbn.
    intros eq1 eq2.
    rewrite mult_4.
    rewrite eq1, eq2.
    apply mult_4.
Qed.

Local Instance frac_mult : Mult (frac_type U) := {
    mult := binary_op (binary_self_wd frac_mult_wd);
}.

Local Instance frac_mult_comm : MultComm (frac_type U).
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold mult; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite (mult_comm a1).
    rewrite (mult_comm [b2|]).
    reflexivity.
Qed.

Local Instance frac_mult_assoc : MultAssoc (frac_type U).
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold mult; equiv_simpl.
    unfold frac_eq; cbn.
    do 5 rewrite mult_assoc.
    reflexivity.
Qed.

Local Existing Instance frac_plus.

Local Instance frac_ldist : Ldist (frac_type U).
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold plus, mult; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite ldist.
    do 2 rewrite rdist.
    apply lrplus.
    -   rewrite (mult_4 [a2|]).
        rewrite (mult_comm [a2|] [c2|]).
        do 7 rewrite mult_assoc.
        reflexivity.
    -   rewrite (mult_4 [a2|]).
        rewrite (mult_comm [a2|] [b2|]).
        do 7 rewrite mult_assoc.
        reflexivity.
Qed.

Local Instance frac_one : One (frac_type U) := {
    one := to_frac U 1
}.

Local Instance frac_mult_lid : MultLid (frac_type U).
Proof.
    split.
    intros a.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold one; cbn.
    unfold to_frac, mult; equiv_simpl.
    unfold frac_eq; cbn.
    do 2 rewrite mult_lid.
    reflexivity.
Qed.

Let frac_div_base (a : frac_base U) :=
    IfH (0 = fst a) then λ _, a else λ H, ([snd a|], [fst a | H]).

Local Notation "⊘ a" := (frac_div_base a).

Lemma frac_div_wd : ∀ a b, a ~ b → ⊘a ~ ⊘b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    destruct a2 as [a2 a2_nz], b2 as [b2 b2_nz].
    cbn in *.
    unfold frac_eq in *; cbn in *.
    unfold frac_div_base; cbn.
    classic_case (0 = a1) as [a1_z|a1_nz].
    all: classic_case (0 = b1) as [b1_z|b1_nz].
    all: cbn.
    -   exact eq.
    -   subst a1.
        rewrite mult_lanni in eq.
        apply mult_zero in eq as [|]; contradiction.
    -   subst b1.
        rewrite mult_lanni in eq.
        symmetry in eq.
        apply mult_zero in eq as [|]; contradiction.
    -   rewrite mult_comm.
        rewrite <- eq.
        apply mult_comm.
Qed.

Local Instance frac_div : Div (frac_type U) := {
    div := unary_op (unary_self_wd frac_div_wd);
}.

Local Existing Instance frac_zero.

Local Instance frac_mult_linv : MultLinv (frac_type U).
Proof.
    split.
    intros a.
    equiv_get_value a.
    destruct a as [a1 a2].
    unfold zero, one; cbn.
    unfold to_frac, div, mult; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite mult_lanni, mult_rid.
    intros nz.
    unfold frac_div_base; cbn.
    rewrite (ifH_false nz); cbn.
    rewrite mult_lid, mult_rid.
    apply mult_comm.
Qed.

Theorem to_frac_mult : HomomorphismMult (to_frac U).
Proof.
    split.
    intros a b.
    unfold mult at 2, to_frac; equiv_simpl.
    unfold frac_eq; cbn.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem to_frac_one : HomomorphismOne (to_frac U).
Proof.
    split.
    reflexivity.
Qed.

Theorem to_frac_div : ∀ a b,
    to_equiv (frac_equiv U) (a, b) = to_frac U a / to_frac U [b|].
Proof.
    intros a [b b_nz]; cbn.
    unfold mult, div; equiv_simpl.
    unfold frac_eq, frac_div_base; cbn.
    rewrite (ifH_false b_nz); cbn.
    rewrite mult_lid, mult_rid.
    reflexivity.
Qed.

End FractionMult.
