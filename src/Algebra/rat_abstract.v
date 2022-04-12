Require Import init.

Require Import int_abstract.
Require Import fraction_base.
Require Import mult_characteristic.

Require Export rat.
Require Import set.

Section RatAbstract.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    UD : Div U,
    @Ldist U UP UM,
    @MultComm U UM,
    @MultAssoc U UM,
    @MultLid U UM UO,
    @MultLinv U UZ UM UO UD,
    @CharacteristicZero U UP UZ UO
}.

Definition rat_to_abstract_base (x : frac_base int)
    := int_to_abstract (fst x) / int_to_abstract [snd x|] : U.

Local Infix "~" := (eq_equal (frac_equiv int)).

Theorem int_to_abstract_nz : ∀ a : frac_base int, 0 ≠ int_to_abstract [snd a|].
    intros a.
    intros contr.
    apply [|snd a].
    rewrite <- int_to_abstract_zero in contr.
    apply int_to_abstract_eq in contr.
    exact contr.
Qed.

Theorem rat_to_abstract_wd : ∀ a b, a ~ b →
        rat_to_abstract_base a = rat_to_abstract_base b.
    intros a b eq.
    cbn in eq.
    unfold frac_eq in eq; cbn in eq.
    unfold rat_to_abstract_base; cbn.
    rewrite <- mult_rrmove by apply int_to_abstract_nz.
    rewrite (mult_comm (_ (fst b))).
    rewrite <- mult_assoc.
    rewrite <- mult_llmove by apply int_to_abstract_nz.
    do 2 rewrite <- int_to_abstract_mult.
    rewrite mult_comm.
    rewrite eq.
    reflexivity.
Qed.

Definition rat_to_abstract (a : rat) := unary_op rat_to_abstract_wd a.

Theorem rat_to_abstract_eq : ∀ a b,
        rat_to_abstract a = rat_to_abstract b → a = b.
    intros a b eq.
    equiv_get_value a b.
    unfold rat_to_abstract in eq.
    equiv_simpl in eq.
    unfold rat; equiv_simpl.
    unfold frac_eq.
    unfold rat_to_abstract_base in eq.
    rewrite <- mult_rrmove in eq by apply int_to_abstract_nz.
    rewrite (mult_comm (_ (fst b))) in eq.
    rewrite <- mult_assoc in eq.
    rewrite <- mult_llmove in eq by apply int_to_abstract_nz.
    do 2 rewrite <- int_to_abstract_mult in eq.
    apply int_to_abstract_eq in eq.
    rewrite <- eq.
    apply mult_comm.
Qed.

Theorem rat_to_abstract_zero : rat_to_abstract 0 = 0.
    unfold zero at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    rewrite int_to_abstract_zero.
    apply mult_lanni.
Qed.

Theorem rat_to_abstract_one : rat_to_abstract 1 = 1.
    unfold one at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    rewrite int_to_abstract_one.
    rewrite div_one.
    apply mult_lid.
Qed.

Theorem rat_to_abstract_plus : ∀ a b,
        rat_to_abstract (a + b) = rat_to_abstract a + rat_to_abstract b.
    intros a b.
    equiv_get_value a b.
    unfold plus at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    rewrite int_to_abstract_plus.
    do 3 rewrite int_to_abstract_mult.
    rewrite div_mult by apply int_to_abstract_nz.
    rewrite mult_assoc.
    do 2 rewrite rdist.
    rewrite mult_rrinv by apply int_to_abstract_nz.
    apply rplus.
    rewrite <- mult_assoc.
    rewrite (mult_comm (/ _ [snd a|])).
    rewrite mult_assoc.
    rewrite mult_rrinv by apply int_to_abstract_nz.
    reflexivity.
Qed.

Theorem rat_to_abstract_neg : ∀ a, rat_to_abstract (-a) = -rat_to_abstract a.
    intros a.
    equiv_get_value a.
    unfold neg at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    rewrite int_to_abstract_neg.
    apply mult_lneg.
Qed.

Theorem rat_to_abstract_mult : ∀ a b,
        rat_to_abstract (a * b) = rat_to_abstract a * rat_to_abstract b.
    intros a b.
    equiv_get_value a b.
    unfold mult at 1, rat_to_abstract; equiv_simpl.
    unfold rat_to_abstract_base; cbn.
    do 2 rewrite int_to_abstract_mult.
    do 2 rewrite <- mult_assoc.
    apply lmult.
    rewrite div_mult by apply int_to_abstract_nz.
    do 2 rewrite mult_assoc.
    apply rmult.
    apply mult_comm.
Qed.

Theorem rat_to_abstract_div : ∀ a, 0 ≠ a →
        rat_to_abstract (/a) = /rat_to_abstract a.
    intros a a_nz.
    equiv_get_value a.
    unfold div at 1, rat_to_abstract; equiv_simpl.
    unfold zero in a_nz; cbn in a_nz.
    unfold to_frac, rat in a_nz; equiv_simpl in a_nz.
    unfold frac_eq in a_nz; cbn in a_nz.
    rewrite mult_rid, mult_lanni in a_nz.
    destruct (strong_excluded_middle (0 = fst a)) as [contr|a_nz'];
        [>contradiction|].
    unfold rat_to_abstract_base; cbn.
    rewrite div_mult.
    -   rewrite div_div by apply int_to_abstract_nz.
        apply mult_comm.
    -   intros contr.
        rewrite <- int_to_abstract_zero in contr.
        apply int_to_abstract_eq in contr.
        contradiction.
    -   apply div_nz.
        apply int_to_abstract_nz.
Qed.

End RatAbstract.
