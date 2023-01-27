Require Import init.

Require Export order_mult.

Class HomomorphismInj {U V} (f : U → V) := {
    homo_inj : ∀ a b, f a = f b → a = b
}.

Class HomomorphismPlus {U V} `{Plus U, Plus V} (f : U → V) := {
    homo_plus : ∀ a b, f (a + b) = f a + f b
}.

Class HomomorphismZero {U V} `{Zero U, Zero V} (f : U → V) := {
    homo_zero : f 0 = 0
}.

Class HomomorphismNeg {U V} `{Neg U, Neg V} (f : U → V) := {
    homo_neg : ∀ a, f (-a) = -f a
}.

Class HomomorphismMult {U V} `{Mult U, Mult V} (f : U → V) := {
    homo_mult : ∀ a b, f (a * b) = f a * f b
}.

Class HomomorphismOne {U V} `{One U, One V} (f : U → V) := {
    homo_one : f 1 = 1
}.

Class HomomorphismDiv {U V} `{Zero U, Div U, Div V} (f : U → V) := {
    homo_div : ∀ a, 0 ≠ a → f (/a) = /f a
}.

Class HomomorphismLe {U V} `{Order U, Order V} (f : U → V) := {
    homo_le : ∀ a b, a ≤ b → f a ≤ f b
}.

Class HomomorphismLt {U V} `{Order U, Order V} (f : U → V) := {
    homo_lt : ∀ a b, a < b → f a < f b
}.

Class HomomorphismLe2 {U V} `{Order U, Order V} (f : U → V) := {
    homo_le2 : ∀ a b, a ≤ b ↔ f a ≤ f b
}.

Class HomomorphismLt2 {U V} `{Order U, Order V} (f : U → V) := {
    homo_lt2 : ∀ a b, a < b ↔ f a < f b
}.

Section Homomorphisms.

Context {U V} `{OrderedField U, OrderedField V}.
Context (f : U → V) `{
    @HomomorphismInj U V f,
    @HomomorphismPlus U V UP UP0 f,
    @HomomorphismZero U V UZ UZ0 f,
    @HomomorphismNeg U V UN UN0 f,
    @HomomorphismMult U V UM UM0 f,
    @HomomorphismOne U V UE UE0 f,
    @HomomorphismDiv U V UZ UD UD0 f,
    @HomomorphismLe U V UO UO0 f,
    @HomomorphismLt U V UO UO0 f,
    @HomomorphismLe2 U V UO UO0 f,
    @HomomorphismLt2 U V UO UO0 f
}.

Theorem homo_zero_inj : (∀ a, 0 = f a → 0 = a) → HomomorphismInj f.
Proof.
    intros inj.
    split.
    intros a b.
    rewrite <- plus_0_anb_a_b.
    rewrite <- (plus_0_anb_a_b a b).
    rewrite <- homo_neg, <- homo_plus.
    apply inj.
Qed.

Theorem homo_inj_zero : ∀ {a}, 0 ≠ a → 0 ≠ f a.
Proof.
    intros a a_nz contr.
    rewrite <- homo_zero in contr.
    apply homo_inj in contr.
    contradiction.
Qed.

Theorem homo_two : f 2 = 2.
Proof.
    setoid_rewrite homo_plus.
    rewrite homo_one.
    reflexivity.
Qed.

Theorem homo_three : f 3 = 3.
Proof.
    setoid_rewrite homo_plus.
    rewrite homo_one, homo_two.
    reflexivity.
Qed.

Theorem homo_four : f 4 = 4.
Proof.
    setoid_rewrite homo_plus.
    rewrite homo_one, homo_three.
    reflexivity.
Qed.

Global Instance group_homo_zero : HomomorphismZero f.
Proof.
    split.
    apply (plus_lcancel (f 0)).
    rewrite <- homo_plus.
    do 2 rewrite plus_rid.
    reflexivity.
Qed.
Local Remove Hints group_homo_zero : typeclass_instances.

Global Instance group_homo_neg : HomomorphismNeg f.
Proof.
    split.
    intros a.
    apply (plus_lcancel (f a)).
    rewrite <- homo_plus.
    do 2 rewrite plus_rinv.
    apply homo_zero.
Qed.
Local Remove Hints group_homo_neg : typeclass_instances.

Global Instance field_homo_inj : HomomorphismInj f.
Proof.
    apply homo_zero_inj.
    intros a eq.
    classic_contradiction a_nz.
    apply (lmult (f (/a))) in eq.
    rewrite mult_ranni in eq.
    rewrite <- homo_mult in eq.
    rewrite mult_linv in eq by exact a_nz.
    rewrite homo_one in eq.
    contradiction (not_trivial_one eq).
Qed.
Local Remove Hints field_homo_inj : typeclass_instances.

Global Instance field_homo_div : HomomorphismDiv f.
Proof.
    split.
    intros a a_nz.
    pose proof (homo_inj_zero a_nz) as fa_nz.
    apply (mult_lcancel (f a) fa_nz).
    rewrite <- homo_mult.
    do 2 rewrite mult_rinv by assumption.
    apply homo_one.
Qed.
Local Remove Hints field_homo_div : typeclass_instances.

Global Instance homo_le_lt : HomomorphismLt f.
Proof.
    split.
    intros a b [leq neq].
    split.
    -   apply homo_le.
        exact leq.
    -   intros contr.
        apply homo_inj in contr.
        contradiction.
Qed.
Local Remove Hints homo_le_lt : typeclass_instances.

Global Instance homo_le_le2 : HomomorphismLe2 f.
Proof.
    split.
    intros a b.
    split; [>apply homo_le|].
    intros leq.
    classic_contradiction ltq.
    rewrite nle_lt in ltq.
    destruct ltq as [leq2 neq].
    apply homo_le in leq2.
    pose proof (antisym leq2 leq) as eq.
    apply homo_inj in eq.
    contradiction.
Qed.
Local Remove Hints homo_le_le2 : typeclass_instances.

Global Instance homo_lt_lt2 : HomomorphismLt2 f.
Proof.
    split.
    intros a b.
    split; [>apply homo_lt|].
    intros ltq.
    classic_contradiction leq.
    rewrite nlt_le in leq.
    classic_case (b = a) as [eq|neq].
    -   subst b.
        contradiction (irrefl _ ltq).
    -   pose proof (homo_lt _ _ (make_and leq neq)) as ltq2.
        contradiction (irrefl _ (trans ltq ltq2)).
Qed.
Local Remove Hints homo_lt_lt2 : typeclass_instances.

End Homomorphisms.
