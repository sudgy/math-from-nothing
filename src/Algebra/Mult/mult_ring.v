Require Import init.

Require Export plus_group.

#[universes(template)]
Class Mult U := {
    mult : U → U → U;
}.
Infix "*" := mult : algebra_scope.

Class Ldist U `{Plus U} `{Mult U} := {
    ldist : ∀ a b c, a * (b + c) = a * b + a * c;
}.
Class Rdist U `{Plus U} `{Mult U} := {
    rdist : ∀ a b c, (a + b) * c = a * c + b * c;
}.

Class MultAssoc U `{Mult U} := {
    mult_assoc : ∀ a b c, a * (b * c) = (a * b) * c;
}.
Class MultComm U `{Mult U} := {
    mult_comm : ∀ a b, a * b = b * a;
}.

Class MultLanni U `{Zero U, Mult U} := {
    mult_lanni : ∀ a, 0 * a = 0;
}.
Class MultRanni U `{Zero U, Mult U} := {
    mult_ranni : ∀ a, a * 0 = 0;
}.

#[universes(template)]
Class One U := {
    one : U;
}.
Notation "1" := one : algebra_scope.
Notation "- 1" := (-(1)) : algebra_scope.
Class MultLid U `{Mult U, One U} := {
    mult_lid : ∀ a, 1 * a = a;
}.
Class MultRid U `{Mult U, One U} := {
    mult_rid : ∀ a, a * 1 = a;
}.

Class MultLcancel U `{Zero U, Mult U} := {
    mult_lcancel : ∀ {a b} c, 0 ≠ c → c * a = c * b → a = b;
}.
Class MultRcancel U `{Zero U, Mult U} := {
    mult_rcancel : ∀ {a b} c, 0 ≠ c → a * c = b * c → a = b;
}.

Class RngClass U `{
    RP : AllPlusClass U,
    UM : Mult U,
    UL : @Ldist U UP UM,
    UR : @Rdist U UP UM,
    UMA : @MultAssoc U UM
}.

Class RingClass U `{
    RR : RngClass U,
    UE : @One U,
    UME : @MultLid U UM UE,
    UMER : @MultRid U UM UE
}.

Class CRingClass U `{
    CRR : RingClass U,
    UMC : @MultComm U UM
}.

Class IntegralDomainClass U `{
    IDR : CRingClass U,
    UML : @MultLcancel U UZ UM,
    UMR : @MultRcancel U UZ UM
}.

Class AllMultClass U `{
    AMI : IntegralDomainClass U,
    UZL : @MultLanni U UZ UM,
    UZR : @MultRanni U UZ UM
}.

Class HomomorphismMult {U V} `{Mult U, Mult V} (f : U → V) := {
    homo_mult : ∀ a b, f (a * b) = f a * f b
}.

Class HomomorphismOne {U V} `{One U, One V} (f : U → V) := {
    homo_one : f 1 = 1
}.

Arguments mult : simpl never.
Arguments one : simpl never.

Notation "2" := (one + 1) : algebra_scope.
Notation "3" := (one + 2) : algebra_scope.
Notation "4" := (one + 3) : algebra_scope.
Notation "5" := (one + 4) : algebra_scope.
Notation "6" := (one + 5) : algebra_scope.
Notation "7" := (one + 6) : algebra_scope.
Notation "8" := (one + 7) : algebra_scope.
Notation "9" := (one + 8) : algebra_scope.
Notation "- 2" := (-(2)) : algebra_scope.
Notation "- 3" := (-(3)) : algebra_scope.
Notation "- 4" := (-(4)) : algebra_scope.
Notation "- 5" := (-(5)) : algebra_scope.
Notation "- 6" := (-(6)) : algebra_scope.
Notation "- 7" := (-(7)) : algebra_scope.
Notation "- 8" := (-(8)) : algebra_scope.
Notation "- 9" := (-(9)) : algebra_scope.

(* begin hide *)
Section MultRingImply.

Context {U} `{AllMultClass U}.

Global Instance mult_lid_rid : MultRid U.
Proof.
    split.
    intros a.
    rewrite mult_comm.
    apply mult_lid.
Qed.

Global Instance mult_lcancel_rcancel : MultRcancel U.
Proof.
    split.
    intros a b c neq eq.
    do 2 rewrite (mult_comm _ c) in eq.
    apply mult_lcancel with c; [>exact neq|].
    exact eq.
Qed.

Global Instance mult_lanni_ranni : MultRanni U.
Proof.
    split.
    intros a.
    rewrite mult_comm.
    apply mult_lanni.
Qed.

Global Instance ldist_rdist : Rdist U.
Proof.
    split.
    intros a b c.
    do 3 rewrite (mult_comm _ c).
    apply ldist.
Qed.

End MultRingImply.


Section MultRing.

Context {U} `{AllMultClass U, NotTrivial U}.

(* end hide *)
Theorem lmult : ∀ {a b} c, a = b → c * a = c * b.
Proof.
    intros a b c ab.
    apply f_equal.
    exact ab.
Qed.
Theorem rmult : ∀ {a b} c, a = b → a * c = b * c.
Proof.
    intros a b c ab.
    rewrite ab.
    reflexivity.
Qed.
Theorem lrmult : ∀ {a b c d}, a = b → c = d → a * c = b * d.
Proof.
    intros a b c d ab cd.
    rewrite ab, cd.
    reflexivity.
Qed.

Theorem not_trivial_one : 0 ≠ 1.
Proof.
    intros contr.
    pose proof not_trivial_zero as [a a_nz].
    apply rmult with a in contr.
    rewrite mult_lanni in contr.
    rewrite mult_lid in contr.
    contradiction.
Qed.

Global Instance ring_mult_lanni : MultLanni U.
Proof.
    split.
    intros a.
    apply plus_rcancel with (0 * a).
    rewrite <- rdist.
    do 2 rewrite plus_lid.
    reflexivity.
Qed.
Global Instance ring_mult_ranni : MultRanni U.
Proof.
    split.
    intros a.
    apply plus_lcancel with (a * 0).
    rewrite <- ldist.
    do 2 rewrite plus_rid.
    reflexivity.
Qed.

Theorem mult_lneg : ∀ a b, -a * b = -(a * b).
Proof.
    intros a b.
    apply plus_lcancel with (a * b).
    rewrite <- rdist.
    do 2 rewrite plus_rinv.
    apply mult_lanni.
Qed.
Theorem mult_rneg : ∀ a b, a * -b = -(a * b).
Proof.
    intros a b.
    apply plus_lcancel with (a * b).
    rewrite <- ldist.
    do 2 rewrite plus_rinv.
    apply mult_ranni.
Qed.
Theorem mult_lrneg : ∀ a b, -a * b = a * -b.
Proof.
    intros a b.
    rewrite mult_lneg, mult_rneg.
    reflexivity.
Qed.

Theorem mult_neg_one : ∀ a, -1 * a = -a.
Proof.
    intros a.
    rewrite mult_lneg.
    rewrite mult_lid.
    reflexivity.
Qed.

Theorem neg_nz : ∀ a, 0 ≠ a ↔ 0 ≠ -a.
Proof.
    intros a.
    split; intros neq eq.
    -   apply (f_equal neg) in eq.
        rewrite neg_neg, neg_zero in eq.
        contradiction.
    -   rewrite <- eq in neq.
        rewrite neg_zero in neq.
        contradiction.
Qed.

Theorem plus_two : ∀ a, a + a = 2*a.
Proof.
    intros a.
    rewrite <- (mult_lid a) at 1 2.
    rewrite <- rdist.
    reflexivity.
Qed.

Theorem two_plus_two : 2 + 2 = 4.
Proof.
    rewrite <- plus_assoc.
    reflexivity.
Qed.

Theorem two_times_two : 2 * 2 = 4.
Proof.
    rewrite ldist.
    rewrite mult_rid.
    exact two_plus_two.
Qed.

Theorem dif_squares : ∀ a b, a*a - b*b = (a + b) * (a - b).
Proof.
    intros a b.
    rewrite rdist.
    do 2 rewrite ldist.
    do 2 rewrite mult_rneg.
    rewrite (mult_comm b a).
    rewrite <- plus_assoc.
    rewrite plus_llinv.
    reflexivity.
Qed.

Theorem mult_zero : ∀ a b, 0 = a * b → 0 = a ∨ 0 = b.
Proof.
    intros a b eq.
    classic_case (0 = a) as [a_z|a_nz].
    -   left.
        exact a_z.
    -   right.
        apply mult_lcancel with a; [>exact a_nz|].
        rewrite mult_ranni.
        exact eq.
Qed.

Theorem mult_nz : ∀ a b, 0 ≠ a → 0 ≠ b → 0 ≠ a * b.
Proof.
    intros a b neq1 neq2 contr.
    apply mult_zero in contr.
    destruct contr; contradiction.
Qed.

(* begin hide *)
End MultRing.

Section MultHomo.

Context {U V} `{AllMultClass U, AllMultClass V}.
(* end hide *)
Context (f : U → V) `{
    @Injective U V f,
    @HomomorphismPlus U V UP UP0 f,
    @HomomorphismZero U V UZ UZ0 f,
    @HomomorphismNeg U V UN UN0 f,
    @HomomorphismMult U V UM UM0 f,
    @HomomorphismOne U V UE UE0 f
}.

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

(* begin hide *)
End MultHomo.
(* end hide *)
Tactic Notation "mult_bring_left" constr(x) :=
    repeat rewrite mult_assoc;
    repeat rewrite (mult_comm _ x);
    repeat rewrite <- mult_assoc.
Tactic Notation "mult_bring_left" constr(x) "in" ident(H) :=
    repeat rewrite mult_assoc in H;
    repeat rewrite (mult_comm _ x) in H;
    repeat rewrite <- mult_assoc in H.
Tactic Notation "mult_bring_right" constr(x) :=
    repeat rewrite <- mult_assoc;
    repeat rewrite (mult_comm x _);
    repeat rewrite mult_assoc.
Tactic Notation "mult_bring_right" constr(x) "in" ident(H) :=
    repeat rewrite <- mult_assoc in H;
    repeat rewrite (mult_comm x _) in H;
    repeat rewrite mult_assoc in H.
