Require Import init.

Require Export plus_group.
Require Import op.

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
    mult_lanni : ∀ a, zero * a = zero;
}.
Class MultRanni U `{Zero U, Mult U} := {
    mult_ranni : ∀ a, a * zero = zero;
}.

#[universes(template)]
Class One U := {
    one : U;
}.
Class MultLid U `{Mult U, One U} := {
    mult_lid : ∀ a, one * a = a;
}.
Class MultRid U `{Mult U, One U} := {
    mult_rid : ∀ a, a * one = a;
}.

Class MultLcancel U `{Zero U, Mult U} := {
    mult_lcancel : ∀ {a b} c, zero ≠ c → c * a = c * b → a = b;
}.
Class MultRcancel U `{Zero U, Mult U} := {
    mult_rcancel : ∀ {a b} c, zero ≠ c → a * c = b * c → a = b;
}.

Class Rng U `{
    RP : AllPlus U,
    UM : Mult U,
    UL : @Ldist U UP UM,
    UR : @Rdist U UP UM,
    UMA : @MultAssoc U UM
}.

Class Ring U `{
    RR : Rng U,
    UE : @One U,
    UME : @MultLid U UM UE,
    UMER : @MultRid U UM UE
}.

Class CRing U `{
    CRR : Ring U,
    UMC : @MultComm U UM
}.

Class IntegralDomain U `{
    IDR : CRing U,
    UML : @MultLcancel U UZ UM,
    UMR : @MultRcancel U UZ UM
}.

Class AllMult U `{
    AMI : IntegralDomain U,
    UZL : @MultLanni U UZ UM,
    UZR : @MultRanni U UZ UM
}.

Arguments mult : simpl never.
Arguments one : simpl never.

Notation "1" := one : algebra_scope.
Notation "2" := (one + 1) : algebra_scope.
Notation "3" := (one + 2) : algebra_scope.
Notation "4" := (one + 3) : algebra_scope.
Notation "5" := (one + 4) : algebra_scope.
Notation "6" := (one + 5) : algebra_scope.
Notation "7" := (one + 6) : algebra_scope.
Notation "8" := (one + 7) : algebra_scope.
Notation "9" := (one + 8) : algebra_scope.

(* begin hide *)
Section MultRingImply.

Context {U} `{AllMult U}.

Lemma mult_lid_rid_ : ∀ a, a * one = a.
    intros a.
    rewrite mult_comm.
    apply mult_lid.
Qed.

Lemma mult_lcancel_rcancel_ : ∀ a b c, zero ≠ c → a * c = b * c → a = b.
    intros a b c neq eq.
    do 2 rewrite (mult_comm _ c) in eq.
    apply mult_lcancel with c; try exact neq.
    exact eq.
Qed.

Lemma mult_lanni_ranni_ : ∀ a, a * zero = zero.
    intros a.
    rewrite mult_comm.
    apply mult_lanni.
Qed.

Lemma ldist_rdist_ : ∀ a b c, (a + b) * c = a * c + b * c.
    intros a b c.
    do 3 rewrite (mult_comm _ c).
    apply ldist.
Qed.

Global Instance mult_lid_rid : MultRid U := {
    mult_rid := mult_lid_rid_;
}.

Global Instance mult_lcancel_rcancel : MultRcancel U := {
    mult_rcancel := mult_lcancel_rcancel_;
}.

Global Instance mult_lanni_ranni : MultRanni U := {
    mult_ranni := mult_lanni_ranni_;
}.

Global Instance ldist_rdist : Rdist U := {
    rdist := ldist_rdist_;
}.

End MultRingImply.


Section MultRing.

Context {U} `{AllMult U, NotTrivial U}.

Global Instance mult_op_assoc : Assoc mult := {assoc := mult_assoc}.
Global Instance mult_op_comm : Comm mult := {comm := mult_comm}.
Global Instance mult_op_id : Id mult := {id := one}.
Global Instance mult_op_lid : Lid mult := {lid := mult_lid}.
Global Instance mult_op_rid : Rid mult := {rid := mult_rid}.
Global Instance mult_op_anni : Anni mult := {anni := zero}.
Global Instance mult_op_lanni : Lanni mult := {lanni := mult_lanni}.
Global Instance mult_op_ranni : Ranni mult := {ranni := mult_ranni}.
(* end hide *)
Theorem lmult : ∀ {a b} c, a = b → c * a = c * b.
    apply lop.
Qed.
Theorem rmult : ∀ {a b} c, a = b → a * c = b * c.
    apply lop.
Qed.
Theorem lrmult : ∀ {a b c d}, a = b → c = d → a * c = b * d.
    apply lrop.
Qed.

Theorem not_trivial_one : 0 ≠ 1.
    intros contr.
    pose proof not_trivial_zero as [a a_nz].
    apply rmult with a in contr.
    rewrite mult_lanni in contr.
    rewrite mult_lid in contr.
    contradiction.
Qed.

(* begin hide *)
Theorem ring_mult_lanni : ∀ a, 0 * a = 0.
    intros a.
    assert (0 * a = 0 * a) as eq by reflexivity.
    rewrite <- (plus_rid 0) in eq at 1.
    rewrite rdist in eq.
    rewrite <- (plus_lid (0 * a)) in eq at 3.
    apply plus_rcancel in eq.
    exact eq.
Qed.
Theorem ring_mult_ranni : ∀ a, a * 0 = 0.
    intros a.
    assert (a * 0 = a * 0) as eq by reflexivity.
    rewrite <- (plus_rid 0) in eq at 1.
    rewrite ldist in eq.
    rewrite <- (plus_lid (a * 0)) in eq at 3.
    apply plus_rcancel in eq.
    exact eq.
Qed.

Global Instance rint_mult_lanni_class : MultLanni U := {
    mult_lanni := ring_mult_lanni;
}.
Global Instance rint_mult_ranni_class : MultRanni U := {
    mult_ranni := ring_mult_ranni;
}.
(* end hide *)
Theorem mult_lneg : ∀ a b, -a * b = -(a * b).
    intros a b.
    apply plus_lcancel with (a * b).
    rewrite <- rdist.
    do 2 rewrite plus_rinv.
    apply mult_lanni.
Qed.
Theorem mult_rneg : ∀ a b, a * -b = -(a * b).
    intros a b.
    apply plus_lcancel with (a * b).
    rewrite <- ldist.
    do 2 rewrite plus_rinv.
    apply mult_ranni.
Qed.
Theorem mult_lrneg : ∀ a b, -a * b = a * -b.
    intros a b.
    rewrite mult_lneg, mult_rneg.
    reflexivity.
Qed.

Theorem mult_neg_one : ∀ a, -one * a = -a.
    intros a.
    rewrite mult_lneg.
    rewrite mult_lid.
    reflexivity.
Qed.

Theorem neg_nz : ∀ a, 0 ≠ a → 0 ≠ -a.
    intros a a_nz eq.
    apply (f_equal neg) in eq.
    rewrite neg_neg, neg_zero in eq.
    contradiction.
Qed.

Theorem plus_two : ∀ a, a + a = 2*a.
    intros a.
    rewrite <- (mult_lid a) at 1 2.
    rewrite <- rdist.
    reflexivity.
Qed.

Theorem two_plus_two : 2 + 2 = 4.
    rewrite <- plus_assoc.
    reflexivity.
Qed.

Theorem two_times_two : 2 * 2 = 4.
    rewrite ldist.
    rewrite mult_rid.
    exact two_plus_two.
Qed.

Theorem dif_squares : ∀ a b, a*a - b*b = (a + b) * (a - b).
    intros a b.
    rewrite rdist.
    do 2 rewrite ldist.
    rewrite mult_rneg.
    rewrite (mult_comm b a).
    rewrite <- plus_assoc.
    rewrite plus_llinv.
    rewrite mult_rneg.
    reflexivity.
Qed.

Theorem mult_zero : ∀ a b, 0 = a * b → 0 = a ∨ 0 = b.
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
    intros a b neq1 neq2 contr.
    apply mult_zero in contr.
    destruct contr; contradiction.
Qed.

(* begin hide *)
End MultRing.
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
Tactic Notation "mult_cancel_left" constr(x) :=
    mult_bring_left x;
    apply lmult.
Tactic Notation "mult_cancel_left" constr(x) "in" ident(H) :=
    mult_bring_left x in H;
    apply mult_lcancel in H.
Tactic Notation "mult_cancel_right" constr(x) :=
    mult_bring_right x;
    apply rmult.
Tactic Notation "mult_cancel_right" constr(x) "in" ident(H) :=
    mult_bring_right x in H;
    apply mult_rcancel in H.
