Require Import init.

#[universes(template)]
Class Plus U := {
    plus : U → U → U;
}.
Infix "+" := plus : algebra_scope.

Class PlusAssoc U `{Plus U} := {
    plus_assoc : ∀ a b c, a + (b + c) = (a + b) + c;
}.
Class PlusComm U `{Plus U} := {
    plus_comm : ∀ a b, a + b = b + a;
}.

#[universes(template)]
Class Zero U := {
    zero : U;
}.
Notation "0" := zero : algebra_scope.
Class PlusLid U `{Plus U} `{Zero U} := {
    plus_lid : ∀ a, 0 + a = a;
}.
Class PlusRid U `{Plus U} `{Zero U} := {
    plus_rid : ∀ a, a + 0 = a;
}.

Class PlusLcancel U `{Plus U} := {
    plus_lcancel : ∀ {a b} c, c + a = c + b → a = b;
}.
Class PlusRcancel U `{Plus U} := {
    plus_rcancel : ∀ {a b} c, a + c = b + c → a = b;
}.

#[universes(template)]
Class Neg U := {
    neg : U → U;
}.
Notation "- a" := (neg a) : algebra_scope.
Notation "a - b" := (a + -b) : algebra_scope.
Class PlusLinv U `{Plus U} `{Zero U} `{Neg U} := {
    plus_linv : ∀ a, -a + a = 0;
}.
Class PlusRinv U `{Plus U} `{Zero U} `{Neg U} := {
    plus_rinv : ∀ a, a - a = 0;
}.
Arguments plus : simpl never.
Arguments zero : simpl never.
Arguments neg : simpl never.

Class GroupClass U `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UPA : @PlusAssoc U UP,
    UPZ : @PlusLid U UP UZ,
    UPZR : @PlusRid U UP UZ,
    UPN : @PlusLinv U UP UZ UN,
    UPNR : @PlusRinv U UP UZ UN
}.

Class AbelianGroupClass U `{
    AGG : GroupClass U,
    UPC : @PlusComm U UP
}.

Class AllPlusClass U `{
    APG : AbelianGroupClass U,
    UPL : @PlusLcancel U UP,
    UPR : @PlusRcancel U UP
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


(* begin hide *)
Section PlusGroupImply.

Context {U} `{AllPlusClass U}.

Global Instance plus_lid_rid : PlusRid U.
Proof.
    split.
    intros a.
    rewrite plus_comm.
    apply plus_lid.
Qed.

Global Instance plus_lcancel_rcancel : PlusRcancel U.
Proof.
    split.
    intros a b c eq.
    do 2 rewrite (plus_comm _ c) in eq.
    apply plus_lcancel with c.
    exact eq.
Qed.

Global Instance plus_linv_rinv : PlusRinv U.
Proof.
    split.
    intros a.
    rewrite plus_comm.
    apply plus_linv.
Qed.

End PlusGroupImply.


Section PlusGroup.

Context {U} `{AllPlusClass U, NotTrivial U}.

(* end hide *)
Theorem lplus : ∀ {a b} c, a = b → c + a = c + b.
Proof.
    intros a b c ab.
    apply f_equal.
    exact ab.
Qed.
Theorem rplus : ∀ {a b} c, a = b → a + c = b + c.
Proof.
    intros a b c ab.
    rewrite ab.
    reflexivity.
Qed.
Theorem lrplus : ∀ {a b c d}, a = b → c = d → a + c = b + d.
Proof.
    intros a b c d ab cd.
    rewrite ab, cd.
    reflexivity.
Qed.

Theorem not_trivial_zero : ∃ a, 0 ≠ a.
Proof.
    apply not_trivial2.
Qed.

(* begin hide *)
End PlusGroup.

Section PlusGroup2.

Context {U} `{AllPlusClass U}.

Theorem plus_rrinv : ∀ a b, a + b - b = a.
Proof.
    intros a b.
    rewrite <- plus_assoc.
    rewrite plus_rinv.
    apply plus_rid.
Qed.
Theorem plus_rlinv : ∀ a b, a - b + b = a.
Proof.
    intros a b.
    rewrite <- plus_assoc.
    rewrite plus_linv.
    apply plus_rid.
Qed.
Theorem plus_lrinv : ∀ a b, b + (-b + a) = a.
Proof.
    intros a b.
    rewrite plus_assoc.
    rewrite plus_rinv.
    apply plus_lid.
Qed.
Theorem plus_llinv : ∀ a b, -b + (b + a) = a.
Proof.
    intros a b.
    rewrite plus_assoc.
    rewrite plus_linv.
    apply plus_lid.
Qed.

Global Instance plus_linv_lcancel : PlusLcancel U.
Proof.
    split.
    intros a b c eq.
    apply lplus with (-c) in eq.
    do 2 rewrite plus_llinv in eq.
    exact eq.
Qed.

Global Instance plus_rinv_rcancel : PlusRcancel U.
Proof.
    split.
    intros a b c eq.
    apply rplus with (-c) in eq.
    do 2 rewrite plus_rrinv in eq.
    exact eq.
Qed.

(* end hide *)
Theorem neg_zero : -0 = 0.
Proof.
    apply plus_rcancel with 0.
    rewrite plus_linv.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem neg_neg : ∀ a, --a = a.
Proof.
    intros a.
    apply plus_rcancel with (-a).
    rewrite plus_linv, plus_rinv.
    reflexivity.
Qed.

Theorem neg_eq : ∀ a b, a = b ↔ -a = -b.
Proof.
    intros a b.
    split; intros eq.
    -   rewrite eq.
        reflexivity.
    -   apply (f_equal neg) in eq.
        do 2 rewrite neg_neg in eq.
        exact eq.
Qed.

Theorem plus_llmove : ∀ a b c, a + b = c ↔ b = -a + c.
Proof.
    intros a b c.
    split; intros eq.
    -   apply lplus with (-a) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply lplus with a in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem plus_lrmove : ∀ a b c, a + b = c ↔ a = c - b.
Proof.
    intros a b c.
    split; intros eq.
    -   apply rplus with (-b) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply rplus with b in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.
Theorem plus_rlmove : ∀ a b c, a = b + c ↔ -b + a = c.
Proof.
    intros a b c.
    split; intros eq.
    -   apply lplus with (-b) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply lplus with b in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem plus_rrmove : ∀ a b c, a = b + c ↔ a - c = b.
Proof.
    intros a b c.
    split; intros eq.
    -   apply rplus with (-c) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply rplus with c in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.

Theorem plus_0_ab_na_b : ∀ a b, 0 = a + b ↔ -a = b.
Proof.
    intros a b.
    rewrite plus_rlmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem plus_0_ab_nb_a : ∀ a b, 0 = a + b ↔ -b = a.
Proof.
    intros a b.
    rewrite plus_rrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem plus_0_ab_a_nb : ∀ a b, 0 = a + b ↔ a = -b.
Proof.
    intros a b.
    rewrite plus_0_ab_na_b.
    rewrite neg_eq.
    rewrite neg_neg.
    reflexivity.
Qed.
Theorem plus_0_ab_b_na : ∀ a b, 0 = a + b ↔ b = -a.
Proof.
    intros a b.
    rewrite plus_0_ab_nb_a.
    rewrite neg_eq.
    rewrite neg_neg.
    reflexivity.
Qed.

Theorem plus_0_a_ab_b : ∀ a b, 0 = a ↔ a + b = b.
Proof.
    intros a b.
    split; intros eq.
    -   rewrite <- eq.
        apply plus_lid.
    -   rewrite <- (plus_lid b) in eq at 2.
        apply plus_rcancel in eq.
        symmetry; exact eq.
Qed.
Theorem plus_0_a_ba_b : ∀ a b, 0 = a ↔ b + a = b.
Proof.
    intros a b.
    split; intros eq.
    -   rewrite <- eq.
        apply plus_rid.
    -   rewrite <- (plus_rid b) in eq at 2.
        apply plus_lcancel in eq.
        symmetry; exact eq.
Qed.
Theorem plus_0_a_b_ab : ∀ a b, 0 = a ↔ b = a + b.
Proof.
    intros a b.
    split; intros eq.
    -   rewrite <- eq.
        symmetry; apply plus_lid.
    -   rewrite <- (plus_lid b) in eq at 1.
        apply plus_rcancel in eq.
        exact eq.
Qed.
Theorem plus_0_a_b_ba : ∀ a b, 0 = a ↔ b = b + a.
Proof.
    intros a b.
    split; intros eq.
    -   rewrite <- eq.
        symmetry; apply plus_rid.
    -   rewrite <- (plus_rid b) in eq at 1.
        apply plus_lcancel in eq.
        exact eq.
Qed.

Theorem plus_0_nab_a_b : ∀ a b, 0 = -a + b ↔ a = b.
Proof.
    intros a b.
    rewrite plus_0_ab_na_b.
    rewrite neg_neg.
    reflexivity.
Qed.
Theorem plus_0_anb_a_b : ∀ a b, 0 = a - b ↔ a = b.
Proof.
    intros a b.
    rewrite plus_0_ab_a_nb.
    rewrite neg_neg.
    reflexivity.
Qed.
Theorem plus_0_nab_b_a : ∀ a b, 0 = -a + b ↔ b = a.
Proof.
    intros a b.
    rewrite plus_0_ab_b_na.
    rewrite neg_neg.
    reflexivity.
Qed.
Theorem plus_0_anb_b_a : ∀ a b, 0 = a - b ↔ b = a.
Proof.
    intros a b.
    rewrite plus_0_ab_nb_a.
    rewrite neg_neg.
    reflexivity.
Qed.

Theorem neg_plus_group : ∀ a b, -(a + b) = -b + -a.
Proof.
    intros a b.
    apply (plus_lcancel (a + b)).
    rewrite plus_rinv.
    rewrite <- plus_assoc.
    rewrite plus_lrinv.
    rewrite plus_rinv.
    reflexivity.
Qed.

Theorem neg_plus : ∀ a b, -(a + b) = -a + -b.
Proof.
    intros a b.
    rewrite neg_plus_group.
    apply plus_comm.
Qed.

Theorem zero_eq_neg : ∀ a, 0 = a ↔ 0 = -a.
Proof.
    intros a.
    rewrite neg_eq.
    rewrite neg_zero.
    reflexivity.
Qed.

Theorem plus_3 : ∀ a b c, a + (b + c) = b + (a + c).
Proof.
    intros a b c.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply plus_comm.
Qed.

Theorem plus_4 : ∀ a b c d, a + b + (c + d) = a + c + (b + d).
Proof.
    intros a b c d.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    apply plus_3.
Qed.

(* begin hide *)
End PlusGroup2.

Section PlusHomo.

Context {U V W} `{AllPlusClass U, AllPlusClass V, AllPlusClass W}.
(* end hide *)
Context (f : U → V) (g : V → W) `{
    @Injective U V f,
    @HomomorphismPlus U V UP UP0 f,
    @HomomorphismZero U V UZ UZ0 f,
    @HomomorphismNeg U V UN UN0 f,
    @HomomorphismPlus V W UP0 UP1 g,
    @HomomorphismZero V W UZ0 UZ1 g,
    @HomomorphismNeg V W UN0 UN1 g
}.

Theorem homo_zero_inj : (∀ a, 0 = f a → 0 = a) → Injective f.
Proof.
    intros inj.
    split.
    intros a b.
    rewrite <- plus_0_anb_a_b.
    rewrite <- (plus_0_anb_a_b a b).
    rewrite <- homo_neg, <- homo_plus.
    apply inj.
Qed.

Theorem inj_zero : ∀ {a}, 0 ≠ a → 0 ≠ f a.
Proof.
    intros a a_nz contr.
    rewrite <- homo_zero in contr.
    apply inj in contr.
    contradiction.
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

Local Instance homo_plus_compose : HomomorphismPlus (λ x, g (f x)).
Proof.
    split.
    intros a b.
    setoid_rewrite homo_plus.
    apply homo_plus.
Qed.

Local Instance homo_zero_compose : HomomorphismZero (λ x, g (f x)).
Proof.
    split.
    setoid_rewrite homo_zero.
    apply homo_zero.
Qed.

Local Instance homo_neg_compose : HomomorphismNeg (λ x, g (f x)).
Proof.
    split.
    intros a.
    setoid_rewrite homo_neg.
    apply homo_neg.
Qed.

(* begin hide *)
End PlusHomo.
(* end hide *)
Tactic Notation "plus_bring_left" constr(x) :=
    repeat rewrite plus_assoc;
    repeat rewrite (plus_comm _ x);
    repeat rewrite <- plus_assoc.
Tactic Notation "plus_bring_left" constr(x) "in" ident(H) :=
    repeat rewrite plus_assoc in H;
    repeat rewrite (plus_comm _ x) in H;
    repeat rewrite <- plus_assoc in H.
Tactic Notation "plus_bring_right" constr(x) :=
    repeat rewrite <- plus_assoc;
    repeat rewrite (plus_comm x _);
    repeat rewrite plus_assoc.
Tactic Notation "plus_bring_right" constr(x) "in" ident(H) :=
    repeat rewrite <- plus_assoc in H;
    repeat rewrite (plus_comm x _) in H;
    repeat rewrite plus_assoc in H.
Tactic Notation "plus_cancel_left" constr(x) :=
    plus_bring_left x;
    apply lplus.
Tactic Notation "plus_cancel_left" constr(x) "in" ident(H) :=
    plus_bring_left x in H;
    apply plus_lcancel in H.
Tactic Notation "plus_cancel_right" constr(x) :=
    plus_bring_right x;
    apply rplus.
Tactic Notation "plus_cancel_right" constr(x) "in" ident(H) :=
    plus_bring_right x in H;
    apply plus_rcancel in H.
