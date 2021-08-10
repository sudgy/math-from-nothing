Require Import init.

Require Import op.

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
Class PlusLid U `{Plus U} `{Zero U} := {
    plus_lid : ∀ a, zero + a = a;
}.
Class PlusRid U `{Plus U} `{Zero U} := {
    plus_rid : ∀ a, a + zero = a;
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
    plus_linv : ∀ a, -a + a = zero;
}.
Class PlusRinv U `{Plus U} `{Zero U} `{Neg U} := {
    plus_rinv : ∀ a, a + -a = zero;
}.

Arguments plus : simpl never.
Arguments zero : simpl never.
Arguments neg : simpl never.

Notation "0" := zero : algebra_scope.


(* begin hide *)
Section PlusGroupImply.

Context {U} `{
    p : Plus U,
    z : Zero U,
    n : Neg U,
    @PlusLid U p z,
    @PlusLcancel U p,
    @PlusComm U p,
    @PlusLinv U p z n
}.

Lemma plus_lid_rid_ : ∀ a, a + zero = a.
    intros a.
    rewrite plus_comm.
    apply plus_lid.
Qed.

Lemma plus_lcancel_rcancel_ : ∀ a b c, a + c = b + c → a = b.
    intros a b c eq.
    do 2 rewrite (plus_comm _ c) in eq.
    apply plus_lcancel with c.
    exact eq.
Qed.

Lemma plus_linv_rinv : ∀ a, a + -a = 0.
    intros a.
    rewrite plus_comm.
    apply plus_linv.
Qed.

Global Instance plus_lid_rid : PlusRid U := {
    plus_rid := plus_lid_rid_;
}.

Global Instance plus_lcancel_rcancel : PlusRcancel U := {
    plus_rcancel := plus_lcancel_rcancel_;
}.

Global Instance plus_linv_rinv_class : PlusRinv U := {
    plus_rinv := plus_linv_rinv
}.

End PlusGroupImply.


Section PlusGroup.

Context {U} `{
    p : Plus U,
    @PlusAssoc U p,
    @PlusComm U p,
    z : Zero U,
    @PlusLid U p z,
    @PlusRid U p z,
    @PlusLcancel U p,
    @PlusRcancel U p,
    n : Neg U,
    @PlusLinv U p z n,
    @PlusRinv U p z n
}.

Global Instance plus_op_assoc : Assoc plus := {assoc := plus_assoc}.
Global Instance plus_op_comm : Comm plus := {comm := plus_comm}.
Global Instance plus_op_id : Id plus := {id := zero}.
Global Instance plus_op_lid : Lid plus := {lid := plus_lid}.
Global Instance plus_op_rid : Rid plus := {rid := plus_rid}.
Global Instance plus_op_lcancel : Lcancel plus :=
    {lcancel := (@plus_lcancel _ _ _)}.
Global Instance plus_op_rcancel : Rcancel plus :=
    {rcancel := (@plus_rcancel _ _ _)}.
Global Instance plus_op_inv : Inv plus := {inv := neg}.
Global Instance plus_op_linv : Linv plus := {linv := plus_linv}.
Global Instance plus_op_rinv : Rinv plus := {rinv := plus_rinv}.
(* end hide *)

Theorem lplus : ∀ {a b} c, a = b → c + a = c + b.
    apply lop.
Qed.
Theorem rplus : ∀ {a b} c, a = b → a + c = b + c.
    apply lop.
Qed.
Theorem lrplus : ∀ {a b c d}, a = b → c = d → a + c = b + d.
    apply lrop.
Qed.

(* begin hide *)
End PlusGroup.

Section PlusGroup2.

Context {U} `{
    p : Plus U,
    @PlusAssoc U p,
    @PlusComm U p,
    z : Zero U,
    @PlusLid U p z,
    @PlusRid U p z,
    n : Neg U,
    @PlusLinv U p z n,
    @PlusRinv U p z n
}.

Lemma plus_linv_lcancel : ∀ a b c, c + a = c + b → a = b.
    intros a b c eq.
    apply lplus with (-c) in eq.
    do 2 rewrite plus_assoc in eq.
    rewrite plus_linv in eq.
    do 2 rewrite plus_lid in eq.
    exact eq.
Qed.
Lemma plus_rinv_rcancel : ∀ a b c, a + c = b + c → a = b.
    intros a b c eq.
    apply rplus with (-c) in eq.
    do 2 rewrite <- plus_assoc in eq.
    rewrite plus_rinv in eq.
    do 2 rewrite plus_rid in eq.
    exact eq.
Qed.
Global Instance plus_linv_lcancel_class : PlusLcancel U := {
    plus_lcancel := plus_linv_lcancel
}.
Global Instance plus_rinv_rcancel_class : PlusRcancel U := {
    plus_rcancel := plus_rinv_rcancel
}.
(* end hide *)

Theorem neg_zero : -0 = 0.
    apply plus_rcancel with 0.
    rewrite plus_linv.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem neg_neg : ∀ a, --a = a.
    intros a.
    apply plus_rcancel with (-a).
    rewrite plus_linv, plus_rinv.
    reflexivity.
Qed.

Theorem neg_eq : ∀ a b, a = b → -a = -b.
    intros a b eq.
    apply lplus with (-a) in eq.
    rewrite plus_linv in eq.
    apply rplus with (-b) in eq.
    rewrite <- plus_assoc, plus_rinv, plus_rid, plus_lid in eq.
    symmetry; exact eq.
Qed.

Theorem neg_plus : ∀ a b, -(a + b) = -a + -b.
    intros a b.
    apply plus_rcancel with b.
    apply plus_lcancel with a.
    rewrite plus_comm.
    repeat rewrite <- plus_assoc.
    rewrite (plus_comm b a).
    do 2 rewrite plus_linv.
    rewrite plus_rid.
    rewrite plus_rinv.
    reflexivity.
Qed.

Theorem plus_rrinv : ∀ a b, a + b - b = a.
    intros a b.
    rewrite <- plus_assoc.
    rewrite plus_rinv.
    apply plus_rid.
Qed.
Theorem plus_rlinv : ∀ a b, a - b + b = a.
    intros a b.
    rewrite <- plus_assoc.
    rewrite plus_linv.
    apply plus_rid.
Qed.
Theorem plus_lrinv : ∀ a b, b + (-b + a) = a.
    intros a b.
    rewrite plus_assoc.
    rewrite plus_rinv.
    apply plus_lid.
Qed.
Theorem plus_llinv : ∀ a b, -b + (b + a) = a.
    intros a b.
    rewrite plus_assoc.
    rewrite plus_linv.
    apply plus_lid.
Qed.

Theorem plus_llmove : ∀ a b c, a + b = c → b = -a + c.
    intros a b c eq.
    apply lplus with (-a) in eq.
    rewrite plus_llinv in eq.
    exact eq.
Qed.
Theorem plus_lrmove : ∀ a b c, a + b = c → a = c - b.
    intros a b c eq.
    apply rplus with (-b) in eq.
    rewrite plus_rrinv in eq.
    exact eq.
Qed.
Theorem plus_rlmove : ∀ a b c, a = b + c → -b + a = c.
    intros a b c eq.
    apply lplus with (-b) in eq.
    rewrite plus_llinv in eq.
    exact eq.
Qed.
Theorem plus_rrmove : ∀ a b c, a = b + c → a - c = b.
    intros a b c eq.
    apply rplus with (-c) in eq.
    rewrite plus_rrinv in eq.
    exact eq.
Qed.

Theorem plus_llneg : ∀ a b, a + b = 0 → b = -a.
    intros a b eq.
    apply plus_llmove in eq.
    rewrite plus_rid in eq.
    exact eq.
Qed.
Theorem plus_lrneg : ∀ a b, a + b = 0 → a = -b.
    intros a b eq.
    apply plus_lrmove in eq.
    rewrite plus_lid in eq.
    exact eq.
Qed.
Theorem plus_rlneg : ∀ a b, 0 = a + b → -a = b.
    intros a b eq.
    apply plus_rlmove in eq.
    rewrite plus_rid in eq.
    exact eq.
Qed.
Theorem plus_rrneg : ∀ a b, 0 = a + b → -b = a.
    intros a b eq.
    apply plus_rrmove in eq.
    rewrite plus_lid in eq.
    exact eq.
Qed.

Theorem plus_ll0 : ∀ a b, a + b = b → a = 0.
    intros a b eq.
    apply plus_lrmove in eq.
    rewrite plus_rinv in eq.
    exact eq.
Qed.
Theorem plus_lr0 : ∀ a b, a + b = a → b = 0.
    intros a b eq.
    apply plus_llmove in eq.
    rewrite plus_linv in eq.
    exact eq.
Qed.
Theorem plus_rl0 : ∀ a b, b = a + b → 0 = a.
    intros a b eq.
    apply plus_rrmove in eq.
    rewrite plus_rinv in eq.
    exact eq.
Qed.
Theorem plus_rr0 : ∀ a b, a = a + b → 0 = b.
    intros a b eq.
    apply plus_rlmove in eq.
    rewrite plus_linv in eq.
    exact eq.
Qed.

Theorem plus_eq_lneg : ∀ a b, a = b → 0 = -a + b.
    intros a b eq.
    rewrite <- (plus_rid a) in eq.
    apply plus_llmove in eq.
    exact eq.
Qed.
Theorem plus_eq_rneg : ∀ a b, a = b → 0 = a - b.
    intros a b eq.
    rewrite <- (plus_lid b) in eq.
    symmetry in eq.
    apply plus_lrmove in eq.
    exact eq.
Qed.

Theorem plus_llneg_eq : ∀ a b, -a + b = 0 → b = a.
    intros a b eq.
    apply plus_llneg in eq.
    rewrite neg_neg in eq.
    exact eq.
Qed.
Theorem plus_lrneg_eq : ∀ a b, a - b = 0 → a = b.
    intros a b eq.
    apply plus_lrneg in eq.
    rewrite neg_neg in eq.
    exact eq.
Qed.
Theorem plus_rlneg_eq : ∀ a b, 0 = -a + b → a = b.
    intros a b eq.
    apply plus_rlneg in eq.
    rewrite neg_neg in eq.
    exact eq.
Qed.
Theorem plus_rrneg_eq : ∀ a b, 0 = a - b → b = a.
    intros a b eq.
    apply plus_rrneg in eq.
    rewrite neg_neg in eq.
    exact eq.
Qed.

(* begin hide *)
End PlusGroup2.
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
