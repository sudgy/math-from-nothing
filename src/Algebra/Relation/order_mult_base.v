Require Import init.

Require Export relation.
Require Export order_plus.
Require Export mult_field.

(* To avoid infinite typeclass loops, when proving implications involving these
 * typeclasses, only make the ones global that use conditions higher in the list
 * to prove conditions lower in the list.  Assume that all previously-defined
 * mult-related typeclasses are above these in the list.
 *)

Class OrderMult U `{Zero U, Mult U, Order U} := {
    le_mult : ∀ {a b}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
}.
Class OrderMult2 U `{Zero U, Mult U, Order U} := {
    lt_mult : ∀ {a b}, 0 < a → 0 < b → 0 < a * b
}.
Class OrderLmult U `{Zero U, Mult U, Order U} := {
    le_lmult_pos : ∀ {a b} c, 0 ≤ c → a ≤ b → c * a ≤ c * b
}.
Class OrderRmult U `{Zero U, Mult U, Order U} := {
    le_rmult_pos : ∀ {a b} c, 0 ≤ c → a ≤ b → a * c ≤ b * c
}.
Class OrderLmult2 U `{Zero U, Mult U, Order U} := {
    lt_lmult_pos : ∀ {a b} c, 0 < c → a < b → c * a < c * b
}.
Class OrderRmult2 U `{Zero U, Mult U, Order U} := {
    lt_rmult_pos : ∀ {a b} c, 0 < c → a < b → a * c < b * c
}.
Class OrderMultLcancel U `{Zero U, Mult U, Order U} := {
    le_mult_lcancel_pos : ∀ {a b} c, 0 < c → c * a ≤ c * b → a ≤ b
}.
Class OrderMultRcancel U `{Zero U, Mult U, Order U} := {
    le_mult_rcancel_pos : ∀ {a b} c, 0 < c → a * c ≤ b * c → a ≤ b
}.
Class OrderMultLcancel2 U `{Zero U, Mult U, Order U} := {
    lt_mult_lcancel_pos : ∀ {a b} c, 0 < c → c * a < c * b → a < b
}.
Class OrderMultRcancel2 U `{Zero U, Mult U, Order U} := {
    lt_mult_rcancel_pos : ∀ {a b} c, 0 < c → a * c < b * c → a < b
}.

Class OrderedDomainClass U `{
    OFF : IntegralDomainClass U,
    OFO : TotalOrder U,
    UOP : @OrderLplus U UP UO,
    UOPR : @OrderRplus U UP UO,
    UOPC : @OrderPlusLcancel U UP UO,
    UOPCR : @OrderPlusRcancel U UP UO,
    UOM : @OrderMult U UZ UM UO,
    UOM2 : @OrderMult2 U UZ UM UO,
    UOML : @OrderLmult U UZ UM UO,
    UOMR : @OrderRmult U UZ UM UO,
    UOM2 : @OrderLmult2 U UZ UM UO,
    UOMR2 : @OrderRmult2 U UZ UM UO,
    UOMLC : @OrderMultLcancel U UZ UM UO,
    UOMRC : @OrderMultRcancel U UZ UM UO,
    UOMC2 : @OrderMultLcancel2 U UZ UM UO,
    UOMCR2 : @OrderMultRcancel2 U UZ UM UO
}.

Class OrderedFieldClass U `{
    OFF : FieldClass U,
    OFO : TotalOrder U,
    UOP : @OrderLplus U UP UO,
    UOPR : @OrderRplus U UP UO,
    UOPC : @OrderPlusLcancel U UP UO,
    UOPCR : @OrderPlusRcancel U UP UO,
    UOM : @OrderMult U UZ UM UO,
    UOM2 : @OrderMult2 U UZ UM UO,
    UOML : @OrderLmult U UZ UM UO,
    UOMR : @OrderRmult U UZ UM UO,
    UOM2 : @OrderLmult2 U UZ UM UO,
    UOMR2 : @OrderRmult2 U UZ UM UO,
    UOMLC : @OrderMultLcancel U UZ UM UO,
    UOMRC : @OrderMultRcancel U UZ UM UO,
    UOMC2 : @OrderMultLcancel2 U UZ UM UO,
    UOMCR2 : @OrderMultRcancel2 U UZ UM UO
}.

Section OrderMultImply.

Context {U} `{OrderedFieldClass U}.

Global Instance le_lmult_rmult : OrderRmult U.
Proof.
    split.
    intros a b c c_pos leq.
    do 2 rewrite (mult_comm _ c).
    apply le_lmult_pos.
    all: assumption.
Qed.

Global Instance le_lmult_rmult2 : OrderRmult2 U.
Proof.
    split.
    intros a b c c_pos leq.
    do 2 rewrite (mult_comm _ c).
    apply lt_lmult_pos.
    all: assumption.
Qed.

Global Instance le_lcancel_rcancel : OrderMultRcancel U.
Proof.
    split.
    intros a b c c_pos leq.
    do 2 rewrite (mult_comm _ c) in leq.
    apply le_mult_lcancel_pos in leq.
    all: assumption.
Qed.

Global Instance le_lcancel_rcancel2 : OrderMultRcancel2 U.
Proof.
    split.
    intros a b c c_pos leq.
    do 2 rewrite (mult_comm _ c) in leq.
    apply lt_mult_lcancel_pos in leq.
    all: assumption.
Qed.

Local Remove Hints le_lmult_rmult le_lmult_rmult2 le_lcancel_rcancel
    le_lcancel_rcancel2 : typeclass_instances.

Theorem div_pos : ∀ {a}, 0 < a → 0 < /a.
Proof.
    intros a a_pos.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    do 2 (apply le_lmult_pos with a in contr; [>|apply a_pos]).
    rewrite mult_rinv, mult_rid in contr by apply a_pos.
    do 2 rewrite mult_ranni in contr.
    destruct (lt_le_trans a_pos contr); contradiction.
Qed.

Global Instance le_mult_lmult : OrderLmult U.
Proof.
    split.
    intros a b c c_pos leq.
    apply le_lplus with (-a) in leq.
    rewrite plus_linv in leq.
    pose proof (le_mult c_pos leq) as eq.
    rewrite ldist in eq.
    rewrite mult_rneg in eq.
    apply le_lplus with (c * a) in eq.
    rewrite plus_lrinv in eq.
    rewrite plus_rid in eq.
    exact eq.
Qed.

Global Instance le_lt_mult : OrderMult2 U.
Proof.
    split.
    intros a b a_pos b_pos.
    split.
    -   apply le_mult; [>apply a_pos|apply b_pos].
    -   apply mult_nz; [>apply a_pos|apply b_pos].
Qed.
Local Remove Hints le_mult_lmult le_lt_mult : typeclass_instances.

(** OrderMultLcancel2 → OrderLmult *)
Local Instance le_lmult1 : OrderLmult U.
Proof.
    split.
    intros a b c c_pos leq.
    classic_case (0 = c) as [c_z|c_nz].
    -   subst.
        do 2 rewrite mult_lanni.
        apply refl.
    -   order_contradiction ltq.
        apply lt_mult_lcancel_pos in ltq; [>|split; assumption].
        contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

(** OrderLmult2 → OrderLmult *)
Local Instance le_lmult2 : OrderLmult U.
Proof.
    split.
    intros a b c c_pos leq.
    classic_case (0 = c) as [c_z|c_nz].
    -   subst.
        do 2 rewrite mult_lanni.
        apply refl.
    -   classic_case (a = b) as [eq|neq].
        1: subst; apply refl.
        apply lt_lmult_pos; split; assumption.
Qed.

(** OrderMultRcancel2 → OrderRmult *)
Local Instance le_rmult1 : OrderRmult U.
Proof.
    split.
    intros a b c c_pos leq.
    classic_case (0 = c) as [c_z|c_nz].
    -   subst.
        do 2 rewrite mult_ranni.
        apply refl.
    -   order_contradiction ltq.
        apply lt_mult_rcancel_pos in ltq; [>|split; assumption].
        contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

(** OrderRmult2 → OrderRmult *)
Local Instance le_rmult2 : OrderRmult U.
Proof.
    split.
    intros a b c c_pos leq.
    classic_case (0 = c) as [c_z|c_nz].
    -   subst.
        do 2 rewrite mult_ranni.
        apply refl.
    -   classic_case (a = b) as [eq|neq].
        1: subst; apply refl.
        apply lt_rmult_pos; split; assumption.
Qed.

Local Remove Hints le_lmult1 le_lmult2 le_rmult1 le_rmult2
    : typeclass_instances.

(** OrderLmult + MultLcancel → OrderLmult2 *)
Global Instance lt_lmult1 : OrderLmult2 U.
Proof.
    split.
    intros a b c c_pos ltq.
    split.
    -   apply le_lmult_pos; [>apply c_pos|].
        apply ltq.
    -   intros contr.
        apply mult_lcancel in contr; [>|apply c_pos].
        subst.
        contradiction (irrefl _ ltq).
Qed.

(** OrderMultLcancel → OrderLmult2 *)
Local Instance lt_lmult2 : OrderLmult2 U.
Proof.
    split.
    intros a b c c_pos ltq.
    order_contradiction leq.
    apply (le_mult_lcancel_pos _ c_pos) in leq.
    pose proof (lt_le_trans ltq leq) as contr.
    contradiction (irrefl _ contr).
Qed.

(** OrderRmult + MultRcancel → OrderRmult2 *)
Global Instance lt_rmult1 : OrderRmult2 U.
Proof.
    split.
    intros a b c c_pos ltq.
    split.
    -   apply le_rmult_pos; [>apply c_pos|].
        apply ltq.
    -   intros contr.
        apply mult_rcancel in contr; [>|apply c_pos].
        subst.
        contradiction (irrefl _ ltq).
Qed.

(** OrderMultRcancel → OrderRmult2 *)
Local Instance lt_rmult2 : OrderRmult2 U.
Proof.
    split.
    intros a b c c_pos ltq.
    order_contradiction leq.
    apply (le_mult_rcancel_pos _ c_pos) in leq.
    pose proof (lt_le_trans ltq leq) as contr.
    contradiction (irrefl _ contr).
Qed.

Local Remove Hints lt_lmult1 lt_lmult2 lt_rmult1 lt_rmult2
    : typeclass_instances.

(** MultLcancel + OrderMultLcancel2 → OrderMultLcancel *)
Local Instance le_mult_lcancel1 : OrderMultLcancel U.
Proof.
    split.
    intros a b c c_pos leq.
    classic_case (c * a = c * b) as [eq|neq].
    -   apply mult_lcancel in eq; [>|apply c_pos].
        subst; apply refl.
    -   apply (lt_mult_lcancel_pos c c_pos).
        split; assumption.
Qed.

(** OrderLmult2 → OrderMultLcancel *)
Global Instance le_mult_lcancel2 : OrderMultLcancel U.
Proof.
    split.
    intros a b c c_pos leq.
    order_contradiction ltq.
    apply (lt_lmult_pos c c_pos) in ltq.
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

(** MultLinv + OrderLmult → OrderMultLcancel *)
Global Instance le_mult_lcancel3 : OrderMultLcancel U.
Proof.
    split.
    intros a b c c_pos leq.
    apply le_lmult_pos with (/c) in leq; [>|apply div_pos; exact c_pos].
    do 2 rewrite mult_llinv in leq by apply c_pos.
    exact leq.
Qed.

(** MultRcancel + OrderMultRcancel2 → OrderMultRcancel *)
Local Instance le_mult_rcancel1 : OrderMultRcancel U.
Proof.
    split.
    intros a b c c_pos leq.
    classic_case (a * c = b * c) as [eq|neq].
    -   apply mult_rcancel in eq; [>|apply c_pos].
        subst; apply refl.
    -   apply (lt_mult_rcancel_pos c c_pos).
        split; assumption.
Qed.

(** OrderRmult2 → OrderMultRcancel *)
Global Instance le_mult_rcancel2 : OrderMultRcancel U.
Proof.
    split.
    intros a b c c_pos leq.
    order_contradiction ltq.
    apply (lt_rmult_pos c c_pos) in ltq.
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

(** MultRinv + OrderRmult → OrderMultRcancel *)
Global Instance le_mult_rcancel3 : OrderMultRcancel U.
Proof.
    split.
    intros a b c c_pos leq.
    apply le_rmult_pos with (/c) in leq; [>|apply div_pos; exact c_pos].
    do 2 rewrite mult_rrinv in leq by apply c_pos.
    exact leq.
Qed.

Local Remove Hints le_mult_lcancel1 le_mult_lcancel2 le_mult_lcancel3
    le_mult_rcancel1 le_mult_rcancel2 le_mult_rcancel3 : typeclass_instances.

(** OrderMultLcancel → OrderMultLcancel2 *)
Global Instance lt_mult_lcancel1 : OrderMultLcancel2 U.
Proof.
    split.
    intros a b c c_pos eq.
    split.
    -   apply (le_mult_lcancel_pos c c_pos).
        apply eq.
    -   intro; subst.
        contradiction (irrefl _ eq).
Qed.

(** OrderLmult → OrderMultLcancel2 *)
Global Instance lt_mult_lcancel2 : OrderMultLcancel2 U.
Proof.
    split.
    intros a b c c_pos ltq.
    order_contradiction leq.
    apply (le_lmult_pos c (land c_pos)) in leq.
    contradiction (irrefl _ (lt_le_trans ltq leq)).
Qed.

(** OrderMultRcancel → OrderMultRcancel2 *)
Global Instance lt_mult_rcancel1 : OrderMultRcancel2 U.
Proof.
    split.
    intros a b c c_pos eq.
    split.
    -   apply (le_mult_rcancel_pos c c_pos).
        apply eq.
    -   intro; subst.
        contradiction (irrefl _ eq).
Qed.

(** OrderRmult → OrderMultRcancel2 *)
Global Instance lt_mult_rcancel2 : OrderMultRcancel2 U.
Proof.
    split.
    intros a b c c_pos ltq.
    order_contradiction leq.
    apply (le_rmult_pos c (land c_pos)) in leq.
    contradiction (irrefl _ (lt_le_trans ltq leq)).
Qed.

Local Remove Hints lt_mult_lcancel1 lt_mult_lcancel2 lt_mult_rcancel1
    lt_mult_rcancel2 : typeclass_instances.

End OrderMultImply.
