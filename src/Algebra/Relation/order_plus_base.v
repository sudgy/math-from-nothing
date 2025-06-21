Require Import init.

Require Export relation.
Require Export plus_group.

(* To avoid infinite typeclass loops, when proving implications involving these
 * typeclasses, only make the ones global that use conditions higher in the list
 * to prove conditions lower in the list.  Assume that all previously-defined
 * plus-related typeclasses are above these in the list.
 *)

Class OrderLplus U `{Plus U, Order U} := {
    le_lplus : ∀ {a b} c, a ≤ b → c + a ≤ c + b
}.
Class OrderRplus U `{Plus U, Order U} := {
    le_rplus : ∀ {a b} c, a ≤ b → a + c ≤ b + c
}.
Class OrderLplus2 U `{Plus U, Order U} := {
    lt_lplus : ∀ {a b} c, a < b → c + a < c + b
}.
Class OrderRplus2 U `{Plus U, Order U} := {
    lt_rplus : ∀ {a b} c, a < b → a + c < b + c
}.
Class OrderPlusLcancel U `{Plus U, Order U} := {
    le_plus_lcancel : ∀ {a b} c, c + a ≤ c + b → a ≤ b
}.
Class OrderPlusRcancel U `{Plus U, Order U} := {
    le_plus_rcancel : ∀ {a b} c, a + c ≤ b + c → a ≤ b
}.
Class OrderPlusLcancel2 U `{Plus U, Order U} := {
    lt_plus_lcancel : ∀ {a b} c, c + a < c + b → a < b
}.
Class OrderPlusRcancel2 U `{Plus U, Order U} := {
    lt_plus_rcancel : ∀ {a b} c, a + c < b + c → a < b
}.

Class OrderPlusClass U `{
    OPP : AllPlusClass U,
    OPO : TotalOrder U,
    UOP : @OrderLplus U UP UO,
    UOPR : @OrderRplus U UP UO,
    UOP2 : @OrderLplus2 U UP UO,
    UOPR2 : @OrderRplus2 U UP UO,
    UOPC : @OrderPlusLcancel U UP UO,
    UOPCR : @OrderPlusRcancel U UP UO,
    UOPC2 : @OrderPlusLcancel2 U UP UO,
    UOPCR2 : @OrderPlusRcancel2 U UP UO
}.

Section OrderPlusImply.

Context {U} `{OrderPlusClass U}.

Global Instance le_lplus_rplus : OrderRplus U.
Proof.
    split.
    intros a b c leq.
    do 2 rewrite (plus_comm _ c).
    apply le_lplus.
    exact leq.
Qed.

Global Instance le_lplus_rplus2 : OrderRplus2 U.
Proof.
    split.
    intros a b c leq.
    do 2 rewrite (plus_comm _ c).
    apply lt_lplus.
    exact leq.
Qed.

Global Instance le_lcancel_rcancel : OrderPlusRcancel U.
Proof.
    split.
    intros a b c leq.
    do 2 rewrite (plus_comm _ c) in leq.
    apply le_plus_lcancel in leq.
    exact leq.
Qed.

Global Instance le_lcancel_rcancel2 : OrderPlusRcancel2 U.
Proof.
    split.
    intros a b c leq.
    do 2 rewrite (plus_comm _ c) in leq.
    apply lt_plus_lcancel in leq.
    exact leq.
Qed.

Local Remove Hints le_lplus_rplus le_lplus_rplus2 le_lcancel_rcancel
    le_lcancel_rcancel2 : typeclass_instances.

(** OrderPlusLcancel2 → OrderLplus *)
Local Instance le_lplus1 : OrderLplus U.
Proof.
    split.
    intros a b c leq.
    order_contradiction ltq.
    apply lt_plus_lcancel in ltq.
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

(** OrderLplus2 → OrderLplus *)
Local Instance le_lplus2 : OrderLplus U.
Proof.
    split.
    intros a b c leq.
    classic_case (a = b) as [eq|neq].
    1: subst; apply refl.
    apply lt_lplus.
    split; assumption.
Qed.

(** OrderPlusRcancel2 → OrderRplus *)
Local Instance le_rplus1 : OrderRplus U.
Proof.
    split.
    intros a b c leq.
    order_contradiction ltq.
    apply lt_plus_rcancel in ltq.
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

(** OrderRplus2 → OrderRplus *)
Local Instance le_rplus2 : OrderRplus U.
Proof.
    split.
    intros a b c leq.
    classic_case (a = b) as [eq|neq].
    1: subst; apply refl.
    apply lt_rplus.
    split; assumption.
Qed.

Local Remove Hints le_lplus1 le_lplus2 le_rplus1 le_rplus2
    : typeclass_instances.

(** OrderLplus + PlusLcancel → OrderLplus2 *)
Global Instance lt_lplus1 : OrderLplus2 U.
Proof.
    split.
    intros a b c ltq.
    split.
    -   apply le_lplus.
        apply ltq.
    -   intros contr.
        apply plus_lcancel in contr.
        subst.
        contradiction (irrefl _ ltq).
Qed.

(** OrderPlusLcancel → OrderLplus2 *)
Local Instance lt_lplus2 : OrderLplus2 U.
Proof.
    split.
    intros a b c ltq.
    order_contradiction leq.
    apply le_plus_lcancel in leq.
    pose proof (lt_le_trans ltq leq) as contr.
    contradiction (irrefl _ contr).
Qed.

(** OrderRplus + PlusRcancel → OrderRplus2 *)
Global Instance lt_rplus1 : OrderRplus2 U.
Proof.
    split.
    intros a b c ltq.
    split.
    -   apply le_rplus.
        apply ltq.
    -   intros contr.
        apply plus_rcancel in contr.
        subst.
        contradiction (irrefl _ ltq).
Qed.

(** OrderPlusRcancel → OrderRplus2 *)
Local Instance lt_rplus2 : OrderRplus2 U.
Proof.
    split.
    intros a b c ltq.
    order_contradiction leq.
    apply le_plus_rcancel in leq.
    pose proof (lt_le_trans ltq leq) as contr.
    contradiction (irrefl _ contr).
Qed.

Local Remove Hints lt_lplus1 lt_lplus2 lt_rplus1 lt_rplus2
    : typeclass_instances.

(** PlusLcancel + OrderPlusLcancel2 → OrderPlusLcancel *)
Local Instance le_plus_lcancel1 : OrderPlusLcancel U.
Proof.
    split.
    intros a b c leq.
    classic_case (c + a = c + b) as [eq|neq].
    -   apply plus_lcancel in eq.
        subst; apply refl.
    -   apply (lt_plus_lcancel c).
        split; assumption.
Qed.

(** OrderLplus2 → OrderPlusLcancel *)
Global Instance le_plus_lcancel2 : OrderPlusLcancel U.
Proof.
    split.
    intros a b c leq.
    order_contradiction ltq.
    apply (lt_lplus c) in ltq.
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

(** PlusLinv + OrderLplus → OrderPlusLcancel *)
Global Instance le_plus_lcancel3 : OrderPlusLcancel U.
Proof.
    split.
    intros a b c leq.
    apply le_lplus with (-c) in leq.
    do 2 rewrite plus_llinv in leq.
    exact leq.
Qed.

(** PlusRcancel + OrderPlusRcancel2 → OrderPlusRcancel *)
Local Instance le_plus_rcancel1 : OrderPlusRcancel U.
Proof.
    split.
    intros a b c leq.
    classic_case (a + c = b + c) as [eq|neq].
    -   apply plus_rcancel in eq.
        subst; apply refl.
    -   apply (lt_plus_rcancel c).
        split; assumption.
Qed.

(** OrderRplus2 → OrderPlusRcancel *)
Global Instance le_plus_rcancel2 : OrderPlusRcancel U.
Proof.
    split.
    intros a b c leq.
    order_contradiction ltq.
    apply (lt_rplus c) in ltq.
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

(** PlusRinv + OrderRplus → OrderPlusRcancel *)
Global Instance le_plus_rcancel3 : OrderPlusRcancel U.
Proof.
    split.
    intros a b c leq.
    apply le_rplus with (-c) in leq.
    do 2 rewrite plus_rrinv in leq.
    exact leq.
Qed.

Local Remove Hints le_plus_lcancel1 le_plus_lcancel2 le_plus_lcancel3
    le_plus_rcancel1 le_plus_rcancel2 le_plus_rcancel3 : typeclass_instances.

(** OrderPlusLcancel → OrderPlusLcancel2 *)
Global Instance lt_plus_lcancel1 : OrderPlusLcancel2 U.
Proof.
    split.
    intros a b c eq.
    split.
    -   apply (le_plus_lcancel c).
        apply eq.
    -   intro; subst.
        contradiction (irrefl _ eq).
Qed.

(** OrderLplus → OrderPlusLcancel2 *)
Global Instance lt_plus_lcancel2 : OrderPlusLcancel2 U.
Proof.
    split.
    intros a b c ltq.
    order_contradiction leq.
    apply (le_lplus c) in leq.
    contradiction (irrefl _ (lt_le_trans ltq leq)).
Qed.

(** OrderPlusRcancel → OrderPlusRcancel2 *)
Global Instance lt_plus_rcancel1 : OrderPlusRcancel2 U.
Proof.
    split.
    intros a b c eq.
    split.
    -   apply (le_plus_rcancel c).
        apply eq.
    -   intro; subst.
        contradiction (irrefl _ eq).
Qed.

(** OrderRplus → OrderPlusRcancel2 *)
Global Instance lt_plus_rcancel2 : OrderPlusRcancel2 U.
Proof.
    split.
    intros a b c ltq.
    order_contradiction leq.
    apply (le_rplus c) in leq.
    contradiction (irrefl _ (lt_le_trans ltq leq)).
Qed.

Local Remove Hints lt_plus_lcancel1 lt_plus_lcancel2 lt_plus_rcancel1
    lt_plus_rcancel2 : typeclass_instances.

(** OrderLplus2 → PlusLcancel *)
Local Instance plus_lcancel1 : PlusLcancel U.
Proof.
    split.
    intros a b c eq.
    destruct (trichotomy a b) as [[ltq|eq']|ltq].
    -   apply lt_lplus with c in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply lt_lplus with c in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

(** OrderPlusLcancel → PlusLcancel *)
Local Instance plus_lcancel2 : PlusLcancel U.
Proof.
    split.
    intros a b c eq.
    assert (c + a ≤ c + b) as leq1 by (rewrite eq; apply refl).
    assert (c + b ≤ c + a) as leq2 by (rewrite eq; apply refl).
    apply le_plus_lcancel in leq1.
    apply le_plus_lcancel in leq2.
    apply antisym; assumption.
Qed.

(** OrderRplus2 → PlusRcancel *)
Local Instance plus_rcancel1 : PlusRcancel U.
Proof.
    split.
    intros a b c eq.
    destruct (trichotomy a b) as [[ltq|eq']|ltq].
    -   apply lt_rplus with c in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply lt_rplus with c in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

(** OrderPlusRcancel → PlusRcancel *)
Local Instance plus_rcancel2 : PlusRcancel U.
Proof.
    split.
    intros a b c eq.
    assert (a + c ≤ b + c) as leq1 by (rewrite eq; apply refl).
    assert (b + c ≤ a + c) as leq2 by (rewrite eq; apply refl).
    apply le_plus_rcancel in leq1.
    apply le_plus_rcancel in leq2.
    apply antisym; assumption.
Qed.

Local Remove Hints plus_lcancel1 plus_lcancel2 plus_rcancel1 plus_rcancel2
    : typeclass_instances.

End OrderPlusImply.
