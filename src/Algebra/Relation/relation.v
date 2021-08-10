Require Import init.

Class Reflexive {U} (op : U → U → Prop) := {
    refl : ∀ x, op x x;
}.
Class Irreflexive {U} (op : U → U → Prop) := {
    irrefl : ∀ x, ¬op x x;
}.
Class Symmetric {U} (op : U → U → Prop) := {
    sym : ∀ x y, op x y → op y x;
}.
Class Antisymmetric {U} (op : U → U → Prop) := {
    antisym : ∀ {x y}, op x y → op y x → x = y;
}.
Class Asymmetric {U} (op : U → U → Prop) := {
    asym : ∀ x y, op x y → ¬op y x;
}.
Class Transitive {U} (op : U → U → Prop) := {
    trans : ∀ {x y z}, op x y → op y z → op x z;
}.
Class Dense {U} (op : U → U → Prop) := {
    dense : ∀ x y, op x y → ∃ z, op x z ∧ op z y;
}.
#[universes(template)]
Class Connex {U} (op : U → U → Prop) := {
    connex : ∀ x y, {op x y} + {op y x};
}.
#[universes(template)]
Class Trichotomy {U} (op : U → U → Prop) := {
    trichotomy : ∀ x y, {op x y} + {x = y} + {op y x};
}.

Arguments refl: simpl never.
Arguments irrefl: simpl never.
Arguments sym: simpl never.
Arguments antisym: simpl never.
Arguments asym: simpl never.
Arguments trans: simpl never.
Arguments dense: simpl never.
Arguments connex: simpl never.
Arguments trichotomy: simpl never.

Definition strict {U} (op : U → U → Prop) a b := op a b ∧ a ≠ b.
Definition dual_op {U} (op : U → U → Prop) a b := op b a.

Program Instance eq_refl {U : Type} : Reflexive (U := U) equal.

(* begin hide *)
Lemma neq_sym_ {U : Type} : ∀ x y : U, x ≠ y → y ≠ x.
    intros x y neq eq.
    subst.
    contradiction.
Qed.
(* end hide *)
Theorem neq_sym {U : Type} : ∀ x y : U, (x ≠ y) = (y ≠ x).
    intros x y.
    apply propositional_ext.
    split; apply neq_sym_.
Qed.
(* Sadly, we can't declare ≠ to be symmetric because a ≠ b is actually ¬(a = b).
 *)

#[universes(template)]
Class Order U := {
    le : U → U → Prop;
}.
Infix "<=" := le.
Definition lt {U} `{Order U} := strict le.
Infix "<" := lt.

Arguments le: simpl never.

(* begin hide *)
Section TotalOrderImply.

Context {U} `{
    Order U,
    Connex U le,
    Antisymmetric U le,
    Transitive U le
}.

Lemma total_order_refl_ : ∀ a, a <= a.
    intros a.
    destruct (connex a a); assumption.
Qed.

Global Instance total_order_refl : Reflexive le := {
    refl := total_order_refl_
}.

End TotalOrderImply.


Section TotalOrder.

Context {U} {op : U → U → Prop} `{
    Connex U op,
    Antisymmetric U op,
    Transitive U op,
    Reflexive U op
}.

Lemma op_lt_irrefl_ : ∀ x, ¬(strict op x x).
    intros x [leq neq].
    contradiction.
Qed.
Global Instance op_lt_irrefl : Irreflexive (strict op) := {
    irrefl := op_lt_irrefl_
}.

Lemma op_lt_asym_ : ∀ x y, strict op x y → ¬(strict op y x).
    intros x y [leq neq] [cleq cneq].
    pose proof (antisym leq cleq).
    contradiction.
Qed.
Global Instance op_lt_asym : Asymmetric (strict op) := {
    asym := op_lt_asym_
}.

Lemma op_lt_trans_ : ∀ x y z, strict op x y → strict op y z → strict op x z.
    intros x y z [xy_leq xy_neq] [yz_leq yz_neq].
    split.
    -   exact (trans xy_leq yz_leq).
    -   intro contr; subst.
        pose proof (antisym xy_leq yz_leq).
        contradiction.
Qed.
Global Instance op_lt_trans : Transitive (strict op) := {
    trans := op_lt_trans_
}.

Lemma op_lt_trichotomy_ : ∀ x y, {strict op x y} + {x = y} + {strict op y x}.
    intros x y.
    classic_case (x = y) as [eq|neq].
    -   left; right.
        exact eq.
    -   destruct (connex x y) as [leq|leq].
        +   left; left.
            split; assumption.
        +   right.
            rewrite neq_sym in neq.
            split; assumption.
Qed.
Global Instance op_lt_trichotomy : Trichotomy (strict op) := {
    trichotomy := op_lt_trichotomy_
}.
(* end hide *)

Theorem op_nle_lt : ∀ a b, (¬op a b) = (strict op b a).
    intros a b.
    apply propositional_ext.
    split; intro eq.
    -   split.
        +   destruct (connex a b); try assumption.
            contradiction.
        +   intro contr; subst.
            apply eq.
            apply refl.
    -   intro contr.
        destruct eq as [leq neq].
        pose proof (antisym leq contr).
        contradiction.
Qed.

Theorem op_nlt_le : ∀ a b, (¬strict op a b) = (op b a).
    intros a b.
    apply propositional_ext.
    split; intro eq.
    -   unfold lt, strict in eq.
        rewrite not_and in eq.
        rewrite not_not in eq.
        destruct eq as [neq|eq].
        +   destruct (connex a b); try assumption.
            contradiction.
        +   subst.
            apply refl.
    -   intros [leq neq].
        pose proof (antisym leq eq).
        contradiction.
Qed.

Theorem op_le_lt_trans : ∀ {a b c}, op a b → strict op b c → strict op a c.
    intros a b c ab [leq neq].
    split.
    -   apply (trans ab leq).
    -   intro contr; subst.
        pose proof (antisym leq ab).
        contradiction.
Qed.
Theorem op_lt_le_trans : ∀ {a b c}, strict op a b → op b c → strict op a c.
    intros a b c [leq neq] bc.
    split.
    -   apply (trans leq bc).
    -   intro contr; subst.
        pose proof (antisym leq bc).
        contradiction.
Qed.

Theorem trans2 : ∀ {a b c}, op b c → op a b → op a c.
    intros a b c bc ab.
    exact (trans ab bc).
Qed.

Theorem le_lt_trans2 : ∀ {a b c}, strict op b c → op a b → strict op a c.
    intros a b c bc ab.
    exact (op_le_lt_trans ab bc).
Qed.
Theorem lt_le_trans2 : ∀ {a b c}, op b c → strict op a b → strict op a c.
    intros a b c bc ab.
    exact (op_lt_le_trans ab bc).
Qed.

(* begin hide *)
Lemma ge_refl : Reflexive (dual_op op).
    split.
    intros x.
    unfold dual_op.
    apply refl.
Qed.

Lemma ge_antisym : Antisymmetric (dual_op op).
    split.
    intros a b ab ba.
    unfold dual_op in *.
    apply antisym; assumption.
Qed.

Lemma ge_trans : Transitive (dual_op op).
    split.
    intros a b c ab bc.
    unfold dual_op in *.
    exact (trans bc ab).
Qed.

Lemma ge_connex : Connex (dual_op op).
    split.
    intros a b.
    unfold dual_op.
    destruct (connex a b).
    -   right; assumption.
    -   left; assumption.
Qed.

End TotalOrder.
(* end hide *)

(* begin show *)
Ltac make_dual_op op' :=
    try pose proof (ge_refl (op := op'));
    try pose proof (ge_antisym (op := op'));
    try pose proof (ge_trans (op := op'));
    try pose proof (ge_connex (op := op')).
(* end show *)

(* begin hide *)
Section TotalOrder2.

Context {U} `{
    Order U,
    Connex U le,
    Antisymmetric U le,
    Transitive U le,
    Reflexive U le
}.

Lemma lt_irrefl_ : ∀ x, ¬x < x.
    apply op_lt_irrefl.
Qed.
Global Instance lt_irrefl : Irreflexive lt := {
    irrefl := lt_irrefl_
}.

Lemma lt_asym_ : ∀ x y, x < y → ¬y < x.
    apply op_lt_asym.
Qed.
Global Instance lt_asym : Asymmetric lt := {
    asym := lt_asym_
}.

Lemma lt_trans_ : ∀ x y z, x < y → y < z → x < z.
    apply op_lt_trans.
Qed.
Global Instance lt_trans : Transitive lt := {
    trans := lt_trans_
}.

Lemma lt_trichotomy_ : ∀ x y, {x < y} + {x = y} + {y < x}.
    apply op_lt_trichotomy.
Qed.
Global Instance lt_trichotomy : Trichotomy lt := {
    trichotomy := lt_trichotomy_
}.
(* end hide *)

Theorem nle_lt : ∀ a b, (¬a <= b) = (b < a).
    apply op_nle_lt.
Qed.

Theorem nlt_le : ∀ a b, (¬a < b) = (b <= a).
    apply op_nlt_le.
Qed.

Theorem le_lt_trans : ∀ {a b c}, a <= b → b < c → a < c.
    intros a b c ab bc.
    apply (op_le_lt_trans ab bc).
Qed.
Theorem lt_le_trans : ∀ {a b c}, a < b → b <= c → a < c.
    intros a b c ab bc.
    apply (op_lt_le_trans ab bc).
Qed.

(* begin hide *)
End TotalOrder2.
(* end hide *)
