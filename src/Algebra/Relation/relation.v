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

Class WellOrdered {U} (op : U → U → Prop) := {
    well_ordered : ∀ S : U → Prop, (∃ x, S x) → ∃ x, S x ∧ ∀ y, S y → op x y
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

(* begin hide *)
Lemma neq_sym_ {U : Type} : ∀ x y : U, x ≠ y → y ≠ x.
Proof.
    intros x y neq eq.
    subst.
    contradiction.
Qed.
(* end hide *)
Theorem neq_sym {U : Type} : ∀ x y : U, (x ≠ y) = (y ≠ x).
Proof.
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
Infix "≤" := le.
Infix "<" := (strict le).
Arguments le: simpl never.

Class PartialOrder U `{
    UO : Order U,
    UOR : Reflexive U le,
    UOA : Antisymmetric U le,
    UOT : Transitive U le
}.

Class TotalOrder U `{
    TOP : PartialOrder U,
    UOC : Connex U le
}.

Class WellOrder U `{
    WOT : TotalOrder U,
    WOW : WellOrdered U le
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

(* begin hide *)
Section TotalOrder.

Context {U} {op : U → U → Prop} `{
    Connex U op,
    Antisymmetric U op,
    Transitive U op,
    Reflexive U op
}.

Global Instance lt_irrefl : Irreflexive (strict op).
Proof.
    split.
    intros x [leq neq].
    contradiction.
Qed.

Global Instance lt_asym : Asymmetric (strict op).
Proof.
    split.
    intros x y [leq neq] [cleq cneq].
    pose proof (antisym leq cleq).
    contradiction.
Qed.

Global Instance lt_trans : Transitive (strict op).
Proof.
    split.
    intros x y z xy yz.
    split.
    -   destruct xy as [xy_leq xy_neq], yz as [yz_leq yz_neq].
        exact (trans xy_leq yz_leq).
    -   intro contr; subst.
        exact (asym y z yz xy).
Qed.

Global Instance lt_trichotomy : Trichotomy (strict op).
Proof.
    split.
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
(* end hide *)
Theorem nle_lt : ∀ a b, ¬op a b ↔ strict op b a.
Proof.
    intros a b.
    split; intro eq.
    -   split.
        +   destruct (connex a b); [>contradiction|assumption].
        +   intro contr; subst.
            apply eq.
            apply refl.
    -   intro contr.
        destruct eq as [leq neq].
        pose proof (antisym leq contr).
        contradiction.
Qed.

Theorem nlt_le : ∀ a b, ¬strict op a b ↔ op b a.
Proof.
    intros a b.
    rewrite <- nle_lt.
    apply not_not.
Qed.

Theorem le_lt_trans : ∀ {a b c}, op a b → strict op b c → strict op a c.
Proof.
    intros a b c ab [leq neq].
    split.
    -   apply (trans ab leq).
    -   intro contr; subst.
        pose proof (antisym leq ab).
        contradiction.
Qed.
Theorem lt_le_trans : ∀ {a b c}, strict op a b → op b c → strict op a c.
Proof.
    intros a b c [leq neq] bc.
    split.
    -   apply (trans leq bc).
    -   intro contr; subst.
        pose proof (antisym leq bc).
        contradiction.
Qed.

Theorem trans2 : ∀ {a b c}, op b c → op a b → op a c.
Proof.
    intros a b c bc ab.
    exact (trans ab bc).
Qed.

Theorem le_lt_trans2 : ∀ {a b c}, strict op b c → op a b → strict op a c.
Proof.
    intros a b c bc ab.
    exact (le_lt_trans ab bc).
Qed.
Theorem lt_le_trans2 : ∀ {a b c}, op b c → strict op a b → strict op a c.
Proof.
    intros a b c bc ab.
    exact (lt_le_trans ab bc).
Qed.

(* begin hide *)
Lemma ge_refl : Reflexive (dual_op op).
Proof.
    split.
    intros x.
    unfold dual_op.
    apply refl.
Qed.

Lemma ge_antisym : Antisymmetric (dual_op op).
Proof.
    split.
    intros a b ab ba.
    unfold dual_op in *.
    apply antisym; assumption.
Qed.

Lemma ge_trans : Transitive (dual_op op).
Proof.
    split.
    intros a b c ab bc.
    unfold dual_op in *.
    exact (trans bc ab).
Qed.

Lemma ge_connex : Connex (dual_op op).
Proof.
    split.
    intros a b.
    unfold dual_op.
    destruct (connex a b).
    -   right; assumption.
    -   left; assumption.
Qed.

Global Instance total_order_refl : Reflexive op.
Proof.
    split.
    intros x.
    destruct (connex x x); assumption.
Qed.

End TotalOrder.
Section WellOrder.

Context {U} {op : U → U → Prop} `{
    Antisymmetric U op,
    WellOrdered U op
}.

Global Instance well_order_connex : Connex op.
Proof.
    split.
    intros a b.
    apply or_to_strong.
    pose proof (well_ordered (λ x, x = a ∨ x = b)) as x_ex.
    prove_parts x_ex; [>exists a; left; reflexivity|].
    destruct x_ex as [x [x_eq x_least]].
    destruct x_eq as [x_eq|x_eq]; subst x.
    -   left.
        apply x_least.
        right; reflexivity.
    -   right.
        apply x_least.
        left; reflexivity.
Qed.

Global Instance well_order_trans : Transitive op.
Proof.
    split.
    intros a b c ab bc.
    pose proof (well_ordered (λ x, x = a ∨ x = b ∨ x = c)) as x_ex.
    prove_parts x_ex; [>exists a; left; reflexivity|].
    destruct x_ex as [x [x_eq x_least]].
    destruct x_eq as [x_eq|[x_eq|x_eq]]; subst x.
    -   apply x_least.
        right; right; reflexivity.
    -   applys_eq bc.
        apply antisym; [>exact ab|].
        apply x_least.
        left; reflexivity.
    -   applys_eq ab.
        apply antisym; [>|exact bc].
        apply x_least.
        right; left; reflexivity.
Qed.

End WellOrder.

Section HomoLe.

Context {U V W} `{TotalOrder U, TotalOrder V, TotalOrder W}.
(* end hide *)
Context (f : U → V) (g : V → W) `{
    @Injective U V f,
    @HomomorphismLe U V UO UO0 f,
    @HomomorphismLt U V UO UO0 f,
    @HomomorphismLe2 U V UO UO0 f,
    @HomomorphismLt2 U V UO UO0 f,
    @HomomorphismLe V W UO0 UO1 g,
    @HomomorphismLt V W UO0 UO1 g,
    @HomomorphismLe2 V W UO0 UO1 g,
    @HomomorphismLt2 V W UO0 UO1 g
}.

Global Instance homo_le_lt : HomomorphismLt f.
Proof.
    split.
    intros a b [leq neq].
    split.
    -   apply homo_le.
        exact leq.
    -   intros contr.
        apply inj in contr.
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
    apply inj in eq.
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

Local Instance homo_le_compose : HomomorphismLe (λ x, g (f x)).
Proof.
    split.
    intros a b leq.
    do 2 apply homo_le.
    exact leq.
Qed.

Local Instance homo_lt_compose : HomomorphismLt (λ x, g (f x)).
Proof.
    split.
    intros a b leq.
    do 2 apply homo_lt.
    exact leq.
Qed.

Local Instance homo_le2_compose : HomomorphismLe2 (λ x, g (f x)).
Proof.
    split.
    intros a b.
    rewrite <- homo_le2.
    apply homo_le2.
Qed.

Local Instance homo_lt2_compose : HomomorphismLt2 (λ x, g (f x)).
Proof.
    split.
    intros a b.
    rewrite <- homo_lt2.
    apply homo_lt2.
Qed.

(* begin hide *)
End HomoLe.
(* end hide *)
(* begin show *)
Ltac make_dual_op op' :=
    try pose proof (ge_refl (op := op'));
    try pose proof (ge_antisym (op := op'));
    try pose proof (ge_trans (op := op'));
    try pose proof (ge_connex (op := op')).
(* end show *)
