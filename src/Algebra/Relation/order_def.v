Require Import init.

Require Export relation.
Require Import order_plus.

Definition is_least {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → op x y.
Definition is_greatest {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → op y x.
Definition is_minimal {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → y ≠ x → ¬(op y x).
Definition is_maximal {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → y ≠ x → ¬(op x y).
Definition is_lower_bound {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := ∀ y, S y → op x y.
Definition is_upper_bound {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := ∀ y, S y → op y x.
Definition is_infimum {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := is_lower_bound op S x ∧ ∀ y, is_lower_bound op S y → op y x.
Definition is_supremum {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := is_upper_bound op S x ∧ ∀ y, is_upper_bound op S y → op x y.
Definition has_least {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_least op S x.
Definition has_greatest {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_greatest op S x.
Definition has_minimal {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_minimal op S x.
Definition has_maximal {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_maximal op S x.
Definition has_lower_bound {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_lower_bound op S x.
Definition has_upper_bound {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_upper_bound op S x.
Definition has_infimum {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_infimum op S x.
Definition has_supremum {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_supremum op S x.

Definition open_interval {U} `{Order U} a b := λ x, a < x ∧ x < b.
Definition open_closed_interval {U} `{Order U} a b := λ x, a < x ∧ x <= b.
Definition closed_open_interval {U} `{Order U} a b := λ x, a <= x ∧ x < b.
Definition closed_interval {U} `{Order U} a b := λ x, a <= x ∧ x <= b.
Definition open_inf_interval {U} `{Order U} a := λ x, a < x.
Definition closed_inf_interval {U} `{Order U} a := λ x, a <= x.
Definition inf_open_interval {U} `{Order U} a := λ x, x < a.
Definition inf_closed_interval {U} `{Order U} a := λ x, x <= a.

Class WellFounded {U} (op : U → U → Prop) := {
    well_founded : ∀ S : U → Prop, (∃ x, S x) → ∃ x, is_minimal op S x
}.

Class SupremumComplete {U} (op : U → U → Prop) := {
    sup_complete : ∀ S : U → Prop, (∃ x, S x) →
        has_upper_bound op S → has_supremum op S
}.

Definition is_chain {U} (op : U → U → Prop) (S : U → Prop)
    := ∀ a b : U, S a → S b → op a b ∨ op b a.

Definition well_orders {U} (op : U → U → Prop) :=
    inhabited (Connex op) ∧
    inhabited (Antisymmetric op) ∧
    inhabited (Transitive op) ∧
    inhabited (WellFounded op).

(* begin hide *)
Section WellOrders.
(* end hide *)
Context {U : Type} {op : U → U → Prop} `{
    Connex U op,
    Antisymmetric U op,
    Transitive U op,
    WellFounded U op
}.

Theorem wo_wo : well_orders op.
    repeat (split; try assumption).
Qed.

Theorem well_ordered : ∀ S : U → Prop, (∃ x, S x) → ∃ x, is_least op S x.
    intros S S_ex.
    destruct (well_founded S S_ex) as [x [Sx x_min]].
    exists x.
    split; try exact Sx.
    intros y Sy.
    classic_contradiction contr.
    apply (x_min y Sy).
    -   intro; subst.
        destruct (connex x x); contradiction.
    -   destruct (connex x y).
        +   contradiction.
        +   exact o.
Qed.

(* begin hide *)
End WellOrders.

Section SupremumComplete.

Context {U} `{
    PLUS : Plus U,
    @PlusAssoc U PLUS,
    ZERO : Zero U,
    @PlusLid U PLUS ZERO,
    @PlusRid U PLUS ZERO,
    NEG : Neg U,
    @PlusLinv U PLUS ZERO NEG,
    @PlusRinv U PLUS ZERO NEG,
    ORD : Order U,
    @SupremumComplete U le,
    @OrderLplus U PLUS ORD,
    @OrderRplus U PLUS ORD
}.
(* end hide *)
Theorem inf_complete : ∀ S : U → Prop, (∃ x, S x) →
        has_lower_bound le S → has_infimum le S.
    intros S S_ex S_lower.
    pose (S' x := S (-x)).
    assert (∃ x, S' x) as S'_ex.
    {
        destruct S_ex as [x Sx].
        exists (-x).
        unfold S'.
        rewrite neg_neg.
        exact Sx.
    }
    assert (has_upper_bound le S') as S'_upper.
    {
        destruct S_lower as [x x_lower].
        exists (-x).
        intros y S'y.
        specialize (x_lower (-y) S'y).
        apply le_plus_leq_neg in x_lower.
        apply le_plus_llmove in x_lower.
        rewrite neg_neg, plus_rid in x_lower.
        exact x_lower.
    }
    pose proof (sup_complete S' S'_ex S'_upper) as [α [α_ub α_lub]].
    exists (-α).
    split.
    -   intros x Sx.
        assert (S' (-x)) as S'x by (unfold S'; rewrite neg_neg; exact Sx).
        specialize (α_ub (-x) S'x).
        apply le_plus_leq_neg in α_ub.
        apply le_plus_llmove in α_ub.
        rewrite neg_neg, plus_rid in α_ub.
        exact α_ub.
    -   intros y y_lower.
        assert (is_upper_bound le S' (-y)) as y_upper.
        {
            intros x S'x.
            specialize (y_lower (-x) S'x).
            apply le_plus_leq_neg in y_lower.
            apply le_plus_llmove in y_lower.
            rewrite neg_neg, plus_rid in y_lower.
            exact y_lower.
        }
        specialize (α_lub (-y) y_upper).
        apply le_plus_leq_neg in α_lub.
        apply le_plus_llmove in α_lub.
        rewrite neg_neg, plus_rid in α_lub.
        exact α_lub.
Qed.
(* begin hide *)
End SupremumComplete.
(* end hide *)
