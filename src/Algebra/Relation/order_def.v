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

Class WellOrder U `{
    WOT : TotalOrder U,
    WOW : WellFounded U le
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
Proof.
    repeat (split; try assumption).
Qed.

Theorem well_ordered : ∀ S : U → Prop, (∃ x, S x) → ∃ x, is_least op S x.
Proof.
    intros S S_ex.
    destruct (well_founded S S_ex) as [x [Sx x_min]].
    exists x.
    split; [>exact Sx|].
    intros y Sy.
    classic_contradiction contr.
    apply (x_min y Sy).
    -   intro; subst.
        apply contr.
        apply refl.
    -   destruct (connex x y) as [xy|yx].
        +   contradiction.
        +   exact yx.
Qed.

Theorem well_ordered_founded :
    (∀ S : U → Prop, (∃ x, S x) → ∃ x, is_least op S x) →
    WellFounded op.
Proof.
    intros wf.
    split.
    intros S S_ex.
    specialize (wf S S_ex) as [x [Sx x_least]].
    exists x.
    split; [>exact Sx|].
    intros y Sy y_neq leq.
    specialize (x_least y Sy).
    pose proof (antisym leq x_least).
    contradiction.
Qed.

(* begin hide *)
End WellOrders.

Section SupremumComplete.

Context {U} `{
    OrderPlus U,
    @SupremumComplete U le
}.
(* end hide *)
Theorem inf_complete : ∀ S : U → Prop, (∃ x, S x) →
    has_lower_bound le S → has_infimum le S.
Proof.
    intros S S_ex S_lower.
    pose (S' x := S (-x)).
    pose proof (sup_complete S') as S'_sup.
    prove_parts S'_sup.
    {
        destruct S_ex as [x Sx].
        exists (-x).
        unfold S'.
        rewrite neg_neg.
        exact Sx.
    }
    {
        destruct S_lower as [x x_lower].
        exists (-x).
        intros y S'y.
        specialize (x_lower (-y) S'y).
        rewrite le_half_rneg.
        exact x_lower.
    }
    destruct S'_sup as [α [α_ub α_lub]].
    exists (-α).
    split.
    -   intros x Sx.
        rewrite le_half_lneg.
        apply α_ub.
        unfold S'.
        rewrite neg_neg.
        exact Sx.
    -   intros y y_lower.
        rewrite le_half_rneg.
        apply α_lub.
        intros x S'x.
        rewrite le_half_rneg.
        apply y_lower.
        exact S'x.
Qed.
(* begin hide *)
End SupremumComplete.
(* end hide *)
