Require Import init.

Require Export relation.

Definition is_least {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → op x y.
Definition is_greatest {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → op y x.
Definition is_minimal {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → y ≠ x → ¬(op y x).
Definition is_maximal {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → y ≠ x → ¬(op x y).
Definition has_least {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_least op S x.
Definition has_greatest {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_greatest op S x.
Definition has_minimal {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_minimal op S x.
Definition has_maximal {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_maximal op S x.

Definition open_interval {U} `{Order U} a b := λ x, a < x ∧ x < b.
Definition open_closed_interval {U} `{Order U} a b := λ x, a < x ∧ x ≤ b.
Definition closed_open_interval {U} `{Order U} a b := λ x, a ≤ x ∧ x < b.
Definition closed_interval {U} `{Order U} a b := λ x, a ≤ x ∧ x ≤ b.
Definition open_inf_interval {U} `{Order U} a := λ x, a < x.
Definition closed_inf_interval {U} `{Order U} a := λ x, a ≤ x.
Definition inf_open_interval {U} `{Order U} a := λ x, x < a.
Definition inf_closed_interval {U} `{Order U} a := λ x, x ≤ a.

Definition is_chain {U} (op : U → U → Prop) (S : U → Prop)
    := ∀ a b : U, S a → S b → op a b ∨ op b a.

Definition well_orders {U} (op : U → U → Prop) :=
    inhabited (Connex op) ∧
    inhabited (Antisymmetric op) ∧
    inhabited (Transitive op) ∧
    inhabited (WellOrdered op).

(* begin hide *)
Section WellOrders.
(* end hide *)
Context {U : Type} {op : U → U → Prop} `{
    Connex U op,
    Antisymmetric U op,
    Transitive U op,
    WellOrdered U op
}.

Theorem wo_wo : well_orders op.
Proof.
    repeat (split; try assumption).
Qed.
(* begin hide *)

End WellOrders.
(* end hide *)
