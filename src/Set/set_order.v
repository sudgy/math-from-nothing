Require Import init.

Require Export relation.
Require Export set_base.
Require Export set_type.

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

Definition well_orders {U} (op : U → U → Prop) (S : U → Prop)
    := ∀ A : U → Prop, A ⊆ S → (∃ x, A x) → ∃ a, is_least op A a.

Definition initial_segment {U} `{Order U} x := λ a, a < x.

Section SetOrder.

Context {U} `{
    op : U → U → Prop,
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op
}.

Theorem chain_subset : ∀ S, is_chain op S → ∀ T, T ⊆ S → is_chain op T.
Proof.
    intros S S_chain T sub a b Ta Tb.
    apply S_chain.
    all: apply sub; assumption.
Qed.

Theorem well_orders_subset :
    ∀ S, well_orders op S → ∀ T, T ⊆ S → well_orders op T.
Proof.
    intros S S_wo T sub A A_sub A_ex.
    apply S_wo.
    -   exact (trans A_sub sub).
    -   exact A_ex.
Qed.

Theorem well_orders_chain : ∀ S, well_orders op S → is_chain op S.
Proof.
    intros S S_wo a b Sa Sb.
    specialize (S_wo ❴a, b❵).
    prove_parts S_wo.
    -   intros x [eq|eq]; rewrite <- eq; assumption.
    -   exists a.
        left; reflexivity.
    -   destruct S_wo as [x [x_in x_least]].
        destruct x_in as [eq|eq]; destruct eq.
        +   left.
            apply x_least.
            right; reflexivity.
        +   right.
            apply x_least.
            left; reflexivity.
Qed.

End SetOrder.
