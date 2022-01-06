Require Import init.

Require Export linear_base.

Definition qf_polar {U V} `{Plus U, Neg U, Plus V}
    (Q : V → U) (a b : V) := Q (a + b) - Q a - Q b.

Definition quadratic_form U V `{Plus U, Neg U, Mult U, Plus V, ScalarMult U V}
    (Q : V → U)
    := (∀ a v, Q (a · v) = a * a * Q v) ∧
       (∀ u v w, qf_polar Q (u + v) w = qf_polar Q u w + qf_polar Q v w) ∧
       (∀ u v w, qf_polar Q u (v + w) = qf_polar Q u v + qf_polar Q u w) ∧
       (∀ a u v, qf_polar Q (a · u) v = a * qf_polar Q u v) ∧
       (∀ a u v, qf_polar Q u (a · v) = a * qf_polar Q u v).
