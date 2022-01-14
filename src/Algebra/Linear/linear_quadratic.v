Require Import init.

Require Import set.

Require Export linear_base.
Require Export linear_bilinear_form.

Definition qf_polar {U V} `{Plus U, Neg U, Plus V}
    (Q : V → U) (a b : V) := Q (a + b) - Q a - Q b.

Definition quadratic_form U V `{Plus U, Neg U, Mult U, Plus V, ScalarMult U V}
    (Q : V → U)
    := (∀ a v, Q (a · v) = a * a * Q v) ∧ bilinear_form (qf_polar Q).

Section QuadraticForm.

Context {U V} `{
    Plus U,
    Neg U,
    Mult U,
    Plus V,
    ScalarMult U V
}.

Variable Q : set_type (quadratic_form U V).

Theorem qf_eq : ∀ a v, [Q|] (a · v) = a * a * [Q|] v.
    apply [|Q].
Qed.
Theorem qf_polar_lscalar : ∀ a u v,
        qf_polar [Q|] (a · u) v = a * (qf_polar [Q|] u v).
    apply [|Q].
Qed.
Theorem qf_polar_rscalar : ∀ a u v,
        qf_polar [Q|] u (a · v) = a * (qf_polar [Q|] u v).
    apply [|Q].
Qed.
Theorem qf_polar_lplus : ∀ u v w,
        qf_polar [Q|] (u + v) w = qf_polar [Q|] u w + qf_polar [Q|] v w.
    apply [|Q].
Qed.
Theorem qf_polar_rplus : ∀ u v w,
        qf_polar [Q|] u (v + w) = qf_polar [Q|] u v + qf_polar [Q|] u w.
    apply [|Q].
Qed.

End QuadraticForm.
