Require Import init.

Require Import set.

Require Export linear_base.
Require Export linear_bilinear_form.

Definition qf_polar {U V} `{Plus U, Neg U, Plus V}
    (Q : V → U) (a b : V) := Q (a + b) - Q a - Q b.

Definition quadratic_form U V `{Plus U, Neg U, Mult U, Plus V, ScalarMult U V}
    (Q : V → U)
    := (∀ a v, Q (a · v) = a * a * Q v) ∧ bilinear_form (qf_polar Q).

(* begin hide *)
Section QuadraticForm.

Context {U V} `{
    Plus U,
    Neg U,
    Mult U,
    Plus V,
    ScalarMult U V
}.

(* end hide *)
Variable Q : set_type (quadratic_form U V).

Theorem qf_eq : ∀ a v, [Q|] (a · v) = a * a * [Q|] v.
Proof.
    apply [|Q].
Qed.
Theorem qf_polar_lscalar : ∀ a u v,
    qf_polar [Q|] (a · u) v = a * (qf_polar [Q|] u v).
Proof.
    apply [|Q].
Qed.
Theorem qf_polar_rscalar : ∀ a u v,
    qf_polar [Q|] u (a · v) = a * (qf_polar [Q|] u v).
Proof.
    apply [|Q].
Qed.
Theorem qf_polar_lplus : ∀ u v w,
    qf_polar [Q|] (u + v) w = qf_polar [Q|] u w + qf_polar [Q|] v w.
Proof.
    apply [|Q].
Qed.
Theorem qf_polar_rplus : ∀ u v w,
    qf_polar [Q|] u (v + w) = qf_polar [Q|] u v + qf_polar [Q|] u w.
Proof.
    apply [|Q].
Qed.
(* begin hide *)

End QuadraticForm.
(* end hide *)
