Require Import init.

Require Import analysis_topology.
Require Import norm_mult.
Require Import real_ivt.

(* begin hide *)
Section Sqrt.

Existing Instance real_order_topology.
(* end hide *)
Theorem sqrt_ex : ∀ a : real, 0 <= a → ∃ b, b * b = a ∧ 0 <= b.
Proof.
    intros a a_pos.
    classic_case (0 = a) as [a_z|a_nz].
    1: {
        exists 0.
        subst.
        split.
        -   apply mult_lanni.
        -   apply refl.
    }
    classic_case (a = 1) as [a_o|a_no].
    1: {
        exists 1.
        subst.
        split.
        -   apply mult_lid.
        -   apply one_pos.
    }
    pose (f (x : real) := x*x).
    assert (continuous f) as f_con.
    {
        intros x.
        rewrite <- real_metric_topology_eq.
        apply continuous_mult; apply identity_continuous.
    }
    assert (f 0 < a) as a_gt.
    {
        unfold f.
        rewrite mult_lanni.
        split; assumption.
    }
    destruct (connex a 1) as [leq|leq].
    -   assert (a < f 1) as a_lt.
        {
            unfold f.
            rewrite mult_lid.
            split; assumption.
        }
        pose proof (real_ivt f f_con 0 1 a one_pos a_gt a_lt)
            as [b b_eq].
        exists b.
        split; apply b_eq.
    -   assert (a < f a) as a_lt.
        {
            unfold f.
            apply lt_mult_rcancel_pos with (/a).
            1: apply div_pos; split; assumption.
            rewrite mult_rinv by exact a_nz.
            rewrite mult_rrinv by exact a_nz.
            rewrite neq_sym in a_no.
            split; assumption.
        }
        pose proof (real_ivt f f_con 0 a a (make_and a_pos a_nz) a_gt a_lt)
            as [b b_eq].
        exists b.
        split; apply b_eq.
Qed.

Definition sqrt (x : set_type (λ a : real, 0 <= a))
    := ex_val (sqrt_ex [x|] [|x]).

Theorem sqrt_squares : ∀ x, sqrt(x) * sqrt(x) = [x|].
Proof.
    intros [x x_pos]; cbn.
    unfold sqrt.
    rewrite_ex_val a a_eq.
    apply a_eq.
Qed.
Theorem sqrt_pos : ∀ x, 0 <= sqrt(x).
Proof.
    intros [x x_pos]; cbn.
    unfold sqrt.
    rewrite_ex_val a a_eq.
    apply a_eq.
Qed.
(* begin hide *)
End Sqrt.
(* end hide *)
