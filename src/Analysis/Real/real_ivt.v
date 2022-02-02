Require Import init.

Require Import topology.
Require Import analysis_topology.

(* begin hide *)
Section IVT.

Existing Instance real_order_topology.
Existing Instance subspace_topology.
(* end hide *)
(* TODO: Make the domain of this better *)
Theorem real_ivt : ∀ f : real → real, continuous f →
        ∀ a b r, a < b → f a < r → r < f b → ∃ c, f c = r ∧ a <= c ∧ c <= b.
    intros f f_cont a b r ab r_gt r_lt.
    pose (S := closed_interval a b).
    pose (g (x : set_type S) := f [x|]).
    assert (continuous g) as g_cont.
    {
        unfold g.
        apply comp_continuous.
        -   intros x A [A_open Ax].
            exists (λ x, A [x|]).
            split.
            +   split.
                *   exists A.
                    split; try exact A_open.
                    reflexivity.
                *   exact Ax.
            +   intros y y_in.
                destruct y_in as [y' [Ay' y_eq]].
                rewrite y_eq.
                exact Ay'.
        -   exact f_cont.
    }
    assert (closed_interval a b a) as a_in.
    {
        split.
        -   apply refl.
        -   apply ab.
    }
    assert (closed_interval a b b) as b_in.
    {
        split.
        -   apply ab.
        -   apply refl.
    }
    pose proof (ivt
        (closed_interval_connected a b)
        g
        g_cont
        [a|a_in]
        [b|b_in]
        r
        r_gt
        r_lt
    ) as [[c [c_gt c_lt]] eq].
    exists c.
    repeat split; assumption.
Qed.
(* begin hide *)
End IVT.
(* end hide *)
