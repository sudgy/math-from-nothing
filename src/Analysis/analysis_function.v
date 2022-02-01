Require Import init.

Require Export analysis_base.
Require Import analysis_topology.
Require Import analysis_sequence.

Require Import order_abs.
Require Import order_minmax.

Definition f_seq_lim_uniform {U V} `{Metric U, Metric V}
    (fn : sequence (U → V)) f :=
    ∀ ε, 0 < ε → ∃ N, ∀ n, N <= n → ∀ x, d (fn n x) (f x) < ε.
Definition f_seq_uniformly_converges {U V} `{Metric U, Metric V}
    (fn : sequence (U → V)) := ∃ f, f_seq_lim_uniform fn f.

(* begin hide *)
Section AnalysisFunction.

Context {U V} `{Metric U, Metric V}.

Existing Instance real_metric.
(* end hide *)
Theorem uniform_converge_sup : U → ∀ fn (f : U → V),
    f_seq_lim_uniform fn f ↔
    (seq_lim
        (λ n, match (strong_excluded_middle
                (has_supremum le (λ m, ∃ x, m = d (fn n x) (f x))))
            with
            | strong_or_left H => ex_val H
            | _ => 1
            end)
        0
    ).
    intros Ux fn f.
    split.
    -   intros f_uni.
        rewrite metric_seq_lim.
        intros ε ε_pos.
        assert (0 < min 1 ε) as min_pos.
        {
            unfold min; case_if.
            -   exact one_pos.
            -   exact ε_pos.
        }
        pose proof (half_pos ε ε_pos) as ε2_pos.
        specialize (f_uni _ ε2_pos) as [N f_uni].
        exists N.
        intros n n_ge.
        specialize (f_uni n n_ge).
        destruct (strong_excluded_middle _) as [sup|nsup].
        +   rewrite_ex_val m m_sup.
            destruct m_sup as [m_upper m_least].
            assert (m <= ε / 2) as leq.
            {
                apply m_least.
                intros c [x c_eq]; subst c.
                apply f_uni.
            }
            assert (0 <= m) as m_pos.
            {
                apply (trans (d_pos (fn n Ux) (f Ux))).
                apply m_upper.
                exists Ux.
                reflexivity.
            }
            unfold d; cbn.
            rewrite plus_lid.
            rewrite abs_neg.
            unfold abs; cbn.
            case_if; try contradiction.
            apply (le_lt_trans leq).
            rewrite <- plus_half.
            rewrite <- (plus_rid (ε / 2)) at 1.
            apply lt_lplus.
            exact ε2_pos.
        +   exfalso; apply nsup.
            apply sup_complete.
            *   exists (d (fn n Ux) (f Ux)), Ux.
                reflexivity.
            *   exists (ε / 2).
                intros m [x m_eq].
                rewrite m_eq.
                apply f_uni.
    -   intros f_conv ε ε_pos.
        rewrite metric_seq_lim in f_conv.
        assert (0 < min 1 ε) as min_pos.
        {
            unfold min; case_if.
            -   exact one_pos.
            -   exact ε_pos.
        }
        specialize (f_conv _ min_pos) as [N f_conv].
        exists N.
        intros n n_ge x.
        specialize (f_conv n n_ge).
        destruct (strong_excluded_middle _) as [sup|nsup].
        +   rewrite_ex_val m [m_upper m_least].
            cbn in *.
            unfold is_upper_bound in *.
            apply (lt_le_trans2 (rmin _ _)) in f_conv.
            rewrite plus_lid, abs_neg in f_conv.
            assert (0 <= m) as m_pos.
            {
                apply (trans (d_pos (fn n x) (f x))).
                apply m_upper.
                exists x.
                reflexivity.
            }
            unfold abs in f_conv; cbn in f_conv.
            case_if; try contradiction.
            apply (le_lt_trans2 f_conv).
            apply m_upper.
            exists x.
            reflexivity.
        +   apply (lt_le_trans2 (lmin _ _)) in f_conv.
            unfold d in f_conv; cbn in f_conv.
            rewrite plus_lid, abs_neg, abs_one in f_conv.
            destruct f_conv; contradiction.
Qed.

Theorem metric_func_lim : ∀ (A : U → Prop) (f : set_type A → V) c l,
        limit_point A c → func_lim A f c l ↔
            (∀ ε, 0 < ε →
                ∃ δ, 0 < δ ∧ ∀ x, [x|] ≠ c → d [x|] c < δ → d (f x) l < ε).
    intros A f c l Ac.
    rewrite (basis_func_lim A f c l Ac).
    split.
    -   intros l_lim ε ε_pos.
        pose proof (open_ball_basis l [ε|ε_pos]) as l_basis.
        pose proof (open_ball_self l [ε|ε_pos]) as l_in.
        specialize (l_lim _ l_basis l_in) as [S [S_basis [Sc S_sub]]].
        apply basis_open in S_basis.
        rewrite open_all_balls in S_basis.
        specialize (S_basis c Sc) as [[δ δ_pos] δ_sub].
        exists δ.
        split; [>exact δ_pos|].
        intros [x Ax] x_neq x_lt; cbn in *.
        rewrite d_sym; apply S_sub.
        exists [x|Ax]; cbn.
        repeat split; [>|rewrite neq_sym; exact x_neq].
        apply δ_sub.
        rewrite d_sym in x_lt.
        exact x_lt.
    -   intros l_lim T T_basis Tl.
        apply basis_open in T_basis.
        rewrite open_all_balls in T_basis.
        specialize (T_basis l Tl) as [[ε ε_pos] ε_sub].
        specialize (l_lim ε ε_pos) as [δ [δ_pos l_lim]].
        exists (open_ball c [δ|δ_pos]).
        split; [>|split].
        +   apply open_ball_basis.
        +   unfold open_ball.
            rewrite d_zero.
            exact δ_pos.
        +   intros y [[x Ax] [[c_lt c_neq] y_eq]]; cbn in *.
            apply ε_sub.
            rewrite y_eq.
            unfold open_ball.
            rewrite d_sym.
            apply l_lim; [>rewrite neq_sym; exact c_neq|].
            cbn.
            rewrite d_sym.
            exact c_lt.
Qed.
(* begin hide *)

End AnalysisFunction.
(* end hide *)
