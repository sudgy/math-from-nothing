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
(* begin hide *)

End AnalysisFunction.
(* end hide *)
