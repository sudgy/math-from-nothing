Require Import init.

Require Export analysis_norm.
Require Import analysis_topology.
Require Import analysis_sequence.
Require Import analysis_series.
Require Import order_minmax.
Require Import plus_sum.

(* If I ever want to do analysis on an ordered field that's not the real
 * numbers, I'll figure it out then.
 *)
(* begin hide *)
Section AnalysisOrder.

Existing Instance abs_metric.
(* end hide *)
Theorem seq_lim_pos : ∀ xf x, (∀ n, 0 <= xf n) → seq_lim xf x → 0 <= x.
    intros xf x xf_pos x_lim.
    rewrite metric_seq_lim in x_lim.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    apply neg_pos2 in contr.
    specialize (x_lim _ contr) as [N x_lim].
    specialize (x_lim N (refl N)).
    cbn in x_lim.
    rewrite abs_minus in x_lim.
    apply (le_lt_trans (abs_le_pos _)) in x_lim.
    rewrite <- (plus_lid (-x)) in x_lim at 2.
    apply lt_plus_rcancel in x_lim.
    destruct (le_lt_trans (xf_pos N) x_lim); contradiction.
Qed.

Theorem seq_lim_le : ∀ xf yf x y,
        (∀ n, xf n <= yf n) → seq_lim xf x → seq_lim yf y → x <= y.
    intros xf yf x y f_leq x_lim y_lim.
    pose (xyf n := yf n - xf n).
    apply le_plus_0_anb_b_a.
    apply (seq_lim_pos xyf).
    -   intros n; unfold xyf.
        apply le_plus_0_anb_b_a.
        apply f_leq.
    -   apply seq_lim_plus.
        +   exact y_lim.
        +   apply seq_lim_neg.
            exact x_lim.
Qed.

Theorem seq_lim_le_constant : ∀ xf x y,
        (∀ n, xf n <= y) → seq_lim xf x → x <= y.
    intros xf x y f_leq x_lim.
    apply (seq_lim_le xf (λ _, y)).
    -   exact f_leq.
    -   exact x_lim.
    -   apply constant_seq_lim.
Qed.

Theorem seq_lim_ge_constant : ∀ yf x y,
        (∀ n, x <= yf n) → seq_lim yf y → x <= y.
    intros yf x y f_leq y_lim.
    apply (seq_lim_le (λ _, x) yf).
    -   exact f_leq.
    -   apply constant_seq_lim.
    -   exact y_lim.
Qed.

Theorem increasing_seq_converges : ∀ f : nat → real,
        (∃ M, ∀ n, |f n| <= M) → (∀ n, f n <= f (nat_suc n)) →
        seq_converges f.
    intros f [M M_bound] f_inc.
    assert (∀ m n, m <= n → f m <= f n) as f_inc2.
    {
        intros m n leq.
        apply nat_le_ex in leq as [c eq].
        subst n.
        nat_induction c.
        -   rewrite plus_rid.
            apply refl.
        -   apply (trans IHc).
            rewrite nat_plus_rsuc.
            apply f_inc.
    }
    pose (S x := ∃ n, f n = x).
    assert (∃ x, S x) as S_ex by (exists (f 0); exists 0; reflexivity).
    assert (has_upper_bound le S) as S_bound.
    {
        exists M.
        intros x [n x_eq]; subst x.
        apply (trans (abs_le_pos _)).
        apply M_bound.
    }
    pose proof (sup_complete S S_ex S_bound) as [x [x_bound x_least]].
    exists x.
    rewrite metric_seq_lim.
    intros ε ε_pos.
    assert (¬is_upper_bound le S (x - ε)) as xε_lt.
    {
        intros contr.
        specialize (x_least _ contr).
        rewrite <- (plus_rid x) in x_least at 1.
        apply le_plus_lcancel in x_least.
        apply pos_neg2 in ε_pos.
        destruct (le_lt_trans x_least ε_pos); contradiction.
    }
    unfold is_upper_bound in xε_lt.
    rewrite not_all in xε_lt.
    destruct xε_lt as [y xε_lt].
    rewrite not_impl in xε_lt.
    destruct xε_lt as [[N y_eq] ltq]; subst y.
    rewrite nle_lt in ltq.
    exists N.
    intros n n_geq.
    cbn.
    rewrite abs_pos_eq.
    2: {
        apply le_plus_0_anb_b_a.
        apply x_bound.
        exists n.
        reflexivity.
    }
    apply lt_plus_rrmove.
    rewrite <- (neg_neg ε).
    apply lt_plus_llmove.
    rewrite plus_comm.
    apply (lt_le_trans ltq).
    apply f_inc2.
    exact n_geq.
Qed.

Theorem decreasing_seq_converges : ∀ f : nat → real,
        (∃ M, ∀ n, |f n| <= M) → (∀ n, f (nat_suc n) <= f n) →
        seq_converges f.
    intros f [M M_bound] f_dec.
    pose (g n := -f n).
    assert (seq_converges g) as [x x_lim].
    {
        apply increasing_seq_converges.
        -   exists M.
            unfold g.
            setoid_rewrite abs_neg.
            exact M_bound.
        -   intros n.
            unfold g.
            apply le_neg.
            apply f_dec.
    }
    exists (-x).
    apply seq_lim_neg in x_lim.
    unfold g in x_lim.
    assert ((λ n, --f n) = (λ n, f n)) as f_eq.
    {
        apply functional_ext.
        intros n.
        apply neg_neg.
    }
    rewrite f_eq in x_lim.
    exact x_lim.
Qed.

Theorem real_complete : complete real.
    intros f f_cauchy.
    pose (fn m n := f (m + n)).
    assert (∀ m, cauchy_seq (fn m)) as fn_cauchy.
    {
        intros m.
        intros ε ε_pos.
        specialize (f_cauchy ε ε_pos) as [N f_cauchy].
        exists N.
        intros i j i_ge j_ge.
        unfold fn.
        apply f_cauchy.
        all: rewrite <- (plus_lid N).
        all: apply le_lrplus.
        1, 3: apply nat_le_zero.
        1, 2: assumption.
    }
    assert (∀ m, seq_norm_bounded (fn m)) as fn_bounded.
    {
        intros m.
        apply seq_bounded_norm_bounded.
        apply cauchy_bounded.
        apply fn_cauchy.
    }
    pose (S m x := ∃ n, x = fn m n).
    assert (∀ m, ∃ a, is_supremum le (S m) a) as sup_ex.
    {
        intros m.
        apply sup_complete.
        -   exists (fn m 0).
            exists 0.
            reflexivity.
        -   specialize (fn_bounded m) as [M M_bound].
            exists M.
            unfold is_upper_bound; cbn.
            intros y [n y_eq]; subst y.
            apply (trans2 (M_bound n)).
            apply abs_le_pos.
    }
    pose (a m := ex_val (sup_ex m)).
    assert (seq_converges a) as [x x_lim].
    {
        apply decreasing_seq_converges.
        -   pose proof (fn_bounded 0) as [M M_bound].
            unfold fn in M_bound.
            setoid_rewrite plus_lid in M_bound.
            exists M.
            intros n.
            unfold a.
            rewrite_ex_val A A_sup.
            destruct A_sup as [A_upper A_least].
            unfold abs; cbn; case_if.
            +   apply A_least.
                intros y [m y_eq]; subst y.
                unfold fn.
                apply (trans2 (M_bound (n + m))).
                apply abs_le_pos.
            +   rewrite nle_lt in n0.
                assert (S n (fn n 0)) as fn_in by (exists 0; reflexivity).
                specialize (A_upper (fn n 0) fn_in).
                apply le_neg in A_upper.
                apply (trans A_upper).
                unfold fn.
                rewrite plus_rid.
                apply (trans2 (M_bound n)).
                apply abs_le_neg.
        -   intros m.
            unfold a.
            rewrite_ex_val A [A_upper A_least].
            rewrite_ex_val B [B_upper B_least].
            apply A_least.
            intros y [n y_eq]; subst y.
            apply B_upper.
            unfold S, fn.
            exists (nat_suc n).
            rewrite nat_plus_lrsuc.
            reflexivity.
    }
    exists x.
    rewrite metric_seq_lim in *; cbn in *.
    intros ε ε_pos.
    pose proof (half_pos ε ε_pos) as ε2_pos.
    pose proof (half_pos _ ε2_pos) as ε4_pos.
    specialize (f_cauchy _ ε2_pos) as [N1 f_cauchy]; cbn in f_cauchy.
    specialize (x_lim _ ε4_pos) as [N2 x_lim].
    pose (N := max N1 N2).
    exists N.
    intros n n_ge.
    assert (∃ n', N <= n' ∧ |a N - f n'| < ε/2/2) as [n' [n'_ge af_leq]].
    {
        unfold a.
        rewrite_ex_val A A_sup.
        destruct A_sup as [A_upper' A_least'].
        unfold is_upper_bound, S in A_upper'.
        assert (∀ n, fn N n <= A) as A_upper.
        {
            intros m.
            apply A_upper'.
            exists m.
            reflexivity.
        }
        assert (∀ y, (∀ n, fn N n <= y) → A <= y) as A_least.
        {
            intros y y_leq.
            apply A_least'.
            intros z [m z_eq]; subst z.
            apply y_leq.
        }
        clear A_upper' A_least'.
        classic_contradiction contr.
        rewrite not_ex in contr.
        setoid_rewrite not_and in contr.
        setoid_rewrite nle_lt in contr.
        setoid_rewrite nlt_le in contr.
        assert (A <= A - ε/2/2) as leq.
        {
            apply A_least.
            intros m.
            unfold fn.
            specialize (contr (N + m)) as [contr|contr].
            -   rewrite <- (plus_rid N) in contr at 2.
                apply lt_plus_lcancel in contr.
                contradiction (nat_lt_zero _ contr).
            -   specialize (A_upper m).
                unfold fn in A_upper.
                apply le_plus_0_anb_b_a in A_upper.
                unfold abs in contr; cbn in contr; case_if; try contradiction.
                apply le_plus_lrmove.
                apply le_plus_rrmove in contr.
                rewrite neg_neg, plus_comm in contr.
                exact contr.
        }
        rewrite <- (plus_rid A) in leq at 1.
        apply le_plus_lcancel in leq.
        apply pos_neg in leq.
        rewrite neg_neg in leq.
        clear - leq ε4_pos.
        destruct (lt_le_trans ε4_pos leq); contradiction.
    }
    specialize (x_lim N (rmax _ _)).
    specialize (f_cauchy n' n (trans (lmax _ _) n'_ge) (trans (lmax _ _) n_ge)).
    clear - f_cauchy x_lim af_leq.
    pose proof (lt_lrplus x_lim af_leq) as ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans (abs_tri _ _)) in ltq.
    rewrite <- plus_assoc in ltq.
    rewrite plus_llinv in ltq.
    clear - f_cauchy ltq.
    pose proof (lt_lrplus ltq f_cauchy) as eq.
    rewrite plus_half in eq.
    apply (le_lt_trans (abs_tri _ _)) in eq.
    rewrite <- plus_assoc in eq.
    rewrite plus_llinv in eq.
    exact eq.
Qed.

Theorem series_le_converge : ∀ a b,
        seq_converges (series b) → (∀ n, 0 <= a n) → (∀ n, a n <= b n) →
        seq_converges (series a).
    intros a b b_conv a_pos ab.
    apply cauchy_series_converges.
    1: exact real_complete.
    apply series_converges_cauchy in b_conv.
    intros ε ε_pos.
    specialize (b_conv ε ε_pos) as [N b_conv].
    exists N.
    intros i j leq.
    specialize (b_conv i j leq).
    apply (le_lt_trans2 b_conv).
    clear - a_pos ab.
    assert (0 <= sum a i j) as sum_a_pos.
    {
        clear - a_pos.
        nat_induction j.
        -   apply refl.
        -   cbn.
            specialize (a_pos (i + j)).
            pose proof (le_lrplus IHj a_pos) as leq.
            rewrite plus_rid in leq.
            exact leq.
    }
    assert (0 <= sum b i j) as sum_b_pos.
    {
        clear - a_pos ab.
        nat_induction j.
        -   apply refl.
        -   cbn.
            specialize (a_pos (i + j)).
            specialize (ab (i + j)).
            pose proof (le_lrplus IHj (trans a_pos ab)) as leq.
            rewrite plus_rid in leq.
            exact leq.
    }
    unfold abs; cbn.
    case_if; case_if; try contradiction.
    clear l l0 sum_a_pos sum_b_pos.
    nat_induction j.
    -   unfold zero; cbn.
        apply refl.
    -   cbn.
        apply le_lrplus.
        +   exact IHj.
        +   apply ab.
Qed.
(* begin hide *)
End AnalysisOrder.
(* end hide *)
