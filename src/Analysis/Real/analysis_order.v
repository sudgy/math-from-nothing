Require Import init.

Require Import order_minmax.
Require Import plus_sum.
Require Import mult_pow.

Require Export analysis_norm.
Require Import analysis_topology.
Require Import analysis_sequence.
Require Import analysis_series.

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

Theorem seq_squeeze : ∀ an bn cn l, (∀ n, an n <= bn n ∧ bn n <= cn n) →
        seq_lim an l → seq_lim cn l → seq_lim bn l.
    intros an bn cn l leqs anl cnl.
    rewrite metric_seq_lim in *.
    intros ε ε_pos.
    cbn in *.
    specialize (anl ε ε_pos) as [N1 anl].
    specialize (cnl ε ε_pos) as [N2 cnl].
    exists (max N1 N2).
    intros n n_geq.
    specialize (anl n (trans (lmax N1 N2) n_geq)).
    specialize (cnl n (trans (rmax N1 N2) n_geq)).
    specialize (leqs n) as [leq1 leq2].
    rewrite abs_minus in *.
    apply abs_lt.
    apply abs_lt in anl as [anl1 anl2].
    apply abs_lt in cnl as [cnl1 cnl2].
    split.
    -   apply (lt_le_trans anl1).
        apply le_rplus.
        exact leq1.
    -   apply (le_lt_trans2 cnl2).
        apply le_rplus.
        exact leq2.
Qed.

Local Open Scope nat_scope.

Theorem alternating_series_test : ∀ an,
        (∀ n, an (nat_suc n) <= an n) →
        seq_lim an 0 →
        seq_converges (series (λ n, (-(1))^n * an n)).
    intros an an_dec an0'.
    pose proof an0' as an0.
    rewrite metric_seq_lim in an0.
    pose (an' n := (-(1))^n * an n).
    fold an'.
    pose (an'_even n := series an' (2*n)).
    pose (an'_odd n := series an' (2*n + 1)).
    assert (∀ n, an'_odd n = an'_even n + an (2*n)) as even_odd.
    {
        intros n.
        unfold an'_odd, an'_even.
        rewrite plus_comm.
        change (1 + 2*n) with (nat_suc (2*n)).
        cbn.
        rewrite plus_lid.
        unfold an' at 2.
        rewrite pow_neg_one_even.
        rewrite mult_lid.
        reflexivity.
    }
    assert (∀ m n, an (m + n) <= an n) as an_dec2.
    {
        intros m n.
        nat_induction m.
        -   rewrite plus_lid.
            apply refl.
        -   rewrite nat_plus_lsuc.
            apply (trans2 IHm).
            apply an_dec.
    }
    assert (∀ n, 0 <= an n) as an_pos.
    {
        intros n.
        classic_contradiction contr.
        rewrite nle_lt in contr.
        apply neg_pos2 in contr.
        specialize (an0 _ contr) as [N an0].
        destruct (connex n N) as [leq|leq].
        -   specialize (an0 N (refl N)).
            cbn in an0.
            rewrite plus_lid in an0.
            apply nat_le_ex in leq as [c eq]; subst N.
            specialize (an_dec2 c n).
            apply le_neg in an_dec2.
            pose proof (lt_le_trans an0 an_dec2) as ltq.
            pose proof (lt_le_trans contr an_dec2) as pos.
            rewrite plus_comm in ltq.
            rewrite abs_pos_eq in ltq by apply pos.
            destruct ltq; contradiction.
        -   specialize (an0 n leq).
            cbn in an0.
            rewrite plus_lid in an0.
            rewrite abs_pos_eq in an0 by apply contr.
            destruct an0; contradiction.
    }
    assert (∀ n, 0 <= an'_even n) as even_pos.
    {
        intros n.
        nat_induction n.
        -   unfold an'_even.
            rewrite mult_ranni.
            apply refl.
        -   unfold an'_even.
            rewrite nat_mult_rsuc.
            change (2 + 2*n) with (nat_suc (nat_suc (2*n))).
            cbn.
            do 2 rewrite plus_lid.
            rewrite <- (plus_rid 0).
            rewrite <- plus_assoc.
            apply le_lrplus; [>exact IHn|].
            unfold an'.
            change (nat_suc (2*n)) with (1 + 2*n).
            rewrite (plus_comm 1 (2*n)).
            rewrite pow_neg_one_even.
            rewrite pow_neg_one_odd.
            rewrite mult_lid.
            rewrite mult_neg_one.
            apply le_plus_0_anb_b_a.
            rewrite plus_comm.
            apply an_dec.
    }
    assert (∀ n, 0 <= an'_odd n) as odd_pos.
    {
        intros n.
        rewrite even_odd.
        rewrite <- (plus_rid 0).
        apply le_lrplus.
        -   apply even_pos.
        -   apply an_pos.
    }
    assert (seq_converges an'_odd) as [l l_odd].
    {
        apply decreasing_seq_converges.
        -   exists (an 0).
            intros n.
            rewrite abs_pos_eq by apply odd_pos.
            nat_induction n.
            +   unfold an'_odd.
                rewrite mult_ranni, plus_lid.
                unfold one; cbn.
                do 2 rewrite plus_lid.
                unfold an'; cbn.
                rewrite mult_lid.
                apply refl.
            +   apply (trans2 IHn).
                unfold an'_odd.
                rewrite nat_mult_rsuc.
                rewrite <- plus_assoc.
                change (2 + (2*n + 1)) with (nat_suc (nat_suc (2*n + 1))).
                cbn.
                do 2 rewrite plus_lid.
                unfold series.
                rewrite <- (plus_rid (sum _ _ _)) at 2.
                rewrite <- plus_assoc.
                apply le_lplus.
                unfold an'.
                change (nat_suc (2 * n + 1)) with (1 + (2*n + 1)) at 1.
                rewrite (plus_comm 1 (2*n + 1)).
                rewrite <- plus_assoc.
                rewrite <- (mult_rid 2) at 4.
                rewrite <- ldist.
                rewrite pow_neg_one_even, pow_neg_one_odd.
                rewrite mult_lid, mult_neg_one.
                apply le_plus_nab_0_b_a.
                apply an_dec.
        -   intros n.
            unfold an'_odd.
            rewrite nat_mult_rsuc.
            rewrite <- plus_assoc.
            change (2 + (2*n + 1)) with (nat_suc (nat_suc (2*n + 1))).
            cbn.
            rewrite <- (plus_rid (series _ _)).
            rewrite <- plus_assoc.
            apply le_lplus.
            do 2 rewrite plus_lid.
            unfold an'; cbn.
            rewrite pow_neg_one_odd.
            do 2 rewrite mult_neg_one.
            rewrite neg_neg.
            rewrite mult_lid.
            apply le_plus_nab_0_b_a.
            apply an_dec.
    }
    assert (seq_lim an'_even l) as l_even.
    {
        replace an'_even with (λ n, an'_odd n - an (2 * n)).
        2: {
            apply functional_ext; intros n.
            rewrite <- plus_rrmove.
            apply even_odd.
        }
        rewrite <- (plus_rid l).
        apply seq_lim_plus; [>exact l_odd|].
        rewrite <- neg_zero.
        apply seq_lim_neg.
        apply (subsequence_lim_eq _ _ _ an0').
        exists (λ n, 2*n).
        split; [>|reflexivity].
        split.
        -   rewrite nat_mult_rsuc.
            rewrite <- (plus_lid (2*n)) at 1.
            apply le_rplus.
            exact true.
        -   intros contr.
            rewrite nat_mult_rsuc in contr.
            rewrite <- (plus_lid (2*n)) in contr at 1.
            apply plus_rcancel in contr.
            inversion contr.
    }
    exists l.
    apply seq_lim_even_odd.
    -   exact l_even.
    -   exact l_odd.
Qed.
(* begin hide *)
End AnalysisOrder.
(* end hide *)
