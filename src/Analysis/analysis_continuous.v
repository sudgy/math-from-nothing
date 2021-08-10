Require Import init.

Require Export analysis_base.
Require Import analysis_topology.
Require Import analysis_sequence.
Require Import analysis_compact.
Require Import analysis_function.

Definition uniformly_continuous {U V} `{Metric U, Metric V} (f : U → V) :=
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ (∀ a x, d a x < δ → d (f a) (f x) < ε).

(* begin hide *)
Section AnalysisContinuous.

Context {U V} `{Metric U, Metric V}.
(* end hide *)

Theorem metric_continuous_at : ∀ (f : U → V) a, continuous_at f a ↔
        (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ (∀ x, d a x < δ → d (f a) (f x) < ε)).
    intros f a.
    rewrite basis_continuous_at.
    split.
    -   intros cont ε ε_pos.
        pose proof (open_ball_basis (f a) [_|ε_pos]) as fa_basis.
        pose proof (open_ball_self (f a) [_|ε_pos]) as fa_in.
        specialize (cont _ fa_basis fa_in) as [S [[S_open Sa] sub]].
        specialize (S_open a Sa) as [B [B_basis [Ba sub2]]].
        destruct B_basis as [z [δ' eq]]; subst B.
        pose proof (open_ball_ex _ _ _ Ba) as [δ sub3].
        exists [δ|].
        split.
        +   exact [|δ].
        +   intros x x_lt.
            apply sub3 in x_lt.
            apply sub2 in x_lt.
            assert (image_under f S (f x)) as fx_lt.
            {
                exists x.
                split; trivial.
            }
            apply sub in fx_lt.
            exact fx_lt.
    -   intros cont T T_basis Tfa.
        destruct T_basis as [z [ε' eq]]; subst T.
        pose proof (open_ball_ex _ _ _ Tfa) as [ε sub].
        specialize (cont [ε|] [|ε]) as [δ [δ_pos cont]].
        exists (open_ball a [δ|δ_pos]).
        split.
        +   split.
            *   apply open_ball_open.
            *   apply open_ball_self.
        +   intros fx [x [x_lt eq]]; subst fx.
            apply sub.
            apply cont.
            exact x_lt.
Qed.

Theorem metric_continuous_seq : ∀ (f : U → V) x, continuous_at f x ↔
        (∀ a, seq_lim a x → seq_lim (λ n, f (a n)) (f x)).
    intros f x.
    split.
    -   apply continuous_seq.
    -   intros seqs.
        rewrite metric_continuous_at.
        intros ε ε_pos.
        classic_contradiction contr.
        rewrite not_ex in contr.
        assert (∀ δ, 0 < δ → ∃ a, d x a < δ ∧ ¬ d (f x) (f a) < ε) as contr2.
        {
            intros δ δ_pos.
            specialize (contr δ).
            not_simpl in contr.
            destruct contr as [contr|contr]; try contradiction.
            destruct contr as [a contr].
            rewrite not_impl in contr.
            exists a.
            exact contr.
        }
        assert (∀ n, 0 < nat0_to_real (nat0_suc n)) as n_pos.
        {
            intros n.
            change 0 with (nat0_to_real 0).
            rewrite nat0_to_real_lt.
            apply nat0_zero_lt_suc.
        }
        assert (∀ n, 0 < /(nat0_to_real (nat0_suc n))) as n_pos'.
        {
            intros n.
            apply div_pos.
            apply n_pos.
        }
        pose (a n := ex_val (contr2 _ (n_pos' n))).
        assert (seq_lim a x) as lim.
        {
            rewrite metric_seq_lim.
            intros ε' ε'_pos.
            pose proof (archimedean2 ε' ε'_pos) as [N N_ltq].
            exists N.
            intros n n_gt.
            unfold a.
            rewrite_ex_val b b_eq.
            destruct b_eq as [b_lt b_nlt].
            apply (trans b_lt).
            rewrite <- nat0_sucs_le in n_gt.
            rewrite <- nat0_to_real_le in n_gt.
            apply le_div_pos in n_gt.
            2: apply n_pos.
            apply (le_lt_trans n_gt).
            rewrite nat0_to_abstract_real in N_ltq.
            exact N_ltq.
        }
        specialize (seqs _ lim).
        rewrite metric_seq_lim in seqs.
        specialize (seqs ε ε_pos) as [N seqs].
        specialize (seqs N (refl N)).
        unfold a in seqs.
        rewrite_ex_val b [b_lt b_nlt].
        contradiction.
Qed.

Theorem unformly_implies_continuous : ∀ f : U → V,
        uniformly_continuous f → continuous f.
    intros f f_cont x.
    rewrite metric_continuous_at.
    intros ε ε_pos.
    specialize (f_cont ε ε_pos) as [δ [δ_pos f_cont]].
    exists δ.
    split.
    -   exact δ_pos.
    -   apply f_cont.
Qed.

Theorem compact_continuous_uniformly : compact U → ∀ f : U → V,
        continuous f → uniformly_continuous f.
    intros U_comp f f_cont ε ε_pos.
    pose (S a (δ : real_pos) := ∀ x, d a x < [δ|] → d (f a) (f x) < ε / 2).
    assert (∀ a, ∃ δ, S a δ) as δ_ex.
    {
        intros a.
        specialize (f_cont a).
        rewrite metric_continuous_at in f_cont.
        pose proof (half_pos _ ε_pos) as ε2_pos.
        destruct (f_cont _ ε2_pos) as [δ [δ_pos f_cont2]].
        exists [δ|δ_pos].
        exact f_cont2.
    }
    pose (to_ball a := open_ball a (ex_val (δ_ex a))).
    pose (C := image_under to_ball all).
    assert (open_covering C) as C_cover.
    {
        split.
        -   intros a C0; clear C0.
            exists (to_ball a).
            split.
            +   exists a.
                split; reflexivity.
            +   apply open_ball_self.
        -   intros T' [T [allT T_eq]].
            rewrite T_eq.
            apply open_ball_open.
    }
    pose proof (lebesgue_number_lemma U_comp C C_cover) as [δ δ_leb].
    exists [δ|].
    split.
    1: exact [|δ].
    intros x y ltq1.
    pose proof (δ_leb x) as [T [CT sub_T]].
    pose proof (open_ball_self x δ) as ltq2.
    destruct CT as [a [C0 T_eq]]; clear C0.
    subst T.
    apply sub_T in ltq1, ltq2.
    unfold to_ball in ltq1, ltq2.
    rewrite_ex_val δ2 δ2_ltq.
    apply δ2_ltq in ltq1.
    apply δ2_ltq in ltq2.
    rewrite d_sym in ltq2.
    pose proof (lt_lrplus ltq2 ltq1) as ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans2 ltq).
    apply d_tri.
Qed.

Theorem uniform_converge_continuous : ∀ fn (f : U → V),
        f_seq_lim_uniform fn f → (∀ n, continuous (fn n)) → continuous f.
    intros fn f f_uni f_cont a.
    rewrite metric_continuous_at.
    intros ε ε_pos.
    pose proof (half_pos ε ε_pos) as ε2_pos.
    pose proof (half_pos (ε / 2) ε2_pos) as ε4_pos.
    specialize (f_uni _ ε4_pos) as [N f_uni].
    specialize (f_uni N (refl N)).
    specialize (f_cont N a).
    rewrite metric_continuous_at in f_cont.
    specialize (f_cont _ ε2_pos) as [δ [δ_pos f_cont]].
    exists δ.
    split; try exact δ_pos.
    intros x δ_ltq.
    specialize (f_cont x δ_ltq).
    pose proof (f_uni x) as x_ltq.
    pose proof (f_uni a) as a_ltq.
    pose proof (lt_lrplus x_ltq a_ltq) as ltq.
    rewrite plus_half in ltq.
    apply (lt_lrplus f_cont) in ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans2 ltq).
    apply (trans (d_tri (f a) (fn N a) (f x))).
    rewrite d_sym.
    rewrite plus_comm.
    rewrite plus_assoc.
    apply le_rplus.
    apply d_tri.
Qed.

(* begin hide *)
End AnalysisContinuous.
(* end hide *)
