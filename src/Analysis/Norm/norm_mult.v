Require Import init.

Require Export analysis_norm.
Require Import norm_continuous.
Require Import analysis_series.
Require Import order_minmax.

(* begin hide *)
Section NormMult.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    UD : Div U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusRid U UP UZ,
    @PlusLinv U UP UZ UN,
    @PlusRinv U UP UZ UN,
    @MultComm U UM,
    @MultAssoc U UM,
    @Ldist U UP UM,
    @Rdist U UP UM,
    @MultLid U UM UO,
    @MultRid U UM UO,
    @MultLinv U UZ UM UO UD,
    @MultRinv U UZ UM UO UD,
    NotTrivial U,

    SM : ScalarMult real U,
    @ScalarComp real U real_mult SM,
    @ScalarId real U real_one SM,
    @ScalarLdist real U UP SM,
    @ScalarRdist real U real_plus UP SM,
    @ScalarLMult real U UM SM,
    @ScalarRMult real U UM SM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP,
    @AbsPositive U UA,
    @MultBounded U UA UM,
    @AbsMult U UA UM,
    @AbsScalar U UA SM
}.

Existing Instance abs_metric.
(* end hide *)
Theorem mult_bilinear : bilinear mult.
Proof.
    repeat split.
    -   apply scalar_lmult.
    -   apply scalar_rmult.
    -   apply rdist.
    -   apply ldist.
Qed.

Theorem seq_lim_mult : ∀ xf yf (x y : U), seq_lim xf x → seq_lim yf y →
    seq_lim (λ n, xf n * yf n) (x * y).
Proof.
    intros xf yf x y.
    apply seq_lim_bilinear.
    -   exact mult_bilinear.
    -   unfold bilinear_bounded.
        apply mult_bound.
Qed.

Theorem continuous_mult : ∀ x (f g : U → U),
    continuous_at f x → continuous_at g x → continuous_at (λ a, f a * g a) x.
Proof.
    intros x f g.
    apply continuous_bilinear.
    -   exact mult_bilinear.
    -   unfold bilinear_bounded.
        apply mult_bound.
Qed.

Theorem seq_lim_constant : ∀ a x xf, seq_lim xf x →
    seq_lim (λ n, a * xf n) (a * x).
Proof.
    intros a x xf xf_x.
    pose (af (n : nat) := a).
    assert ((λ n, a * xf n) = (λ n, af n * xf n)) as f_eq by reflexivity.
    rewrite f_eq.
    apply seq_lim_mult.
    2: exact xf_x.
    apply constant_seq_lim.
Qed.

Theorem seq_lim_div : ∀ a af, seq_lim af a →
    0 ≠ a → seq_lim (λ n, /(af n)) (/a).
Proof.
    intros a af a_lim a_neq.
    rewrite metric_seq_lim in *.
    intros ε ε_pos.
    assert (0 < |a|) as a_pos.
    {
        split.
        -   apply abs_pos.
        -   intro contr.
            rewrite abs_def in contr.
            contradiction.
    }
    assert (0 < |a|/2) as a2_pos.
    {
        apply half_pos.
        exact a_pos.
    }
    pose proof (a_lim _ a2_pos) as [N1 a_pos'].
    assert (∃ D, 0 < D ∧ ∀ n, N1 ≤ n → D < |af n|) as [D [D_pos af_pos]].
    {
        exists (|a|/2).
        split.
        1: exact a2_pos.
        intros n n_gt.
        specialize (a_pos' n n_gt).
        cbn in a_pos'.
        apply (le_lt_trans (abs_reverse_tri _ _)) in a_pos'.
        rewrite abs_minus in a_pos'.
        apply (le_lt_trans (abs_le_neg _)) in a_pos'.
        rewrite neg_plus, neg_neg in a_pos'.
        apply lt_plus_llmove in a_pos'.
        rewrite neg_neg in a_pos'.
        apply lt_plus_rrmove in a_pos'.
        rewrite <- (plus_half (|a|)) in a_pos' at 1.
        rewrite plus_rrinv in a_pos'.
        exact a_pos'.
    }
    clear a_pos'.
    pose proof (lt_mult (lt_mult ε_pos a_pos) D_pos) as ε'_pos.
    specialize (a_lim _ ε'_pos) as [N2 a_lim].
    exists (max N1 N2).
    intros n n_gt.
    specialize (a_lim n (trans (rmax _ _) n_gt)).
    specialize (af_pos n (trans (lmax _ _) n_gt)).
    cbn in *.
    pose proof (trans D_pos af_pos) as afn_pos.
    assert (zero ≠ af n) as afn_nz.
    {
        intro contr.
        rewrite <- contr in afn_pos.
        rewrite abs_zero in afn_pos.
        destruct afn_pos; contradiction.
    }
    apply lt_div_pos in af_pos; try assumption.
    rewrite abs_div in af_pos by exact afn_nz.
    apply lt_mult_rrmove_pos in a_lim.
    2: exact D_pos.
    destruct af_pos as [af_pos C0]; clear C0.
    apply le_lmult_pos with (|af n - a|) in af_pos.
    2: apply abs_pos.
    rewrite abs_minus in a_lim.
    pose proof (le_lt_trans af_pos a_lim) as eq.
    apply lt_mult_rrmove_pos in eq.
    2: exact a_pos.
    rewrite abs_div in eq by exact a_neq.
    do 2 rewrite <- abs_mult in eq.
    do 2 rewrite rdist in eq.
    do 2 rewrite mult_lneg in eq.
    rewrite (mult_comm a), <- mult_assoc in eq.
    rewrite mult_lrinv in eq by exact afn_nz.
    rewrite mult_rrinv in eq by exact a_neq.
    exact eq.
Qed.

Theorem seq_lim_zero_mult : ∀ an bn, seq_norm_bounded an → seq_lim bn 0 →
    seq_lim (λ n, an n * bn n) 0.
Proof.
    intros an bn [M M_bound] bn_zero.
    classic_case (0 = M) as [M_z|M_nz].
    {
        subst M.
        assert ((λ n, an n * bn n) = (λ n, 0)) as eq.
        {
            apply functional_ext.
            intros n.
            specialize (M_bound n).
            apply (antisym (abs_pos _)) in M_bound.
            rewrite abs_def in M_bound.
            rewrite <- M_bound.
            apply mult_lanni.
        }
        rewrite eq.
        apply constant_seq_lim.
    }
    assert (0 < M) as M_pos.
    {
        split; [>|exact M_nz].
        apply (trans2 (M_bound 0)).
        apply abs_pos.
    }
    rewrite metric_seq_lim in *.
    intros ε ε_pos.
    pose proof (div_pos M_pos) as M'_pos.
    pose proof (lt_mult ε_pos M'_pos) as ε'_pos.
    specialize (bn_zero _ ε'_pos) as [N bn_zero].
    exists N.
    intros n n_geq.
    specialize (bn_zero n n_geq).
    cbn in *.
    rewrite plus_lid in *.
    rewrite abs_neg in *.
    rewrite abs_mult.
    specialize (M_bound n).
    apply le_rmult_pos with (|bn n|) in M_bound; [>|apply abs_pos].
    apply (le_lt_trans M_bound).
    rewrite lt_mult_llmove_pos by exact M_pos.
    rewrite mult_comm.
    exact bn_zero.
Qed.

Theorem seq_lim_zero_mult2 : ∀ an bn x, seq_lim an x → seq_lim bn 0 →
    seq_lim (λ n, an n * bn n) 0.
Proof.
    intros an bn x anx bn0.
    apply seq_lim_zero_mult; [>|exact bn0].
    apply converges_bounded.
    exists x.
    exact anx.
Qed.
(* begin hide *)
End NormMult.
(* end hide *)
