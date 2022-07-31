Require Import init.

Require Import order_minmax.
Require Import plus_sum.

Require Export analysis_norm.

Definition series {V} `{Plus V, Zero V} (a : nat → V) (n : nat) := sum a 0 n.

Definition cauchy_series {V} `{Plus V, Zero V, AbsoluteValue V} (a : nat → V)
    := ∀ ε, 0 < ε → ∃ N, ∀ i j, N <= i → |sum a i j| < ε.
(* begin hide *)

Section AnalysisSeries.

Context {V} `{
    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult real V,
    @ScalarId real V real_one SM,
    @ScalarLdist real V VP SM,
    @ScalarRdist real V real_plus VP SM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsScalar V VA SM
}.

Existing Instance abs_metric.
(* end hide *)

Definition abs_converges (a : nat → V) := seq_converges (series (λ n, |a n|)).

Theorem series_scalar : ∀ af a c, seq_lim (series af) a →
        seq_lim (series (λ n, c · af n)) (c · a).
    intros af a c a_lim.
    assert (series (λ n, c · af n) = (λ n, c · sum af 0 n)) as f_eq.
    {
        apply functional_ext.
        intros n.
        nat_induction n.
        -   unfold series.
            unfold zero; cbn.
            rewrite scalar_ranni.
            reflexivity.
        -   cbn.
            unfold series in IHn.
            rewrite IHn.
            rewrite scalar_ldist.
            reflexivity.
    }
    rewrite f_eq.
    apply seq_lim_scalar.
    exact a_lim.
Qed.

Theorem series_sum : ∀ af bf a b, seq_lim (series af) a → seq_lim (series bf) b
        → seq_lim (series (λ n, af n + bf n)) (a + b).
    intros af bf a b a_lim b_lim.
    assert (series (λ n, af n + bf n) = (λ n, series af n + series bf n))
        as f_eq.
    {
        apply functional_ext.
        intros n.
        nat_induction n.
        -   unfold zero; cbn.
            rewrite plus_rid.
            reflexivity.
        -   cbn.
            unfold series in IHn.
            rewrite IHn.
            do 2 rewrite <- plus_assoc.
            apply lplus.
            do 2 rewrite plus_assoc.
            apply rplus.
            apply plus_comm.
    }
    rewrite f_eq.
    apply seq_lim_plus; assumption.
Qed.

Theorem series_converges_cauchy :
        ∀ af, seq_converges (series af) → cauchy_series af.
    intros af af_conv.
    apply converges_cauchy in af_conv.
    intros ε ε_pos.
    specialize (af_conv ε ε_pos) as [N af_conv].
    exists N.
    intros i j i_ge.
    assert (N <= i + j) as j_ge.
    {
        apply (trans i_ge).
        rewrite <- (plus_rid i) at 1.
        apply le_lplus.
        apply nat_le_zero.
    }
    specialize (af_conv (i + j) i j_ge i_ge).
    unfold series in af_conv; cbn in af_conv.
    rewrite sum_minus in af_conv.
    rewrite plus_lid in af_conv.
    exact af_conv.
Qed.

Theorem cauchy_series_converges : complete V →
        ∀ af, cauchy_series af → seq_converges (series af).
    intros V_comp af af_conv.
    apply V_comp.
    intros ε ε_pos.
    specialize (af_conv ε ε_pos) as [N af_conv].
    exists N.
    intros i j i_ge j_ge.
    unfold series; cbn.
    destruct (connex i j) as [leq|leq].
    -   apply nat_le_ex in leq as [c eq]; subst.
        rewrite abs_minus.
        rewrite sum_minus.
        rewrite plus_lid.
        apply af_conv.
        exact i_ge.
    -   apply nat_le_ex in leq as [c eq]; subst.
        rewrite sum_minus.
        rewrite plus_lid.
        apply af_conv.
        exact j_ge.
Qed.
(* begin hide *)
End AnalysisSeries.

Section AnalysisSeries.

Context {V} `{
    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult real V,
    @ScalarId real V real_one SM,
    @ScalarLdist real V VP SM,
    @ScalarRdist real V real_plus VP SM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsScalar V VA SM
}.

Existing Instance abs_metric.
(* end hide *)

Theorem abs_converge_test : complete V → ∀ af,
        abs_converges af → seq_converges (series af).
    intros V_comp af af_conv.
    apply (cauchy_series_converges V_comp).
    intros ε ε_pos.
    unfold abs_converges in af_conv.
    apply series_converges_cauchy in af_conv.
    specialize (af_conv ε ε_pos) as [N af_conv].
    exists N.
    intros i j i_geq.
    specialize (af_conv i j i_geq) as ltq.
    apply (le_lt_trans2 ltq).
    clear ε ε_pos N af_conv i_geq ltq.
    assert (0 <= sum (λ n, |af n|) i j) as sum_pos.
    {
        nat_induction j.
        -   unfold zero at 2; cbn.
            apply refl.
        -   cbn.
            rewrite <- (plus_rid 0).
            apply le_lrplus; [>exact IHj|].
            apply abs_pos.
    }
    rewrite (abs_pos_eq _ sum_pos).
    clear sum_pos.
    nat_induction j.
    -   unfold zero; cbn.
        rewrite <- abs_zero.
        apply refl.
    -   cbn.
        apply (trans (abs_tri _ _)).
        apply le_rplus.
        exact IHj.
Qed.

Theorem series_skip : ∀ an n,
        seq_converges (series an) ↔ seq_converges (series (λ m, an (m + n))).
    intros an n.
    split.
    -   intros [x anx].
        exists (x - sum an 0 n).
        rewrite metric_seq_lim in *.
        intros ε ε_pos.
        specialize (anx ε ε_pos) as [N anx].
        exists N.
        intros m m_geq.
        specialize (anx (n + m) (trans m_geq (nat_le_self_lplus m n))).
        cbn in *.
        unfold series in *.
        rewrite sum_argument_plus.
        rewrite plus_lid.
        rewrite <- plus_assoc.
        rewrite <- neg_plus.
        rewrite <- (plus_lid n) at 2.
        rewrite sum_plus.
        exact anx.
    -   intros [x anx].
        exists (x + sum an 0 n).
        rewrite metric_seq_lim in *.
        intros ε ε_pos.
        specialize (anx ε ε_pos) as [N anx].
        exists (N + n).
        intros m m_geq.
        apply nat_le_ex in m_geq as [c eq]; subst m.
        specialize (anx (N + c) (nat_le_self_rplus _ _)).
        cbn in *.
        unfold series in *.
        rewrite sum_argument_plus in anx.
        rewrite plus_lid in anx.
        rewrite <- (neg_neg (sum an 0 n)).
        rewrite <- plus_assoc.
        rewrite <- neg_plus.
        rewrite (plus_comm (-sum an 0 n)).
        rewrite (plus_comm N n).
        rewrite <- plus_assoc.
        rewrite sum_minus.
        rewrite plus_lid.
        exact anx.
Qed.
(* begin hide *)
End AnalysisSeries.
(* end hide *)
