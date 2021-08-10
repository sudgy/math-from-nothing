Require Import init.

Require Export analysis_norm.
Require Export analysis_sequence.
Require Import analysis_topology.

Require Import plus_sum.

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
    @ScalarRdist real V real_plus_class VP SM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsScalar V VA SM
}.

Existing Instance abs_metric.
(* end hide *)

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
(* end hide *)
