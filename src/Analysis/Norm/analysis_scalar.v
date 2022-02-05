Require Import init.

Require Export analysis_norm.
Require Import norm_mult.

(* begin hide *)
Section NormScalar.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    NotTrivial U,

    USM : ScalarMult real U,
    @ScalarId real U real_one USM,
    @ScalarLdist real U UP USM,
    @ScalarRdist real U real_plus_class UP USM,
    @ScalarComp real U real_mult_class USM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP,
    @AbsPositive U UA,
    @AbsScalar U UA USM,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,
    NotTrivial V,

    VSM : ScalarMult real V,
    @ScalarId real V real_one VSM,
    @ScalarLdist real V VP VSM,
    @ScalarRdist real V real_plus_class VP VSM,
    @ScalarComp real V real_mult_class VSM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsScalar V VA VSM
}.

Existing Instance abs_metric.
(* end hide *)

Theorem seq_lim_scalar2 : ∀ a x af xf, seq_lim af a → seq_lim xf x →
        seq_lim (λ n, af n · xf n) (a · x).
    intros a x af xf afa xfx.

    assert (seq_lim (λ n, xf n - x) 0) as lim1.
    {
        pose proof (constant_seq_lim x) as lim1.
        apply seq_lim_neg in lim1.
        pose proof (seq_lim_plus _ _ _ _ xfx lim1) as lim2.
        cbn in lim2.
        rewrite plus_rinv in lim2.
        exact lim2.
    }
    apply (seq_lim_scalar a) in lim1.
    rewrite scalar_ranni in lim1.
    assert (seq_lim (λ n, (af n - a) · xf n) 0) as lim2.
    {
        apply seq_lim_zero.
        assert (seq_lim (λ n, |xf n | * |af n - a|) 0) as lim2.
        {
            apply abs_seq_lim in xfx.
            apply (seq_lim_zero_mult2 _ _ _ xfx).
            rewrite (abs_zero (U := real)).
            apply abs_seq_lim.
            rewrite <- (plus_rinv a).
            apply seq_lim_plus.
            -   exact afa.
            -   apply constant_seq_lim.
        }
        apply (seq_lim_eq _ _ _ lim2).
        intros n.
        rewrite mult_comm.
        rewrite abs_scalar.
        reflexivity.
    }
    pose proof (seq_lim_plus _ _ _ _ lim2 lim1) as lim3.
    cbn in lim3.
    rewrite plus_rid in lim3.
    pose proof (constant_seq_lim (a · x)) as lim4.
    pose proof (seq_lim_plus _ _ _ _ lim3 lim4) as lim5.
    cbn in lim5.
    rewrite plus_lid in lim5.
    apply (seq_lim_eq _ _ _ lim5).
    intros n.
    rewrite scalar_ldist, scalar_rdist.
    rewrite scalar_rneg, scalar_lneg.
    rewrite plus_assoc.
    rewrite plus_rlinv.
    apply plus_rlinv.
Qed.

Theorem func_lim_scalar2 : ∀ (A : U → Prop)
        (af : set_type A → real) (xf : set_type A → V)
        (c : U) (a : real) (x : V), func_lim A af c a → func_lim A xf c x →
        func_lim A (λ n, af n · xf n) c (a · x).
    intros A af xf c a x a_lim x_lim.
    pose proof (land a_lim) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    rewrite metric_func_seq_lim in a_lim by exact Ac.
    intros xn xnc.
    apply seq_lim_scalar2.
    -   apply a_lim.
        exact xnc.
    -   apply x_lim.
        exact xnc.
Qed.
(* begin hide *)

End NormScalar.
(* end hide *)
