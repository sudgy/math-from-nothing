Require Import init.

Require Export analysis_base.
Require Import analysis_topology.
Require Import analysis_sequence.
Require Import analysis_continuous.
Require Export analysis_norm.

(* begin hide *)
Section NormMetric.

Context {U V} `{
    Metric U,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult real V,
    @ScalarId real V real_one SM,
    @ScalarRdist real V real_plus_class VP SM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA
}.

Existing Instance abs_metric.
(* end hide *)
Theorem continuous_plus : ∀ (f g : U → V) x,
        continuous_at f x → continuous_at g x →
        continuous_at (λ a, f a + g a) x.
    intros f g x f_cont g_cont.
    rewrite metric_continuous_seq in *.
    intros a ax.
    specialize (f_cont a ax).
    specialize (g_cont a ax).
    apply seq_lim_plus.
    -   exact f_cont.
    -   exact g_cont.
Qed.

Theorem continuous_bilinear : ∀ m x (f g : U → V),
        bilinear m → cauchy_schwarz m →
        continuous_at f x → continuous_at g x →
        continuous_at (λ a, m (f a) (g a)) x.
    intros m x f g m_bil m_cs f_cont g_cont.
    rewrite metric_continuous_seq in *.
    intros a ax.
    specialize (f_cont a ax).
    specialize (g_cont a ax).
    apply seq_lim_bilinear; assumption.
Qed.
(* begin hide *)
End NormMetric.
(* end hide *)
