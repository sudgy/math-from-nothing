Require Import init.

Require Import set.

Require Export analysis_norm.
Require Import norm_mult.

(* begin hide *)
Section NormFunction.

Context {U V} `{
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

    USM : ScalarMult real U,
    @ScalarComp real U real_mult_class USM,
    @ScalarId real U real_one USM,
    @ScalarLdist real U UP USM,
    @ScalarRdist real U real_plus_class UP USM,
    @ScalarLMult real U UM USM,
    @ScalarRMult real U UM USM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP,
    @AbsPositive U UA,
    @AbsCauchySchwarz U UA UM,
    @AbsMult U UA UM,
    @AbsScalar U UA USM,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    VM : Mult V,
    VO : One V,
    VD : Div V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusRid V VP VZ,
    @PlusLinv V VP VZ VN,
    @PlusRinv V VP VZ VN,
    @MultComm V VM,
    @MultAssoc V VM,
    @Ldist V VP VM,
    @Rdist V VP VM,
    @MultLid V VM VO,
    @MultRid V VM VO,
    @MultLinv V VZ VM VO VD,
    @MultRinv V VZ VM VO VD,
    NotTrivial V,

    VSM : ScalarMult real V,
    @ScalarComp real V real_mult_class VSM,
    @ScalarId real V real_one VSM,
    @ScalarLdist real V VP VSM,
    @ScalarRdist real V real_plus_class VP VSM,
    @ScalarLMult real V VM VSM,
    @ScalarRMult real V VM VSM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsCauchySchwarz V VA VM,
    @AbsMult V VA VM,
    @AbsScalar V VA VSM
}.

Existing Instance abs_metric.
(* end hide *)
Definition func_bounded {A : U → Prop} (f : set_type A → V)
    := ∃ M, ∀ x, |f x| <= M.

Theorem abs_func_lim : ∀ (A : U → Prop) (xf : set_type A → V) c l,
        func_lim A xf c l → func_lim A (λ x, |xf x|) c (|l|).
    intros A xf c l xf_lim.
    pose proof (land xf_lim) as Ac.
    rewrite metric_func_seq_lim in xf_lim by exact Ac.
    rewrite metric_func_seq_lim by exact Ac.
    intros xn xnc.
    apply abs_seq_lim.
    apply xf_lim.
    exact xnc.
Qed.

Theorem func_lim_zero : ∀ (A : U → Prop) (xf : set_type A → V) c,
        func_lim A (λ x, |xf x|) c 0 → func_lim A xf c 0.
    intros A xf c xf_lim.
    pose proof (land xf_lim) as Ac.
    rewrite metric_func_seq_lim in xf_lim by exact Ac.
    rewrite metric_func_seq_lim by exact Ac.
    intros xn xnc.
    apply seq_lim_zero.
    apply xf_lim.
    exact xnc.
Qed.

Theorem func_lim_plus : ∀ (A : U → Prop) (xf yf : set_type A → V)
        (c : U) (x y : V), func_lim A xf c x → func_lim A yf c y →
        func_lim A (λ n, xf n + yf n) c (x + y).
    intros A xf yf c x y cx cy.
    pose proof (land cx) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    intros xn xnc.
    apply seq_lim_plus.
    -   apply cx.
        exact xnc.
    -   apply cy.
        exact xnc.
Qed.

Theorem func_lim_scalar : ∀ (A : U → Prop) (xf : set_type A → V)
        (a : real) (c : U) (x : V), func_lim A xf c x →
        func_lim A (λ n, a · xf n) c (a · x).
    intros A xf a c x cx.
    pose proof (land cx) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    intros xn xnc.
    apply seq_lim_scalar.
    apply cx.
    exact xnc.
Qed.

Theorem func_lim_neg : ∀ (A : U → Prop) (xf : set_type A → V)
        (c : U) (x : V), func_lim A xf c x →
        func_lim A (λ n, -xf n) c (-x).
    intros A xf c x cx.
    pose proof (land cx) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    intros xn xnc.
    apply seq_lim_neg.
    apply cx.
    exact xnc.
Qed.

Theorem func_lim_mult : ∀ (A : U → Prop) (xf yf : set_type A → V)
        (c : U) (x y : V), func_lim A xf c x → func_lim A yf c y →
        func_lim A (λ n, xf n * yf n) c (x * y).
    intros A xf yf c x y cx cy.
    pose proof (land cx) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    intros xn xnc.
    apply seq_lim_mult.
    -   apply cx.
        exact xnc.
    -   apply cy.
        exact xnc.
Qed.

Theorem func_lim_constant : ∀ (A : U → Prop) (xf : set_type A → V)
        (a : V) (c : U) (x : V), func_lim A xf c x →
        func_lim A (λ n, a * xf n) c (a * x).
    intros A xf a c x cx.
    pose proof (land cx) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    intros xn xnc.
    apply seq_lim_constant.
    apply cx.
    exact xnc.
Qed.

Theorem func_lim_div : ∀ (A : U → Prop) (xf : set_type A → V)
        (c : U) (x : V), 0 ≠ x → func_lim A xf c x →
        func_lim A (λ n, /xf n) c (/x).
    intros A xf c x x_nz cx.
    pose proof (land cx) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    intros xn xnc.
    apply seq_lim_div; [>|exact x_nz].
    apply cx.
    exact xnc.
Qed.

Theorem func_lim_zero_mult : ∀ (A : U → Prop) (af bf : set_type A → V) c,
        func_bounded af → func_lim A bf c 0 → func_lim A (λ x, af x * bf x) c 0.
    intros A af bf c [M M_bound] bf_lim.
    pose proof (land bf_lim) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    intros xn xnc.
    apply seq_lim_zero_mult; [>|apply bf_lim; exact xnc].
    exists M.
    intros n.
    apply M_bound.
Qed.

Theorem func_lim_zero_mult2 : ∀ (A : U → Prop) (af bf : set_type A → V) c x,
        func_lim A af c x → func_lim A bf c 0 →
        func_lim A (λ x, af x * bf x) c 0.
    intros A af bf c x af_lim bf_lim.
    pose proof (land af_lim) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    intros xn xnc.
    apply (seq_lim_zero_mult2 _ _ x).
    -   apply af_lim.
        exact xnc.
    -   apply bf_lim.
        exact xnc.
Qed.
(* begin hide *)
End NormFunction.
(* end hide *)
