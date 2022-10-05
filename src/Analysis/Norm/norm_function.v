Require Import init.

Require Import set.
Require Import order_minmax.

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
    @ScalarComp real U real_mult USM,
    @ScalarId real U real_one USM,
    @ScalarLdist real U UP USM,
    @ScalarRdist real U real_plus UP USM,
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
    @ScalarComp real V real_mult VSM,
    @ScalarId real V real_one VSM,
    @ScalarLdist real V VP VSM,
    @ScalarRdist real V real_plus VP VSM,
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
    := ∃ M, ∀ x, |f x| ≤ M.

Definition func_bounded_around {A : U → Prop} (f : set_type A → V) a
    := ∃ ε M, ∀ x, a ≠ [x|] → open_ball a ε [x|] → |f x| ≤ M.

Theorem func_lim_bounded_around : ∀ (A : U → Prop) (f : set_type A → V) c l,
    func_lim_base f c l → func_bounded_around f c.
Proof.
    intros A f c l f_lim.
    rewrite metric_func_seq_lim in f_lim.
    unfold func_bounded_around.
    classic_contradiction contr.
    rewrite not_ex in contr.
    assert (∀ ε a, ∃ x, c ≠ [x|] ∧ open_ball c ε [x|] ∧ a < |l-f x|) as contr'.
    {
        intros ε a.
        specialize (contr ε).
        rewrite not_ex in contr.
        specialize (contr (a + |l|)).
        rewrite not_all in contr.
        destruct contr as [x contr].
        do 2 rewrite not_impl in contr.
        rewrite nle_lt in contr.
        destruct contr as [x_neq [x_lt ltq]].
        exists x.
        split; [>|split]; [>exact x_neq|exact x_lt|].
        rewrite lt_plus_lrmove in ltq.
        apply (lt_le_trans2 (abs_le_pos _)) in ltq.
        apply (lt_le_trans ltq).
        rewrite abs_minus.
        apply abs_reverse_tri.
    }
    pose (a' n := ex_val (contr' [_|real_n_div_pos n] 1)).
    assert (∀ n, (A - ❴c❵)%set [a' n|]) as a_in.
    {
        intros n.
        split.
        -   exact [|a' n].
        -   rewrite singleton_eq; intros eq.
            unfold a' in eq.
            rewrite_ex_val x [x_neq xH].
            contradiction.
    }
    pose (a n := [_|a_in n]).
    specialize (f_lim a).
    assert (seq_lim (λ n, [a n|]) c) as c_lim.
    {
        unfold a, a'; cbn.
        rewrite metric_seq_lim.
        intros ε ε_pos.
        pose proof (archimedean2 ε ε_pos) as [N N_ltq].
        exists N.
        intros n n_geq.
        rewrite_ex_val x [x_neq [x_lt fx_gt]].
        unfold open_ball in x_lt; cbn in x_lt.
        cbn.
        apply (trans x_lt).
        apply (le_lt_trans2 N_ltq).
        apply le_div_pos; [>apply from_nat_pos|].
        cbn.
        apply le_lplus.
        rewrite from_nat_le.
        exact n_geq.
    }
    specialize (f_lim c_lim).
    rewrite metric_seq_lim in f_lim.
    specialize (f_lim 1 one_pos) as [N f_lim].
    specialize (f_lim N (refl _)).
    cbn in f_lim.
    unfold a' in f_lim.
    unpack_ex_val x x_eq [x_neq [x_lt ltq]].
    pose proof (trans f_lim ltq) as ltq'.
    subst x.
    apply ltq'.
    apply f_equal.
    apply f_equal.
    apply f_equal.
    apply f_equal.
    apply set_type_eq; reflexivity.
Qed.

Theorem func_bounded_around_plus : ∀ (A : U → Prop) (xf yf : set_type A → V) a,
    func_bounded_around xf a → func_bounded_around yf a →
    func_bounded_around (λ x, xf x + yf x) a.
Proof.
    intros A xf yf a [ε1 [M M_bound]] [ε2 [N N_bound]].
    exists (min ε1 ε2), (M + N).
    intros x x_neq x_in.
    apply (trans (abs_tri _ _)).
    apply le_lrplus.
    -   apply M_bound; [>exact x_neq|].
        apply (lt_le_trans x_in).
        exact (lmin ε1 ε2).
    -   apply N_bound; [>exact x_neq|].
        apply (lt_le_trans x_in).
        exact (rmin ε1 ε2).
Qed.

Theorem func_bounded_around_subset : ∀ (A B : U → Prop)
    (f : set_type A → V) (g : set_type B → V) a (H : A ⊆ B),
    (∀ x, f x = g [[x|] | H [x|] [|x]]) →
    func_bounded_around g a → func_bounded_around f a.
Proof.
    intros A B f g a sub eq [ε [M M_bound]].
    exists ε, M.
    intros [x Ax]; cbn.
    intros neq ltq.
    specialize (M_bound [x|sub x Ax] neq ltq).
    rewrite eq; cbn.
    exact M_bound.
Qed.

Theorem abs_func_lim : ∀ (A : U → Prop) (xf : set_type A → V) c l,
    func_lim_base xf c l → func_lim_base (λ x, |xf x|) c (|l|).
Proof.
    intros A xf c l xf_lim.
    rewrite metric_func_seq_lim in xf_lim.
    rewrite metric_func_seq_lim.
    intros xn xnc.
    apply abs_seq_lim.
    apply xf_lim.
    exact xnc.
Qed.

Theorem func_lim_zero : ∀ (A : U → Prop) (xf : set_type A → V) c,
    func_lim_base (λ x, |xf x|) c 0 → func_lim_base xf c 0.
Proof.
    intros A xf c xf_lim.
    rewrite metric_func_seq_lim in xf_lim.
    rewrite metric_func_seq_lim.
    intros xn xnc.
    apply seq_lim_zero.
    apply xf_lim.
    exact xnc.
Qed.

Theorem func_lim_plus : ∀ (A : U → Prop) (xf yf : set_type A → V)
    (c : U) (x y : V), func_lim_base xf c x → func_lim_base yf c y →
    func_lim_base (λ n, xf n + yf n) c (x + y).
Proof.
    intros A xf yf c x y cx cy.
    rewrite metric_func_seq_lim in *.
    intros xn xnc.
    apply seq_lim_plus.
    -   apply cx.
        exact xnc.
    -   apply cy.
        exact xnc.
Qed.

Theorem func_lim_scalar : ∀ (A : U → Prop) (xf : set_type A → V)
    (a : real) (c : U) (x : V), func_lim_base xf c x →
    func_lim_base (λ n, a · xf n) c (a · x).
Proof.
    intros A xf a c x cx.
    rewrite metric_func_seq_lim in *.
    intros xn xnc.
    apply seq_lim_scalar.
    apply cx.
    exact xnc.
Qed.

Theorem func_lim_neg : ∀ (A : U → Prop) (xf : set_type A → V)
    (c : U) (x : V), func_lim_base xf c x →
    func_lim_base (λ n, -xf n) c (-x).
Proof.
    intros A xf c x cx.
    rewrite metric_func_seq_lim in *.
    intros xn xnc.
    apply seq_lim_neg.
    apply cx.
    exact xnc.
Qed.

Theorem func_lim_mult : ∀ (A : U → Prop) (xf yf : set_type A → V)
    (c : U) (x y : V), func_lim_base xf c x → func_lim_base yf c y →
    func_lim_base (λ n, xf n * yf n) c (x * y).
Proof.
    intros A xf yf c x y cx cy.
    rewrite metric_func_seq_lim in *.
    intros xn xnc.
    apply seq_lim_mult.
    -   apply cx.
        exact xnc.
    -   apply cy.
        exact xnc.
Qed.

Theorem func_lim_constant : ∀ (A : U → Prop) (xf : set_type A → V)
    (a : V) (c : U) (x : V), func_lim_base xf c x →
    func_lim_base (λ n, a * xf n) c (a * x).
Proof.
    intros A xf a c x cx.
    rewrite metric_func_seq_lim in *.
    intros xn xnc.
    apply seq_lim_constant.
    apply cx.
    exact xnc.
Qed.

Theorem func_lim_div : ∀ (A : U → Prop) (xf : set_type A → V)
    (c : U) (x : V), 0 ≠ x → func_lim_base xf c x →
    func_lim_base (λ n, /xf n) c (/x).
Proof.
    intros A xf c x x_nz cx.
    rewrite metric_func_seq_lim in *.
    intros xn xnc.
    apply seq_lim_div; [>|exact x_nz].
    apply cx.
    exact xnc.
Qed.

Theorem func_lim_zero_mult : ∀ (A : U → Prop) (af bf : set_type A → V) c,
    func_bounded_around af c → func_lim_base bf c 0 →
    func_lim_base (λ x, af x * bf x) c 0.
Proof.
    intros A af bf c [[ε ε_pos] [M' M'_bound]] bf_lim.
    assert (∃ M, ∀ x, open_ball c [ε|ε_pos] [x|] → |af x| ≤ M) as [M M_bound].
    {
        classic_case (A c) as [Ac|Anc].
        -   exists (max M' (|af [c|Ac]|)).
            intros [x Ax] x_in.
            classic_case (c = x) as [eq|neq].
            +   subst x.
                rewrite (proof_irrelevance _ Ac).
                apply rmax.
            +   apply (trans2 (lmax _ _)).
                apply M'_bound.
                *   exact neq.
                *   exact x_in.
        -   exists M'.
            intros x.
            apply M'_bound.
            intros contr.
            subst c.
            apply Anc.
            exact [|x].
    }
    rewrite metric_func_seq_lim in *.
    intros xn xnc.
    pose proof xnc as x_lt.
    rewrite metric_seq_lim in xnc.
    specialize (xnc ε ε_pos) as [N xnc].
    rewrite (seq_lim_part _ N) in x_lt.
    rewrite (seq_lim_part _ N).
    apply seq_lim_zero_mult.
    -   exists M.
        intros n.
        apply M_bound.
        apply xnc.
        apply nat_le_self_lplus.
    -   apply bf_lim.
        exact x_lt.
Qed.

Theorem func_lim_zero_mult2 : ∀ (A : U → Prop) (af bf : set_type A → V) c x,
    func_lim_base af c x → func_lim_base bf c 0 →
    func_lim_base (λ x, af x * bf x) c 0.
Proof.
    intros A af bf c x af_lim bf_lim.
    rewrite metric_func_seq_lim in *.
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
