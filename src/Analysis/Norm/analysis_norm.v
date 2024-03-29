Require Import init.

Require Export analysis_basic.
Require Export linear_bilinear.
Require Import order_minmax.
Require Export order_abs.
Require Export linear_base.

(* begin hide *)
Section NormMetric.

Context {V} `{
    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,
    NotTrivial V,

    SM : ScalarMult real V,
    @ScalarId real V real_one SM,
    @ScalarLdist real V VP SM,
    @ScalarRdist real V real_plus VP SM,
    @ScalarComp real V real_mult SM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsScalar V VA SM
}.

Existing Instance abs_metric.
(* end hide *)
Definition seq_norm_bounded (f : nat → V) := ∃ M, ∀ n, |f n| ≤ M.

Theorem abs_reverse_tri : ∀ u v, | |u| - |v| | ≤ |u - v|.
Proof.
    intros u v.
    pose proof (d_reverse_tri 0 u v) as eq.
    unfold d in eq; cbn in eq.
    do 2 rewrite plus_lid in eq.
    do 2 rewrite abs_neg in eq.
    exact eq.
Qed.

Theorem seq_bounded_norm_bounded : ∀ f, seq_bounded f ↔ seq_norm_bounded f.
Proof.
    intros f.
    split.
    -   intros [M M_bound].
        exists (|f 0| + M).
        intros n.
        cbn in M_bound.
        apply le_plus_lcancel with (-|f 0|).
        rewrite plus_llinv.
        rewrite plus_comm.
        apply (trans2 (M_bound n 0)).
        apply (trans2 (abs_reverse_tri _ _)).
        apply abs_le_pos.
    -   intros [M M_bound].
        exists (2*M).
        intros m n.
        cbn.
        pose proof (M_bound m) as leq1.
        pose proof (M_bound n) as leq2.
        rewrite <- abs_neg in leq2.
        pose proof (le_lrplus leq1 leq2) as leq.
        rewrite plus_two in leq.
        apply (trans2 leq).
        apply abs_tri.
Qed.

Theorem converges_bounded : ∀ f, seq_converges f → seq_norm_bounded f.
Proof.
    intros f f_conv.
    apply seq_bounded_norm_bounded.
    apply cauchy_bounded.
    apply converges_cauchy.
    exact f_conv.
Qed.

Theorem norm_open_limit_point : ∀ S x, open S → S x → limit_point S x.
Proof.
    intros S x S_open Sx T T_open Tx.
    assert (∀ ε x, 0 < ε → 0 ≠ x → |ε / 2 / |x| · x| < ε) as lem.
    {
        clear x Sx Tx.
        intros ε x ε_pos x_nz.
        rewrite abs_scalar.
        rewrite abs_mult.
        rewrite abs_pos_eq by (apply half_pos; exact ε_pos).
        rewrite abs_pos_eq.
        2: {
            apply div_pos.
            split; [>apply abs_pos|].
            intros contr.
            rewrite abs_def in contr.
            contradiction.
        }
        rewrite mult_rlinv.
        2: {
            intros contr.
            rewrite abs_def in contr.
            contradiction.
        }
        apply lt_mult_rcancel_pos with 2; [>apply two_pos|].
        rewrite mult_rlinv by apply two_pos.
        rewrite ldist.
        rewrite mult_rid.
        rewrite <- lt_plus_0_a_b_ab.
        exact ε_pos.
    }
    assert (∀ ε x, 0 < ε → 0 ≠ x → 0 ≠ ε / 2 / |x| · x) as lem2.
    {
        clear x Sx Tx.
        intros ε x ε_pos x_nz contr.
        rewrite <- (scalar_lanni x) in contr.
        apply scalar_rcancel in contr; [>|exact x_nz].
        rewrite <- mult_lrmove in contr.
        2: {
            intros contr2.
            rewrite abs_def in contr2.
            contradiction.
        }
        rewrite mult_lanni in contr.
        clear - ε_pos contr.
        rewrite <- mult_lrmove in contr by apply two_pos.
        rewrite mult_lanni in contr.
        destruct ε_pos; contradiction.
    }
    unfold intersects.
    apply empty_neq.
    pose proof (inter_open2 S T S_open T_open) as ST_open.
    rewrite open_all_balls in ST_open.
    classic_case (0 = x) as [x_z|x_nz].
    -   subst x.
        specialize (ST_open 0 (make_and Sx Tx)) as [[ε ε_pos] sub].
        pose proof not_trivial_zero as [x x_nz].
        pose (x' := ε / 2 / |x| · x).
        assert ((S ∩ T) x') as [Sx' Tx'].
        {
            apply sub.
            unfold open_ball; cbn.
            rewrite abs_minus.
            rewrite neg_zero, plus_rid.
            unfold x'.
            apply lem; assumption.
        }
        exists x'.
        repeat split.
        +   exact Sx'.
        +   rewrite singleton_eq.
            unfold x'.
            apply lem2; assumption.
        +   exact Tx'.
    -   specialize (ST_open x (make_and Sx Tx)) as [[ε ε_pos] sub].
        pose (x' := x + ε/2 / |x| · x).
        assert ((S ∩ T) x') as [Sx' Tx'].
        {
            apply sub.
            unfold open_ball, x'; cbn.
            rewrite neg_plus.
            rewrite plus_lrinv.
            rewrite abs_neg.
            apply lem; assumption.
        }
        exists x'.
        repeat split.
        +   exact Sx'.
        +   rewrite singleton_eq.
            unfold x'.
            rewrite <- plus_0_a_b_ba.
            apply lem2; assumption.
        +   exact Tx'.
Qed.

Theorem abs_seq_lim : ∀ xf x, seq_lim xf x → seq_lim (λ n, |xf n|) (|x|).
Proof.
    intros xf x x_lim'.
    pose proof (land (metric_seq_lim xf x) x_lim') as x_lim; clear x_lim'.
    apply metric_seq_lim.
    intros ε ε_pos.
    specialize (x_lim ε ε_pos) as [N x_lim].
    exists N.
    intros n n_ge.
    specialize (x_lim n n_ge).
    unfold d in *; cbn in *.
    apply (le_lt_trans2 x_lim).
    apply abs_reverse_tri.
Qed.

Theorem seq_lim_zero : ∀ xf, seq_lim (λ n, |xf n|) 0 → seq_lim xf 0.
Proof.
    intros xf x_lim.
    rewrite metric_seq_lim.
    rewrite metric_seq_lim in x_lim.
    intros ε ε_pos.
    specialize (x_lim ε ε_pos) as [N x_lim].
    exists N.
    intros n n_ge.
    specialize (x_lim n n_ge).
    cbn in *.
    rewrite plus_lid, abs_neg.
    rewrite plus_lid, abs_neg in x_lim.
    rewrite abs_abs in x_lim.
    exact x_lim.
Qed.

Theorem seq_lim_plus : ∀ xf yf (x y : V), seq_lim xf x → seq_lim yf y →
    seq_lim (λ n, xf n + yf n) (x + y).
Proof.
    intros xf yf x y x_lim y_lim.
    rewrite metric_seq_lim in *.
    intros ε ε_pos.
    pose proof (half_pos ε_pos) as ε2_pos.
    specialize (x_lim _ ε2_pos) as [N1 x_lim].
    specialize (y_lim _ ε2_pos) as [N2 y_lim].
    exists (max N1 N2).
    intros n n_geq.
    unfold d in *; cbn in *.
    specialize (x_lim n (trans (lmax N1 N2) n_geq)).
    specialize (y_lim n (trans (rmax N1 N2) n_geq)).
    pose proof (lt_lrplus x_lim y_lim) as eq.
    rewrite plus_half in eq.
    apply (le_lt_trans2 eq).
    rewrite neg_plus.
    rewrite <- plus_assoc, (plus_assoc y).
    rewrite (plus_comm y).
    rewrite <- plus_assoc, plus_assoc.
    apply abs_tri.
Qed.

Theorem seq_lim_scalar : ∀ a x xf, seq_lim xf x →
    seq_lim (λ n, a · xf n) (a · x).
Proof.
    intros a x xf x_lim.
    rewrite metric_seq_lim in *.
    intros ε ε_pos.
    unfold d in *; cbn in *.
    classic_case (0 = a) as [a_z|a_nz].
    {
        subst.
        exists 0.
        intros n n_ge.
        do 2 rewrite scalar_lanni.
        rewrite plus_lid, neg_zero.
        rewrite <- abs_zero.
        exact ε_pos.
    }
    assert (0 < |a|) as a_pos.
    {
        split.
        +   apply abs_pos.
        +   intros contr.
            rewrite abs_def in contr.
            contradiction.
    }
    assert (0 < ε / |a|) as εa_pos.
    {
        apply lt_mult.
        -   exact ε_pos.
        -   apply div_pos.
            exact a_pos.
    }
    specialize (x_lim _ εa_pos) as [N x_lim].
    exists N.
    intros n n_ge.
    specialize (x_lim n n_ge).
    apply lt_rmult_pos with (|a|) in x_lim.
    2: exact a_pos.
    rewrite mult_rlinv in x_lim by apply a_pos.
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    rewrite abs_scalar.
    rewrite mult_comm.
    exact x_lim.
Qed.

Theorem seq_lim_neg : ∀ xf x, seq_lim xf x → seq_lim (λ n, -xf n) (-x).
Proof.
    intros xf x x_lim.
    rewrite <- scalar_neg_one.
    assert ((λ n, -xf n) = (λ n, -(1) · xf n)) as f_eq.
    {
        apply functional_ext.
        intros n.
        rewrite scalar_neg_one.
        reflexivity.
    }
    rewrite f_eq.
    apply seq_lim_scalar.
    exact x_lim.
Qed.

Theorem seq_lim_bilinear : ∀ f xf yf (x y : V),
    bilinear f → bilinear_bounded f →
    seq_lim xf x → seq_lim yf y → seq_lim (λ n, f (xf n) (yf n)) (f x y).
Proof.
    intros f xf yf x y f_bil f_cs x_lim y_lim.
    pose proof (converges_bounded yf (ex_intro _ y y_lim))
        as [M M_bound].
    rewrite metric_seq_lim in *.
    intros ε ε_pos.
    unfold d in *; cbn in *.
    assert (zero < max M one) as M_pos.
    {
        apply (lt_le_trans one_pos).
        apply rmax.
    }
    pose proof (rand M_pos) as M_neq.
    pose proof (div_pos M_pos) as M'_pos.
    destruct f_cs as [M' f_bound].
    assert (0 < max M' 1) as M_pos'.
    {
        apply (lt_le_trans one_pos).
        apply rmax.
    }
    classic_case (zero = x) as [x_eq|x_neq].
    {
        subst x.
        pose proof (lt_mult ε_pos M'_pos) as εM_pos.
        pose proof (lt_mult (div_pos M_pos') εM_pos) as εMM_pos.
        specialize (x_lim _ εMM_pos) as [N x_lim].
        exists N.
        intros n n_gt.
        specialize (x_lim n n_gt).
        rewrite bilinear_lanni, plus_lid, abs_neg by exact f_bil.
        rewrite plus_lid, abs_neg in x_lim.
        apply lt_rmult_pos with (max M 1) in x_lim; try exact M_pos.
        rewrite mult_assoc in x_lim.
        rewrite mult_rlinv in x_lim by exact M_neq.
        specialize (M_bound n).
        apply (trans2 (lmax M one)) in M_bound.
        apply le_lmult_pos with (|xf n|) in M_bound.
        2: apply abs_pos.
        rewrite <- lt_mult_llmove_pos in x_lim by exact M_pos'.
        apply (le_lt_trans2 x_lim).
        apply (le_lmult_pos (max M' 1)) in M_bound; [>|apply M_pos'].
        apply (trans2 M_bound).
        pose proof (lmax M' 1) as leq.
        apply (le_rmult_pos (|xf n| * |yf n|)) in leq.
        2: apply le_mult; apply abs_pos.
        apply (trans2 leq).
        apply f_bound.
    }
    assert (0 ≠ |x|) as x_neq2.
    {
        intro contr.
        rewrite abs_def in contr.
        contradiction.
    }
    assert (0 < |x|) as x_pos.
    {
        split.
        -   apply abs_pos.
        -   exact x_neq2.
    }
    pose proof (div_pos x_pos) as x'_pos.
    pose proof (half_pos ε_pos) as ε2_pos.
    pose proof (lt_mult ε2_pos M'_pos) as εM_pos.
    pose proof (lt_mult ε2_pos x'_pos) as εa_pos.
    specialize (x_lim _ (lt_mult (div_pos M_pos') εM_pos)) as [N1 x_lim].
    specialize (y_lim _ (lt_mult (div_pos M_pos') εa_pos)) as [N2 y_lim].
    exists (max N1 N2).
    intros n n_gt.
    specialize (x_lim _ (trans (lmax _ _) n_gt)).
    specialize (y_lim _ (trans (rmax _ _) n_gt)).
    apply lt_rmult_pos with (max M 1) in x_lim.
    2: exact M_pos.
    rewrite mult_assoc in x_lim.
    rewrite mult_rlinv in x_lim by exact M_neq.
    apply lt_rmult_pos with (|x|) in y_lim.
    2: exact x_pos.
    rewrite mult_assoc in y_lim.
    rewrite mult_rlinv in y_lim by exact x_neq2.
    specialize (M_bound n).
    apply (trans2 (lmax M 1)) in M_bound.
    apply le_lmult_pos with (|x - xf n|) in M_bound.
    2: apply abs_pos.
    apply (le_lt_trans M_bound) in x_lim.
    rewrite <- lt_mult_llmove_pos in x_lim by exact M_pos'.
    rewrite <- lt_mult_llmove_pos in y_lim by exact M_pos'.
    assert (∀ u v, |f u v| ≤ max M' 1 * (|u| * |v|)) as f_bound'.
    {
        intros u v.
        apply (trans (f_bound _ _)).
        apply le_rmult_pos.
        1: apply le_mult; apply abs_pos.
        apply lmax.
    }
    apply (le_lt_trans (f_bound' _ _)) in x_lim.
    rewrite (mult_comm _ (|x|)) in y_lim.
    apply (le_lt_trans (f_bound' _ _)) in y_lim.
    rewrite bilinear_rdist in x_lim by exact f_bil.
    rewrite bilinear_ldist in y_lim by exact f_bil.
    pose proof (lt_lrplus x_lim y_lim) as eq.
    rewrite plus_half in eq.
    apply (le_lt_trans (abs_tri _ _)) in eq.
    rewrite (bilinear_lneg f), (bilinear_rneg f) in eq by exact f_bil.
    rewrite plus_comm in eq.
    rewrite <- plus_assoc in eq.
    rewrite plus_llinv in eq.
    exact eq.
Qed.

(* begin hide *)
End NormMetric.
(* end hide *)
Global Instance real_scalar_mult : ScalarMult real real := {
    scalar_mult a b := a * b
}.

Global Program Instance real_scalar_comp : ScalarComp real real.
Next Obligation.
    apply mult_assoc.
Qed.
Global Program Instance real_scalar_id : ScalarId real real.
Next Obligation.
    apply mult_lid.
Qed.
Global Program Instance real_scalar_ldist : ScalarLdist real real.
Next Obligation.
    apply ldist.
Qed.
Global Program Instance real_scalar_rdist : ScalarRdist real real.
Next Obligation.
    apply rdist.
Qed.
Global Program Instance real_scalar_lmult : ScalarLMult real real.
Next Obligation.
    unfold scalar_mult; cbn.
    rewrite mult_assoc.
    reflexivity.
Qed.
Global Program Instance real_scalar_rmult : ScalarRMult real real.
Next Obligation.
    unfold scalar_mult; cbn.
    do 2 rewrite mult_assoc.
    rewrite (mult_comm u a).
    reflexivity.
Qed.
Global Program Instance real_abs_scalar : AbsScalar real.
Next Obligation.
    unfold scalar_mult; cbn.
    apply abs_mult.
Qed.
