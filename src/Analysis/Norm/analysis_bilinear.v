Require Import init.

Require Export analysis_norm.
Require Export linear_sum.
Require Import order_minmax.

Section AnalysisBilinear.

Context {V1 V2 V3}
    `{NormedSpaceClass V1, NormedSpaceClass V2, NormedSpaceClass V3}.
Existing Instance abs_metric.

Local Instance ab_plus : Plus (V1 * V2) := {
    plus a b := (fst a + fst b, snd a + snd b)
}.
Local Instance ab_zero : Zero (V1 * V2) := {
    zero := (0, 0)
}.
Local Instance ab_neg : Neg (V1 * V2) := {
    neg a := (-fst a, -snd a)
}.
Local Instance ab_scalar : ScalarMult real (V1 * V2) := {
    scalar_mult a v := (a · fst v, a · snd v)
}.
Local Instance ab_abs : AbsoluteValue (V1 * V2) := {
    abs a := |fst a| + |snd a|
}.
Local Instance ab_plus_assoc : PlusAssoc (V1 * V2).
Proof.
    split.
    intros a b c.
    unfold plus; cbn.
    do 2 rewrite plus_assoc.
    reflexivity.
Qed.
Local Instance ab_plus_comm : PlusComm (V1 * V2).
Proof.
    split.
    intros a b.
    unfold plus; cbn.
    rewrite (plus_comm (fst a)).
    rewrite (plus_comm (snd a)).
    reflexivity.
Qed.
Local Instance ab_plus_lid : PlusLid (V1 * V2).
Proof.
    split.
    intros a.
    unfold plus, zero; cbn.
    do 2 rewrite plus_lid.
    destruct a; reflexivity.
Qed.
Local Instance ab_plus_linv : PlusLinv (V1 * V2).
Proof.
    split.
    intros a.
    unfold neg, plus, zero; cbn.
    do 2 rewrite plus_linv.
    reflexivity.
Qed.
Local Instance ab_scalar_comp : ScalarComp real (V1 * V2).
Proof.
    split.
    intros a b v.
    unfold scalar_mult; cbn.
    do 2 rewrite scalar_comp.
    reflexivity.
Qed.
Local Instance ab_scalar_id : ScalarId real (V1 * V2).
Proof.
    split.
    intros v.
    unfold scalar_mult; cbn.
    do 2 rewrite scalar_id.
    destruct v; reflexivity.
Qed.
Local Instance ab_scalar_ldist : ScalarLdist real (V1 * V2).
Proof.
    split.
    intros a u v.
    unfold scalar_mult, plus at 2; cbn.
    do 2 rewrite scalar_ldist.
    reflexivity.
Qed.
Local Instance ab_scalar_rdist : ScalarRdist real (V1 * V2).
Proof.
    split.
    intros a b v.
    unfold scalar_mult, plus at 2; cbn.
    do 2 rewrite scalar_rdist.
    reflexivity.
Qed.
Local Instance ab_abs_definite : AbsDefinite (V1 * V2).
Proof.
    split.
    intros [x1 x2].
    split; intros eq.
    -   unfold abs in eq; cbn in eq.
        classic_case (0 = x1) as [x_z|x_nz].
        +   subst x1.
            rewrite <- abs_zero, plus_lid in eq.
            rewrite abs_def in eq.
            subst x2.
            reflexivity.
        +   apply abs_pos2 in x_nz.
            pose proof (abs_pos x2) as x2_pos.
            apply (le_lplus (|x1|)) in x2_pos.
            rewrite plus_rid in x2_pos.
            pose proof (lt_le_trans x_nz x2_pos) as ltq.
            rewrite <- eq in ltq.
            contradiction (irrefl _ ltq).
    -   inversion eq.
        unfold abs; cbn.
        do 2 rewrite <- abs_zero.
        rewrite plus_lid.
        reflexivity.
Qed.
Local Instance ab_abs_pos : AbsPositive (V1 * V2).
Proof.
    split.
    intros [x1 x2].
    unfold abs; cbn.
    apply le_pos_plus; apply abs_pos.
Qed.
Local Instance ab_abs_scalar : AbsScalar (V1 * V2).
Proof.
    split.
    intros a [x1 x2].
    unfold abs at 1 3; cbn.
    unfold scalar_mult; cbn.
    rewrite ldist.
    do 2 rewrite abs_scalar.
    reflexivity.
Qed.
Local Instance ab_abs_tri : AbsTriangle (V1 * V2).
Proof.
    split.
    intros [a1 a2] [b1 b2].
    unfold plus at 1, abs; cbn.
    pose proof (abs_tri a1 b1) as leq1.
    pose proof (abs_tri a2 b2) as leq2.
    rewrite plus_4.
    exact (le_lrplus leq1 leq2).
Qed.

(** This is using (V1 * V2) → V3 instead of V1 → V2 → V3 so that we can say
things like "This bilinear function is continuous" and Coq will automatically
know what we are talking about.
*)
Record bilinear_map := make_bilinear_map {
    bilinear_map_f :> (V1 * V2) → V3;
    bilinear_map_lscalar : ∀ a u v,
        bilinear_map_f (a · u, v) = a · bilinear_map_f (u, v);
    bilinear_map_rscalar : ∀ a u v,
        bilinear_map_f (u, a · v) = a · bilinear_map_f (u, v);
    bilinear_map_lplus : ∀ u v w,
        bilinear_map_f (u + v, w) =
        bilinear_map_f (u, w) + bilinear_map_f (v, w);
    bilinear_map_rplus : ∀ u v w,
        bilinear_map_f (u, v + w) =
        bilinear_map_f (u, v) + bilinear_map_f (u, w);
}.

Theorem bilinear_map_eq : ∀ f g : bilinear_map, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_lscalar f_rscalar f_lplus f_rplus]
           [g g_lscalar g_rscalar g_lplus g_rplus]; cbn.
    intros eq.
    assert (f = g) as eq'.
    {
        apply functional_ext.
        exact eq.
    }
    subst g.
    rewrite (proof_irrelevance _ g_lscalar).
    rewrite (proof_irrelevance _ g_rscalar).
    rewrite (proof_irrelevance _ g_lplus).
    rewrite (proof_irrelevance _ g_rplus).
    reflexivity.
Qed.

Theorem bilinear_map_lanni : ∀ f : bilinear_map, ∀ v, f(0, v) = 0.
Proof.
    intros f v.
    rewrite <- (scalar_ranni 0).
    rewrite bilinear_map_lscalar.
    apply scalar_lanni.
Qed.

Theorem bilinear_map_ranni : ∀ f : bilinear_map, ∀ v, f(v, 0) = 0.
Proof.
    intros f v.
    rewrite <- (scalar_ranni 0).
    rewrite bilinear_map_rscalar.
    apply scalar_lanni.
Qed.

Theorem bilinear_map_lneg : ∀ f : bilinear_map, ∀ u v, f(-u, v) = -f(u, v).
Proof.
    intros f u v.
    rewrite <- scalar_neg_one.
    rewrite bilinear_map_lscalar.
    apply scalar_neg_one.
Qed.

Theorem bilinear_map_rneg : ∀ f : bilinear_map, ∀ u v, f(u, -v) = -f(u, v).
Proof.
    intros f u v.
    rewrite <- scalar_neg_one.
    rewrite bilinear_map_rscalar.
    apply scalar_neg_one.
Qed.

Definition bounded_bilinear_map (f : bilinear_map)
    := ∃ M : real, ∀ x y, |f(x, y)| ≤ M*|x|*|y|.

Theorem bilinear_bounded_continuous : ∀ f : bilinear_map,
    bounded_bilinear_map f → continuous f.
Proof.
    intros f [M' f_bound'].
    intros a.
    rewrite metric_continuous_at.
    intros ε ε_pos.
    cbn.
    classic_case (∀ x : V1, 0 = x) as [all_z|nz1].
    {
        exists 1.
        split; [>exact one_pos|].
        intros x x_lt.
        destruct a as [a1 a2], x as [x1 x2].
        rewrite <- (all_z a1).
        rewrite <- (all_z x1).
        do 2 rewrite bilinear_map_lanni.
        rewrite neg_zero, plus_lid.
        rewrite <- abs_zero.
        exact ε_pos.
    }
    classic_case (∀ x : V2, 0 = x) as [all_z|nz2].
    {
        exists 1.
        split; [>exact one_pos|].
        intros x x_lt.
        destruct a as [a1 a2], x as [x1 x2].
        rewrite <- (all_z a2).
        rewrite <- (all_z x2).
        do 2 rewrite bilinear_map_ranni.
        rewrite neg_zero, plus_lid.
        rewrite <- abs_zero.
        exact ε_pos.
    }
    pose (M := M' + 1).
    assert (∀ x y, |f(x, y)| ≤ M * |x| * |y|) as f_bound.
    {
        intros x y.
        apply (trans (f_bound' x y)).
        do 2 rewrite <- mult_assoc.
        apply le_rmult_pos.
        -   apply le_mult; apply abs_pos.
        -   apply lt_plus_one.
    }
    assert (0 < M) as M_pos.
    {
        apply (lt_le_trans one_pos).
        unfold M.
        rewrite <- le_plus_0_a_b_ab.
        rewrite not_all in nz1.
        rewrite not_all in nz2.
        destruct nz1 as [u u_nz].
        destruct nz2 as [v v_nz].
        specialize (f_bound' u v).
        rewrite <- mult_assoc in f_bound'.
        apply (trans (abs_pos _)) in f_bound'.
        rewrite <- (mult_lanni (|u|*|v|)) in f_bound'.
        apply le_mult_rcancel_pos in f_bound'.
        -   exact f_bound'.
        -   apply lt_mult.
            all: apply abs_pos2.
            all: assumption.
    }
    clearbody M.
    clear M' f_bound' nz1 nz2.
    pose (δ := min 1 (ε/(M * (|a| + 1)))).
    assert (0 < M * (|a| + 1)) as pos.
    {
        apply lt_mult.
        -   exact M_pos.
        -   apply (lt_le_trans one_pos).
            rewrite <- le_plus_0_a_b_ab.
            apply abs_pos.
    }
    exists δ.
    split.
    {
        unfold δ, min; case_if.
        -   exact one_pos.
        -   apply lt_mult.
            +   exact ε_pos.
            +   apply div_pos.
                exact pos.
    }
    intros x ax_lt.
    destruct a as [a1 a2], x as [x1 x2].
    rewrite <- (plus_rlinv (f(a1, a2)) (f(x1, a2))).
    rewrite <- bilinear_map_lneg, <- bilinear_map_lplus.
    rewrite <- plus_assoc.
    rewrite <- bilinear_map_rneg, <- bilinear_map_rplus.
    apply (le_lt_trans (abs_tri _ _)).
    apply (le_lt_trans (le_lrplus (f_bound _ _) (f_bound _ _))).
    do 2 rewrite <- mult_assoc.
    rewrite <- ldist.
    rewrite (mult_comm _ (|a2|)).
    assert (|a2| ≤ |(a1, a2)| + 1) as leq1.
    {
        unfold abs at 2; cbn.
        rewrite plus_comm.
        rewrite plus_assoc.
        rewrite <- le_plus_0_a_b_ab.
        apply le_pos_plus.
        -   apply one_pos.
        -   apply abs_pos.
    }
    assert (|x1| ≤ |(a1, a2)| + 1) as leq2.
    {
        apply (lt_le_trans2 (lmin _ _)) in ax_lt.
        pose proof (abs_reverse_tri (x1, x2) (a1, a2)) as leq.
        apply (trans (abs_le_pos _)) in leq.
        rewrite abs_minus in leq.
        pose proof (le_lt_trans leq ax_lt) as leq2.
        rewrite <- lt_plus_rrmove in leq2.
        rewrite plus_comm.
        apply (le_lt_trans2 leq2).
        unfold abs at 2; cbn.
        rewrite <- le_plus_0_a_b_ba.
        apply abs_pos.
    }
    apply (le_rmult_pos (|a1 - x1|)) in leq1; [>|apply abs_pos].
    apply (le_rmult_pos (|a2 - x2|)) in leq2; [>|apply abs_pos].
    pose proof (le_lrplus leq1 leq2) as leq.
    apply (le_lmult_pos M) in leq; [>|apply M_pos].
    apply (le_lt_trans leq); clear leq1 leq2 leq.
    rewrite <- ldist.
    rewrite mult_assoc.
    apply (lt_le_trans2 (rmin _ _)) in ax_lt.
    apply (lt_rmult_pos (M * (|(a1, a2)| + 1))) in ax_lt; [>|exact pos].
    rewrite mult_rlinv in ax_lt by apply pos.
    rewrite mult_comm in ax_lt.
    exact ax_lt.
Qed.

Theorem bilinear_continuous_bounded : ∀ f : bilinear_map,
    continuous_at f 0 → bounded_bilinear_map f.
Proof.
    intros f f_cont.
    rewrite metric_continuous_at in f_cont.
    specialize (f_cont 1 one_pos) as [δ [δ_pos f_cont]].
    cbn in f_cont.
    exists (4*4/(δ*δ)).
    intros x1 x2.
    classic_case (0 = x1) as [x1_z|x1_nz].
    {
        subst x1.
        rewrite bilinear_map_lanni.
        do 2 rewrite <- abs_zero.
        rewrite mult_ranni, mult_lanni.
        apply refl.
    }
    classic_case (0 = x2) as [x2_z|x2_nz].
    {
        subst x2.
        rewrite bilinear_map_ranni.
        do 2 rewrite <- abs_zero.
        rewrite mult_ranni.
        apply refl.
    }
    pose (u1 := (δ/(4*|x1|))·x1).
    pose (u2 := (δ/(4*|x2|))·x2).
    specialize (f_cont (u1, u2)).
    prove_parts f_cont.
    {
        rewrite plus_lid, abs_neg.
        unfold abs, u1, u2; cbn.
        do 2 rewrite abs_scalar.
        do 2 rewrite abs_mult.
        rewrite <- abs_div; [>rewrite <- abs_div|].
        2, 3: apply mult_nz.
        2, 4: apply four_nz.
        2, 3: rewrite abs_nz.
        2, 3: assumption.
        do 2 rewrite abs_mult.
        do 2 rewrite abs_abs.
        rewrite (abs_pos_eq 4) by apply four_pos.
        rewrite div_mult; [>rewrite div_mult| |].
        2, 4: apply four_nz.
        2, 3: rewrite abs_nz.
        2, 3: assumption.
        do 4 rewrite <- mult_assoc.
        do 2 rewrite mult_linv by (apply abs_nz; assumption).
        rewrite mult_rid.
        rewrite <- two_times_two.
        rewrite div_mult by exact two_nz.
        rewrite mult_assoc.
        rewrite plus_half.
        rewrite <- (plus_half δ) at 2.
        rewrite abs_pos_eq by apply δ_pos.
        rewrite <- lt_plus_0_a_b_ab.
        apply half_pos.
        exact δ_pos.
    }
    rewrite bilinear_map_lanni in f_cont.
    rewrite plus_lid, abs_neg in f_cont.
    assert (x1 = (4 * |x1| / δ) · u1) as x1_eq.
    {
        unfold u1.
        rewrite scalar_comp.
        rewrite mult_assoc.
        rewrite mult_rlinv by apply δ_pos.
        rewrite mult_rinv.
        -   rewrite scalar_id; reflexivity.
        -   apply mult_nz.
            +   apply four_nz.
            +   rewrite abs_nz.
                exact x1_nz.
    }
    assert (x2 = (4 * |x2| / δ) · u2) as x2_eq.
    {
        unfold u2.
        rewrite scalar_comp.
        rewrite mult_assoc.
        rewrite mult_rlinv by apply δ_pos.
        rewrite mult_rinv.
        -   rewrite scalar_id; reflexivity.
        -   apply mult_nz.
            +   apply four_nz.
            +   rewrite abs_nz.
                exact x2_nz.
    }
    rewrite x1_eq at 1.
    rewrite x2_eq at 1.
    rewrite bilinear_map_lscalar, bilinear_map_rscalar.
    do 2 rewrite abs_scalar.
    destruct f_cont as [f_cont neq]; clear neq.
    apply (le_lmult_pos (4 * 4 / (δ * δ) * |x1| * |x2|)) in f_cont.
    2: {
        apply le_mult; [>|apply abs_pos].
        apply le_mult; [>|apply abs_pos].
        apply le_mult.
        -   apply le_mult; apply four_pos.
        -   apply div_pos.
            apply lt_mult; exact δ_pos.
    }
    rewrite mult_rid in f_cont.
    apply (trans2 f_cont).
    assert (∀ a b : real, a = b → a ≤ b) as stupid.
    {
        intros a b eq; subst; apply refl.
    }
    apply stupid; clear stupid.
    rewrite mult_assoc.
    apply rmult.
    do 4 rewrite abs_mult.
    do 2 rewrite abs_abs.
    rewrite abs_pos_eq by apply four_pos.
    do 6 rewrite <- mult_assoc.
    apply lmult.
    rewrite <- abs_div by apply δ_pos.
    rewrite abs_pos_eq by apply δ_pos.
    rewrite (mult_comm (|x2|)).
    do 5 rewrite mult_assoc.
    apply rmult.
    rewrite (mult_comm _ (|x1|)).
    do 2 rewrite <- mult_assoc.
    apply lmult.
    rewrite div_mult by apply δ_pos.
    do 2 rewrite mult_assoc.
    apply rmult.
    apply mult_comm.
Qed.

End AnalysisBilinear.
