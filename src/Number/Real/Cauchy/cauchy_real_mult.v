Require Import init.

Require Export cauchy_real_plus.

Lemma cauchy_bounded : ∀ a : real_base, ∃ M, ∀ n, |r_seq a n| < M.
Proof.
    intros [a a_cauchy]; cbn.
    specialize (a_cauchy 1 one_pos) as [N a_cauchy].
    pose (S := image_under (λ n, |a n|) (initial_segment N)).
    assert (has_upper_bound le S) as [M M_max].
    {
        nat_destruct N.
        {
            exists 0.
            intros x [n [n_lt n_eq]].
            contradiction (nat_neg2 n_lt).
        }
        assert (simple_finite (set_type S)) as S_fin.
        {
            apply (simple_finite_trans _ _ (simple_finite_nat (nat_suc N))).
            exists (λ x : set_type S, [ex_val [|x] | land (ex_proof [|x])]).
            split.
            intros x y.
            rewrite set_type_eq2.
            rewrite_ex_val m [m_lt x_eq].
            rewrite_ex_val n [n_lt y_eq].
            intros eq; subst n.
            rewrite <- y_eq in x_eq.
            rewrite set_type_eq in x_eq.
            exact x_eq.
        }
        pose proof (simple_finite_max S_fin) as x_ex.
        prove_parts x_ex.
        {
            exists (|a 0|).
            exists 0.
            split; [>|reflexivity].
            apply nat_pos2.
        }
        destruct x_ex as [[x Sx] x_greatest].
        exists x.
        intros m Sm.
        exact (x_greatest [m|Sm]).
    }
    exists (max (M + 1) (|a N| + 1)).
    intros n.
    classic_case (n < N) as [ltq|leq].
    -   apply (lt_le_trans2 (lmax _ _)).
        specialize (M_max (|a n|)).
        prove_parts M_max; [>exists n; split; [>exact ltq|reflexivity]|].
        apply (le_lt_trans M_max).
        apply lt_plus_one.
    -   apply (lt_le_trans2 (rmax _ _)).
        rewrite nlt_le in leq.
        specialize (a_cauchy n N leq (refl _)).
        apply (le_lt_trans (abs_reverse_tri2 _ _)) in a_cauchy.
        rewrite lt_plus_rlmove.
        rewrite plus_comm.
        exact a_cauchy.
Qed.

Lemma cauchy_mult : ∀ a b : real_base, cauchy_seq (λ n, r_seq a n * r_seq b n).
Proof.
    intros a b ε ε_pos.
    pose proof (cauchy_bounded a) as [M1 M1_gt].
    pose proof (cauchy_bounded b) as [M2 M2_gt].
    destruct a as [a a_cauchy], b as [b b_cauchy]; cbn in *.
    assert (0 < M1) as M1_pos by (apply (le_lt_trans2 (M1_gt 0));apply abs_pos).
    assert (0 < M2) as M2_pos by (apply (le_lt_trans2 (M2_gt 0));apply abs_pos).
    pose proof (half_pos ε_pos) as ε2_pos.
    specialize (a_cauchy _ (lt_mult (div_pos M2_pos) ε2_pos)) as [N1 a_cauchy].
    specialize (b_cauchy _ (lt_mult (div_pos M1_pos) ε2_pos)) as [N2 b_cauchy].
    exists (max N1 N2).
    intros i j i_ge j_ge.
    specialize (a_cauchy i j (trans (lmax _ _) i_ge) (trans (lmax _ _) j_ge)).
    specialize (b_cauchy i j (trans (rmax _ _) i_ge) (trans (rmax _ _) j_ge)).
    rewrite <- lt_mult_llmove_pos in a_cauchy by exact M2_pos.
    rewrite <- lt_mult_llmove_pos in b_cauchy by exact M1_pos.
    pose proof (lt_lrplus a_cauchy b_cauchy) as ltq.
    rewrite plus_half in ltq.
    rewrite <- (plus_rlinv (a i * b i) (a i * b j)).
    rewrite <- mult_rneg, <- ldist.
    rewrite <- plus_assoc.
    rewrite <- mult_lneg, <- rdist.
    rewrite (mult_comm _ (b j)).
    apply (le_lt_trans (abs_tri _ _)).
    rewrite plus_comm.
    apply (le_lt_trans2 ltq).
    do 2 rewrite abs_mult.
    apply le_lrplus.
    -   apply le_rmult_pos; [>apply abs_pos|].
        apply M2_gt.
    -   apply le_rmult_pos; [>apply abs_pos|].
        apply M1_gt.
Qed.

Notation "a ⊗ b" := (make_real _ (cauchy_mult a b)) : real_scope.

Lemma real_mult_wd : ∀ a b c d, a ~ b → c ~ d → a ⊗ c ~ b ⊗ d.
    intros [a a_cauchy] b c [d d_cauchy] ab cd ε ε_pos.
    pose proof (cauchy_bounded b) as [M1 M1_gt].
    pose proof (cauchy_bounded c) as [M2 M2_gt].
    destruct b as [b b_cauchy], c as [c c_cauchy]; cbn in *.
    assert (0 < M1) as M1_pos by (apply (le_lt_trans2 (M1_gt 0));apply abs_pos).
    assert (0 < M2) as M2_pos by (apply (le_lt_trans2 (M2_gt 0));apply abs_pos).
    pose proof (half_pos ε_pos) as ε2_pos.
    specialize (ab _ (lt_mult (div_pos M2_pos) ε2_pos)) as [N1 ab].
    specialize (cd _ (lt_mult (div_pos M1_pos) ε2_pos)) as [N2 cd].
    exists (max N1 N2).
    intros i i_ge.
    specialize (ab i (trans (lmax _ _) i_ge)).
    specialize (cd i (trans (rmax _ _) i_ge)).
    rewrite <- lt_mult_llmove_pos in ab by exact M2_pos.
    rewrite <- lt_mult_llmove_pos in cd by exact M1_pos.
    pose proof (lt_lrplus ab cd) as ltq.
    rewrite plus_half in ltq.
    rewrite <- (plus_rlinv (a i * c i) (b i * c i)).
    rewrite <- mult_lneg, <- rdist.
    rewrite <- plus_assoc.
    rewrite <- mult_rneg, <- ldist.
    rewrite (mult_comm _ (c i)).
    apply (le_lt_trans (abs_tri _ _)).
    apply (le_lt_trans2 ltq).
    do 2 rewrite abs_mult.
    apply le_lrplus.
    -   apply le_rmult_pos; [>apply abs_pos|].
        apply M2_gt.
    -   apply le_rmult_pos; [>apply abs_pos|].
        apply M1_gt.
Qed.

Global Instance real_mult : Mult real := {
    mult := binary_op (binary_self_wd real_mult_wd)
}.

Global Instance real_one : One real := {
    one := rat_to_real 1
}.

Definition real_div_base (a : real_base) :=
    If (0 = to_equiv real_equiv a)
    then λ _, 0
    else λ n, /(r_seq a n).

Lemma cauchy_nz : ∀ a : real_base, 0 ≠ to_equiv real_equiv a →
    ∃ ε N, 0 < ε ∧ (∀ i, N ≤ i → ε ≤ |r_seq a i|).
Proof.
    intros [a a_cauchy] a_neq; cbn in *.
    rewrite neq_sym in a_neq.
    unfold zero in a_neq; cbn in a_neq.
    unfold rat_to_real in a_neq; equiv_simpl in a_neq.
    rewrite not_all in a_neq.
    destruct a_neq as [ε a_neq].
    rewrite not_impl in a_neq.
    rewrite not_ex in a_neq.
    destruct a_neq as [ε_pos a_neq].
    specialize (a_cauchy _ (half_pos ε_pos)) as [N a_cauchy].
    specialize (a_neq N).
    rewrite not_all in a_neq.
    destruct a_neq as [n a_neq].
    rewrite not_impl in a_neq.
    destruct a_neq as [n_ge an_ge].
    rewrite nlt_le in an_ge.
    rewrite neg_zero, plus_rid in an_ge.
    exists (ε/2), N.
    split; [>exact (half_pos ε_pos)|].
    intros i i_ge.
    specialize (a_cauchy n i n_ge i_ge).
    apply (le_lt_trans (abs_reverse_tri2 _ _)) in a_cauchy.
    rewrite <- lt_plus_rrmove in a_cauchy.
    pose proof (le_lt_trans an_ge a_cauchy) as ltq.
    rewrite <- (plus_half ε) in ltq at 1.
    apply lt_plus_lcancel in ltq.
    apply ltq.
Qed.

Lemma cauchy_div : ∀ a : real_base, cauchy_seq (real_div_base a).
    intros [a a_cauchy].
    unfold real_div_base; cbn.
    case_if [a_eq|a_neq]; [>apply rat_to_real_cauchy|].
    apply cauchy_nz in a_neq as [ε' [N1 [ε'_pos nz]]].
    cbn in nz.
    intros ε ε_pos.
    pose proof (div_pos ε'_pos) as ε''_pos.
    specialize (a_cauchy _ (lt_mult ε_pos (lt_mult ε'_pos ε'_pos)))
        as [N2 a_cauchy].
    exists (max N1 N2).
    intros i j i_ge j_ge.
    pose proof (nz i (trans (lmax N1 N2) i_ge)) as i_gt.
    pose proof (nz j (trans (lmax N1 N2) j_ge)) as j_gt.
    clear nz.
    assert (0 ≠ a i) as ai_nz.
    {
        intros contr.
        rewrite <- contr in i_gt.
        rewrite <- abs_zero in i_gt.
        destruct (lt_le_trans ε'_pos i_gt); contradiction.
    }
    assert (0 ≠ a j) as aj_nz.
    {
        intros contr.
        rewrite <- contr in j_gt.
        rewrite <- abs_zero in j_gt.
        destruct (lt_le_trans ε'_pos j_gt); contradiction.
    }
    rewrite <- (mult_lrinv (/(a i)) (a j)) by exact aj_nz.
    rewrite <- (mult_lrinv (/(a j)) (a i)) at 2 by exact ai_nz.
    rewrite (mult_comm (/(a j))).
    rewrite <- mult_lneg, <- rdist.
    do 2 rewrite abs_mult.
    specialize (a_cauchy j i (trans (rmax _ _) j_ge) (trans (rmax _ _) i_ge)).
    rewrite mult_assoc.
    rewrite <- abs_div by exact ai_nz.
    rewrite <- abs_div by exact aj_nz.
    rewrite <- lt_mult_rrmove_pos by (exact (abs_pos2 aj_nz)).
    rewrite <- lt_mult_rrmove_pos by (exact (abs_pos2 ai_nz)).
    apply (lt_le_trans a_cauchy).
    rewrite <- mult_assoc.
    apply le_lmult_pos; [>apply ε_pos|].
    apply le_lrmult_pos.
    -   apply ε'_pos.
    -   apply ε'_pos.
    -   apply j_gt.
    -   apply i_gt.
Qed.

Notation "⊘ a" := (make_real _ (cauchy_div a)) : real_scope.

Lemma real_div_wd : ∀ a b, a ~ b → ⊘a ~ ⊘b.
Proof.
    intros a b ab ε ε_pos; cbn.
    assert (to_equiv real_equiv a = to_equiv real_equiv b) as ab'
        by (equiv_simpl; exact ab).
    unfold real_div_base.
    case_if [a_z|a_nz]; case_if [b_z|b_nz].
    {
        exists 0.
        intros i i_ge.
        rewrite neg_zero, plus_rid, <- abs_zero.
        exact ε_pos.
    }
    {
        rewrite <- ab' in b_nz.
        contradiction.
    }
    {
        rewrite ab' in a_nz.
        contradiction.
    }
    clear ab'.
    apply cauchy_nz in a_nz as [ε1 [N1 [ε1_pos a_nz]]].
    apply cauchy_nz in b_nz as [ε2 [N2 [ε2_pos b_nz]]].
    destruct a as [a a_cauchy], b as [b b_cauchy]; cbn in *.
    specialize (ab _ (lt_mult ε_pos (lt_mult ε1_pos ε2_pos))) as [N ab].
    exists (max N (max N1 N2)).
    intros i i_ge.
    specialize (a_nz i (trans (lmax _ _) (trans (rmax _ _) i_ge))).
    specialize (b_nz i (trans (rmax _ _) (trans (rmax _ _) i_ge))).
    specialize (ab i (trans (lmax _ _) i_ge)).
    assert (0 ≠ a i) as ai_nz.
    {
        intros contr.
        rewrite <- contr in a_nz.
        rewrite <- abs_zero in a_nz.
        destruct (lt_le_trans ε1_pos a_nz); contradiction.
    }
    assert (0 ≠ b i) as bi_nz.
    {
        intros contr.
        rewrite <- contr in b_nz.
        rewrite <- abs_zero in b_nz.
        destruct (lt_le_trans ε2_pos b_nz); contradiction.
    }
    rewrite <- (mult_lrinv (/(a i)) (b i)) by exact bi_nz.
    rewrite <- (mult_lrinv (/(b i)) (a i)) at 2 by exact ai_nz.
    rewrite (mult_comm (/(a i))).
    rewrite <- mult_lneg, <- rdist.
    do 2 rewrite abs_mult.
    rewrite mult_assoc.
    rewrite <- abs_div by exact bi_nz.
    rewrite <- abs_div by exact ai_nz.
    rewrite <- lt_mult_rrmove_pos by (exact (abs_pos2 ai_nz)).
    rewrite <- lt_mult_rrmove_pos by (exact (abs_pos2 bi_nz)).
    rewrite abs_minus.
    apply (lt_le_trans ab).
    rewrite <- mult_assoc.
    apply le_lmult_pos; [>apply ε_pos|].
    apply le_lrmult_pos.
    -   apply ε1_pos.
    -   apply ε2_pos.
    -   apply a_nz.
    -   apply b_nz.
Qed.

Global Instance real_div : Div real := {
    div := unary_op (unary_self_wd real_div_wd)
}.

Global Instance real_ldist : Ldist real.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold mult, plus; equiv_simpl.
    intros ε ε_pos.
    exists 0.
    intros i i_ge.
    rewrite ldist.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Global Instance real_mult_comm : MultComm real.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold mult; equiv_simpl.
    intros ε ε_pos.
    exists 0.
    intros i i_ge.
    rewrite mult_comm.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Global Instance real_mult_assoc : MultAssoc real.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold mult; equiv_simpl.
    intros ε ε_pos.
    exists 0.
    intros i i_ge.
    rewrite mult_assoc.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Global Instance real_mult_lid : MultLid real.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold mult, one; equiv_simpl.
    intros ε ε_pos.
    exists 0.
    intros i i_ge.
    rewrite mult_lid.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Global Instance real_mult_linv : MultLinv real.
Proof.
    split.
    intros a a_nz.
    equiv_get_value a.
    unfold mult, div, one; cbn.
    unfold rat_to_real; equiv_simpl.
    intros ε ε_pos.
    unfold real_div_base.
    case_if [a_z|a_nz']; [>contradiction|].
    apply cauchy_nz in a_nz' as [ε' [N [ε'_pos a_nz']]].
    exists N.
    intros i i_ge.
    specialize (a_nz' i i_ge).
    pose proof (lt_le_trans ε'_pos a_nz') as ai_pos.
    destruct ai_pos as [ai_pos ai_nz].
    rewrite abs_nz in ai_nz.
    rewrite mult_linv by exact ai_nz.
    rewrite plus_rinv.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

#[refine]
Global Instance real_not_trivial : NotTrivial real := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Proof.
    unfold zero, one; cbn.
    unfold rat_to_real; equiv_simpl.
    intros contr.
    specialize (contr 1 one_pos) as [N contr].
    specialize (contr N (refl _)).
    rewrite abs_minus, neg_zero, plus_rid in contr.
    rewrite abs_one in contr.
    destruct contr; contradiction.
Qed.
