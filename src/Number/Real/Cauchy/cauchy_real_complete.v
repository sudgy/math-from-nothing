Require Import init.

Require Export cauchy_real_order.
Require Import nat.

Open Scope nat_scope.

Lemma real_lt : ∀ a b, to_equiv_type real_equiv a < to_equiv_type real_equiv b →
    ∃ ε N, 0 < ε ∧ ∀ i, N ≤ i → r_seq a i + ε < r_seq b i.
Proof.
    intros a b ltq.
    destruct ltq as [leq neq].
    unfold le in leq; equiv_simpl in leq.
    unfold neg, plus in leq; equiv_simpl in leq.
    pose proof (cauchy_nz (b ⊕ ⊖ a)) as nz.
    prove_parts nz.
    {
        intros contr.
        apply neq.
        rewrite <- plus_0_anb_b_a.
        unfold plus, neg; equiv_simpl.
        exact contr.
    }
    destruct nz as [ε [N1 [ε_pos nz]]].
    destruct leq as [eq|leq].
    {
        exfalso; apply neq.
        rewrite <- plus_0_anb_b_a.
        unfold plus, neg; equiv_simpl.
        exact eq.
    }
    destruct leq as [N2 leq].
    exists (ε/2), (max N1 N2).
    split; [>apply half_pos; exact ε_pos|].
    intros i i_ge.
    cbn in *.
    specialize (nz i (trans (lmax _ _) i_ge)).
    specialize (leq i (trans (rmax _ _) i_ge)).
    rewrite abs_pos_eq in nz by exact leq.
    rewrite lt_plus_llmove.
    rewrite (plus_comm (-(r_seq a i))).
    apply (lt_le_trans2 nz).
    rewrite <- (plus_half ε) at 2.
    rewrite <- lt_plus_0_a_b_ab.
    apply half_pos.
    exact ε_pos.
Qed.

Global Instance real_sup_complete : SupremumComplete (U := real) le.
Proof.
    split.
    intros S S_ex S_upper.
    pose (S' x := is_upper_bound le S (rat_to_real x)).
    assert (∃ q : rat, S' q) as [u u_upper].
    {
        destruct S_upper as [u u_upper].
        equiv_get_value u.
        pose proof (cauchy_bounded u) as [M M_bound].
        exists M.
        intros x Sx.
        apply (trans (u_upper x Sx)).
        unfold le, rat_to_real; equiv_simpl.
        unfold plus, neg; equiv_simpl.
        right; cbn.
        exists 0.
        intros i i_ge.
        rewrite le_plus_0_anb_b_a.
        specialize (M_bound i).
        apply (le_lt_trans (abs_le_pos _)) in M_bound.
        apply M_bound.
    }
    assert (∃ q : rat, ¬S' q) as [l l_lower].
    {
        destruct S_ex as [l Sl].
        equiv_get_value l.
        pose proof (cauchy_bounded l) as [M M_bound].
        exists (-M - 1).
        intros M_upper.
        specialize (M_upper _ Sl) as leq.
        unfold le, rat_to_real in leq; equiv_simpl in leq.
        unfold plus at 1, neg at 5 in leq; equiv_simpl in leq.
        destruct leq as [eq|leq].
        -   unfold zero in eq; cbn in eq.
            unfold rat_to_real in eq; equiv_simpl in eq.
            specialize (eq 1 one_pos) as [N eq].
            specialize (eq N (refl N)).
            rewrite abs_minus in eq.
            rewrite neg_zero, plus_rid in eq.
            apply (le_lt_trans (abs_le_neg _)) in eq.
            do 2 rewrite neg_plus in eq.
            do 3 rewrite neg_neg in eq.
            rewrite plus_comm, plus_assoc in eq.
            rewrite <- lt_plus_a_0_ab_b in eq.
            specialize (M_bound N).
            apply (le_lt_trans (abs_le_neg _)) in M_bound.
            rewrite lt_plus_ab_0_b_na in eq.
            destruct (trans eq M_bound); contradiction.
        -   cbn in leq.
            destruct leq as [N leq].
            specialize (leq N (refl N)).
            do 2 rewrite <- neg_plus in leq.
            rewrite <- neg_pos in leq.
            specialize (M_bound N).
            apply (le_lt_trans (abs_le_neg _)) in M_bound.
            rewrite <- lt_plus_0_ab_na_b in M_bound.
            rewrite plus_comm, plus_assoc in leq.
            rewrite le_plus_ab_0_a_nb in leq.
            pose proof (lt_le_trans M_bound leq) as ltq.
            rewrite <- neg_pos2 in ltq.
            destruct (trans ltq one_pos); contradiction.
    }
    pose (p := fix build (n : nat) :=
        match n with
        | nat_zero => (l, u)
        | nat_suc n' => let m := (fst (build n') + snd (build n')) / 2 in
            If S' m then (fst (build n'), m)
            else (m, snd (build n'))
        end).
    pose (a n := fst (p n)).
    pose (b n := snd (p n)).
    assert (∀ i, ¬S' (a i)) as a_lower.
    {
        nat_induction i.
        -   unfold zero; cbn.
            exact l_lower.
        -   unfold a; cbn.
            case_if [p_in|p_nin]; cbn.
            +   exact IHi.
            +   exact p_nin.
    }
    assert (∀ i, S' (b i)) as b_upper.
    {
        nat_induction i.
        -   unfold zero; cbn.
            exact u_upper.
        -   unfold b; cbn.
            case_if [p_in|p_nin]; cbn.
            +   exact p_in.
            +   exact IHi.
    }
    pose (d n := b n - a n).
    assert (∀ n, d n = d 0 / 2^n) as d_eq.
    {
        nat_induction n.
        {
            rewrite nat_pow_zero.
            rewrite div_one, mult_rid.
            reflexivity.
        }
        cbn.
        rewrite div_mult; [>|
            apply nat_pow_not_zero; apply two_pos|
            apply two_pos].
        rewrite mult_assoc.
        rewrite <- IHn.
        unfold d; cbn.
        unfold b, a; cbn.
        case_if [p_in|p_nin]; cbn.
        -   rewrite (plus_comm (fst (p n))).
            do 2 rewrite rdist.
            rewrite <- plus_assoc.
            apply lplus.
            rewrite <- plus_rrmove.
            rewrite mult_lneg.
            rewrite <- plus_llmove.
            apply plus_half.
        -   rewrite (plus_comm (fst (p n))).
            do 2 rewrite rdist.
            rewrite neg_plus.
            rewrite plus_assoc.
            rewrite mult_lneg.
            apply rplus.
            rewrite <- plus_rrmove.
            symmetry; apply plus_half.
    }
    assert (∀ n, 0 < d n) as d_pos.
    {
        intros n.
        rewrite d_eq.
        unfold d.
        unfold zero at 2 3; cbn.
        apply lt_mult.
        -   pose proof (upper_bound_leq _ _ _ l_lower u_upper) as ltq.
            unfold rat_to_real in ltq.
            apply real_lt in ltq; cbn in ltq.
            destruct ltq as [ε [N [ε_pos ltq]]].
            specialize (ltq N (refl N)).
            rewrite lt_plus_0_anb_b_a.
            apply (trans2 ltq).
            rewrite <- lt_plus_0_a_b_ba.
            exact ε_pos.
        -   apply div_pos.
            apply nat_pow_pos2.
            exact two_pos.
    }
    assert (cauchy_seq a) as a_cauchy.
    {
        intros ε ε_pos.
        assert (∀ n, |a n - a (nat_suc n)| ≤ d 0 / 2^(nat_suc n)) as a_gap.
        {
            intros n.
            rewrite <- d_eq.
            pose proof (Logic.eq_refl (d (nat_suc n))) as eq.
            unfold d in eq at 1.
            unfold a, b in eq; cbn in eq.
            pose proof (d_pos (nat_suc n)) as ltq.
            unfold d, a, b in ltq; cbn in ltq.
            unfold d, a, b; cbn.
            case_if [S'd|S'd]; cbn in *.
            -   rewrite plus_rinv.
                rewrite <- abs_zero.
                rewrite eq.
                rewrite d_eq.
                apply le_mult.
                +   apply d_pos.
                +   apply div_pos.
                    apply nat_pow_pos2.
                    exact two_pos.
            -   rewrite rdist, neg_plus.
                rewrite plus_assoc.
                rewrite <- (plus_half (fst (p n))) at 1.
                rewrite plus_rrinv.
                rewrite (plus_comm (-(fst (p n) / 2))).
                rewrite <- (plus_half (snd (p n))) at 2.
                rewrite plus_assoc.
                rewrite plus_rrinv.
                rewrite abs_minus.
                rewrite abs_pos_eq; [>apply refl|].
                rewrite plus_comm in ltq.
                rewrite rdist, neg_plus, <- plus_assoc in ltq.
                rewrite <- (plus_half (snd (p n))) in ltq at 2.
                rewrite plus_llinv in ltq.
                rewrite plus_comm in ltq.
                apply ltq.
        }
        pose proof (lt_mult ε_pos (div_pos (d_pos 0))) as ε'_pos.
        pose proof (arch_pow2 _ ε'_pos) as [N N_lt].
        exists N.
        assert (∀ i j, N ≤ i → i ≤ j → |a i - a j| < ε) as wlog.
        {
            intros i j i_ge leq.
            apply nat_le_ex in leq as [c c_eq]; subst.
            rewrite <- lt_mult_lrmove_pos in N_lt by apply d_pos.
            rewrite mult_comm in N_lt.
            apply (trans2 N_lt).
            clear ε ε_pos ε'_pos N_lt.
            revert N i i_ge.
            nat_induction c; intros.
            {
                rewrite plus_rid.
                rewrite plus_rinv, <- abs_zero.
                apply lt_mult.
                -   apply d_pos.
                -   apply div_pos.
                    apply nat_pow_pos2.
                    exact two_pos.
            }
            rewrite <- (plus_rlinv (a i) (a (nat_suc i))).
            rewrite <- plus_assoc.
            apply (le_lt_trans (abs_tri _ _)).
            specialize (a_gap i).
            rewrite <- nat_sucs_le in i_ge.
            specialize (IHc _ _ i_ge).
            pose proof (nat_pow_le (U := rat) 2 _ _ (land lt_1_2) i_ge) as leq.
            apply le_div_pos in leq; [>|apply nat_pow_pos2; exact two_pos].
            apply le_lmult_pos with (d 0) in leq; [>|apply d_pos].
            pose proof (trans a_gap leq) as a_gap'.
            pose proof (le_lt_lrplus a_gap' IHc) as ltq.
            applys_eq ltq.
            rewrite <- ldist.
            cbn.
            rewrite div_mult; [>|apply nat_pow_pos2; exact two_pos|apply two_pos].
            rewrite div_mult; [>|apply nat_pow_pos2; exact two_pos|apply two_pos].
            rewrite plus_half.
            reflexivity.
        }
        intros i j i_ge j_ge.
        destruct (connex i j) as [leq|leq].
        -   exact (wlog _ _ i_ge leq).
        -   rewrite abs_minus.
            exact (wlog _ _ j_ge leq).
    }
    assert (cauchy_seq b) as b_cauchy.
    {
        intros ε ε_pos.
        assert (∀ n, |b n - b (nat_suc n)| ≤ d 0 / 2^(nat_suc n)) as b_gap.
        {
            intros n.
            rewrite <- d_eq.
            pose proof (Logic.eq_refl (d (nat_suc n))) as eq.
            unfold d in eq at 1.
            unfold a, b in eq; cbn in eq.
            pose proof (d_pos (nat_suc n)) as ltq.
            unfold d, a, b in ltq; cbn in ltq.
            unfold d, a, b; cbn.
            case_if [S'd|S'd]; cbn in *.
            -   rewrite (plus_comm (fst (p n))).
                rewrite rdist, neg_plus.
                rewrite plus_assoc.
                rewrite <- (plus_half (snd (p n))) at 1.
                rewrite plus_rrinv.
                rewrite <- (plus_half (fst (p n))) at 3.
                rewrite neg_plus, plus_assoc.
                rewrite plus_rrinv.
                rewrite abs_pos_eq; [>apply refl|].
                rewrite plus_comm in ltq.
                rewrite rdist, plus_assoc in ltq.
                rewrite <- (plus_half (fst (p n))) in ltq at 1.
                rewrite neg_plus in ltq.
                rewrite plus_rlinv in ltq.
                rewrite plus_comm in ltq.
                apply ltq.
            -   rewrite plus_rinv.
                rewrite <- abs_zero.
                rewrite eq.
                apply d_pos.
        }
        pose proof (lt_mult ε_pos (div_pos (d_pos 0))) as ε'_pos.
        pose proof (arch_pow2 _ ε'_pos) as [N N_lt].
        exists N.
        assert (∀ i j, N ≤ i → i ≤ j → |b i - b j| < ε) as wlog.
        {
            intros i j i_ge leq.
            apply nat_le_ex in leq as [c c_eq]; subst.
            rewrite <- lt_mult_lrmove_pos in N_lt by apply d_pos.
            rewrite mult_comm in N_lt.
            apply (trans2 N_lt).
            clear ε ε_pos ε'_pos N_lt.
            revert N i i_ge.
            nat_induction c; intros.
            {
                rewrite plus_rid.
                rewrite plus_rinv, <- abs_zero.
                apply lt_mult.
                -   apply d_pos.
                -   apply div_pos.
                    apply nat_pow_pos2.
                    exact two_pos.
            }
            rewrite <- (plus_rlinv (b i) (b (nat_suc i))).
            rewrite <- plus_assoc.
            apply (le_lt_trans (abs_tri _ _)).
            specialize (b_gap i).
            rewrite <- nat_sucs_le in i_ge.
            specialize (IHc _ _ i_ge).
            pose proof (nat_pow_le (U := rat) 2 _ _ (land lt_1_2) i_ge) as leq.
            apply le_div_pos in leq; [>|apply nat_pow_pos2; exact two_pos].
            apply le_lmult_pos with (d 0) in leq; [>|apply d_pos].
            pose proof (trans b_gap leq) as b_gap'.
            pose proof (le_lt_lrplus b_gap' IHc) as ltq.
            applys_eq ltq.
            rewrite <- ldist.
            cbn.
            rewrite div_mult; [>|apply nat_pow_pos2; exact two_pos|apply two_pos].
            rewrite div_mult; [>|apply nat_pow_pos2; exact two_pos|apply two_pos].
            rewrite plus_half.
            reflexivity.
        }
        intros i j i_ge j_ge.
        destruct (connex i j) as [leq|leq].
        -   exact (wlog _ _ i_ge leq).
        -   rewrite abs_minus.
            exact (wlog _ _ j_ge leq).
    }
    pose (a1 := to_equiv_type real_equiv (make_real a a_cauchy)).
    pose (b1 := to_equiv_type real_equiv (make_real b b_cauchy)).
    assert (a1 = b1) as ab_eq.
    {
        unfold a1, b1; equiv_simpl.
        intros ε ε_pos.
        pose proof (arch_pow2 _ (lt_mult ε_pos (div_pos (d_pos 0))))
            as [N N_ltq].
        exists N.
        intros i i_ge.
        rewrite abs_minus.
        rewrite (abs_pos_eq _ (land (d_pos i))).
        rewrite d_eq.
        assert (le (U := rat) (2^N) (2^i)) as i_ge'.
        {
            apply nat_le_ex in i_ge as [c c_eq]; subst i.
            nat_induction c.
            -   rewrite plus_rid.
                apply refl.
            -   rewrite nat_plus_rsuc.
                rewrite nat_pow_suc.
                rewrite ldist, mult_rid.
                apply (trans IHc).
                rewrite <- le_plus_0_a_b_ab.
                apply nat_pow_pos2.
                exact two_pos.
        }
        apply le_div_pos in i_ge'; [>|apply nat_pow_pos2; exact two_pos].
        apply (le_lt_trans i_ge') in N_ltq.
        rewrite <- lt_mult_lrmove_pos in N_ltq by apply d_pos.
        rewrite mult_comm.
        exact N_ltq.
    }
    exists a1.
    split.
    -   rewrite ab_eq.
        intros x Sx.
        classic_contradiction ltq.
        rewrite nle_lt in ltq.
        equiv_get_value x.
        apply real_lt in ltq as [ε [N1 [ε_pos ltq]]]; cbn in ltq.
        pose proof (half_pos ε_pos) as ε2_pos.
        pose proof (b_cauchy _ ε2_pos) as [N2 cauchy].
        specialize (b_upper (max N1 N2) _ Sx).
        unfold rat_to_real, le in b_upper; equiv_simpl in b_upper.
        unfold plus, neg in b_upper; equiv_simpl in b_upper.
        destruct b_upper as [b_eq|b_leq].
        +   unfold zero in b_eq; cbn in b_eq.
            unfold rat_to_real in b_eq; equiv_simpl in b_eq.
            specialize (b_eq _ ε2_pos) as [N3 b_eq].
            pose (N := max (max N1 N2) N3).
            specialize (ltq N).
            prove_parts ltq; [>apply (trans (lmax N1 N2)); apply lmax|].
            specialize (b_eq N (rmax _ _)).
            rewrite abs_minus in b_eq.
            rewrite neg_zero, plus_rid in b_eq.
            specialize (cauchy (max N1 N2) N).
            prove_parts cauchy.
            1: apply rmax.
            1: apply (trans (rmax N1 N2)); apply lmax.
            clearbody b N.
            remember (max N1 N2) as N'.
            clear - ltq cauchy b_eq.
            rewrite abs_minus in b_eq.
            apply (le_lt_trans (abs_le_pos _)) in cauchy.
            apply (le_lt_trans (abs_le_pos _)) in b_eq.
            pose proof (lt_lrplus b_eq cauchy) as ltq'.
            rewrite plus_half in ltq'.
            rewrite plus_assoc in ltq'.
            rewrite plus_rlinv in ltq'.
            rewrite <- lt_plus_rrmove in ltq'.
            rewrite plus_comm in ltq'.
            destruct (trans ltq ltq'); contradiction.
        +   cbn in b_leq.
            destruct b_leq as [N3 b_leq].
            pose (N := max (max N1 N2) N3).
            specialize (b_leq N (rmax _ _)).
            specialize (ltq N).
            prove_parts ltq; [>apply (trans (lmax N1 N2)); apply lmax|].
            specialize (cauchy (max N1 N2) N).
            prove_parts cauchy.
            1: apply rmax.
            1: apply (trans (rmax N1 N2)); apply lmax.
            clearbody b N.
            remember (max N1 N2) as N'.
            clear - ε2_pos b_leq ltq cauchy.
            rewrite le_plus_0_anb_b_a in b_leq.
            pose proof (lt_le_trans ltq b_leq) as ltq'.
            apply lt_rplus with (ε/2) in ε2_pos.
            rewrite plus_half, plus_lid in ε2_pos.
            apply (trans2 ε2_pos) in cauchy.
            apply (le_lt_trans (abs_le_pos _)) in cauchy.
            rewrite <- lt_plus_rrmove in cauchy.
            rewrite plus_comm in cauchy.
            destruct (trans cauchy ltq'); contradiction.
    -   intros y y_upper.
        classic_contradiction ltq.
        rewrite nle_lt in ltq.
        equiv_get_value y.
        apply real_lt in ltq as [ε [N1 [ε_pos ltq]]]; cbn in ltq.
        pose proof (half_pos ε_pos) as ε2_pos.
        pose proof (a_cauchy _ ε2_pos) as [N2 cauchy].
        pose proof (upper_bound_leq _ _ _ (a_lower (max N1 N2)) y_upper)
            as [leq neq]; clear neq.
        unfold rat_to_real, le in leq; equiv_simpl in leq.
        unfold plus, neg in leq; equiv_simpl in leq.
        destruct leq as [a_eq|a_leq].
        +   unfold zero in a_eq; cbn in a_eq.
            unfold rat_to_real in a_eq; equiv_simpl in a_eq.
            specialize (a_eq _ ε2_pos) as [N3 a_eq].
            pose (N := max (max N1 N2) N3).
            specialize (ltq N).
            prove_parts ltq; [>apply (trans (lmax N1 N2)); apply lmax|].
            specialize (a_eq N (rmax _ _)).
            rewrite abs_minus in a_eq.
            rewrite neg_zero, plus_rid in a_eq.
            specialize (cauchy N (max N1 N2)).
            prove_parts cauchy.
            1: apply (trans (rmax N1 N2)); apply lmax.
            1: apply rmax.
            clearbody a N.
            remember (max N1 N2) as N'.
            clear - ltq cauchy a_eq.
            rewrite abs_minus in a_eq.
            apply (le_lt_trans (abs_le_pos _)) in cauchy.
            apply (le_lt_trans (abs_le_pos _)) in a_eq.
            pose proof (lt_lrplus cauchy a_eq) as ltq'.
            rewrite plus_half in ltq'.
            rewrite plus_assoc in ltq'.
            rewrite plus_rlinv in ltq'.
            rewrite <- lt_plus_rrmove in ltq'.
            rewrite plus_comm in ltq'.
            destruct (trans ltq ltq'); contradiction.
        +   cbn in a_leq.
            destruct a_leq as [N3 a_leq].
            pose (N := max (max N1 N2) N3).
            specialize (a_leq N (rmax _ _)).
            specialize (ltq N).
            prove_parts ltq; [>apply (trans (lmax N1 N2)); apply lmax|].
            specialize (cauchy N (max N1 N2)).
            prove_parts cauchy.
            1: apply (trans (rmax N1 N2)); apply lmax.
            1: apply rmax.
            clearbody a N.
            remember (max N1 N2) as N'.
            clear - ε2_pos a_leq ltq cauchy.
            rewrite le_plus_0_anb_b_a in a_leq.
            apply lt_rplus with (ε/2) in ε2_pos.
            rewrite plus_half, plus_lid in ε2_pos.
            apply (trans2 ε2_pos) in cauchy.
            apply (le_lt_trans (abs_le_pos _)) in cauchy.
            rewrite <- lt_plus_rrmove in cauchy.
            rewrite plus_comm in cauchy.
            pose proof (trans ltq cauchy) as ltq'.
            apply lt_plus_rcancel in ltq'.
            rewrite <- nle_lt in ltq'.
            contradiction.
Qed.

Close Scope nat_scope.
