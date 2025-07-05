Require Import init.

Require Export cauchy_real_order.
Require Import nat.

Open Scope nat_scope.

Module RealComplete.
Section RealComplete.

Context (S : real → Prop) (S_ex : ∃ x, S x) (S_upper : has_upper_bound le S).

Let S' x := is_upper_bound le S (rat_to_real x).

Lemma upper_ex : ∃ q : rat, S' q.
Proof.
    destruct S_upper as [u u_upper].
    equiv_get_value u.
    pose proof (cauchy_bounded u) as [M M_bound].
    exists M.
    intros x Sx.
    apply (trans (u_upper x Sx)).
    unfold le, rat_to_real; equiv_simpl.
    unfold real_pos, plus, neg; equiv_simpl.
    right; cbn.
    exists 0.
    intros i i_ge.
    rewrite le_plus_0_anb_b_a.
    specialize (M_bound i).
    apply (le_lt_trans (abs_le_pos _)) in M_bound.
    apply M_bound.
Qed.

Let u := ex_val upper_ex.
Let u_upper := ex_proof upper_ex : S' u.

Lemma lower_ex : ∃ q : rat, ¬S' q.
Proof.
    destruct S_ex as [l Sl].
    equiv_get_value l.
    pose proof (cauchy_bounded l) as [M M_bound].
    assert (∀ N, ¬(M + 1 + l N < 1)) as lem.
    {
        intros N eq.
        rewrite plus_comm, plus_assoc in eq.
        rewrite <- lt_plus_a_0_ab_b in eq.
        specialize (M_bound N).
        apply (le_lt_trans (abs_le_neg _)) in M_bound.
        rewrite lt_plus_ab_0_b_na in eq.
        contradiction (irrefl _ (trans eq M_bound)).
    }
    exists (-M - 1).
    intros M_upper.
    specialize (M_upper _ Sl) as leq.
    unfold le, rat_to_real in leq; equiv_simpl in leq.
    unfold real_pos, plus at 1, neg at 5 in leq; equiv_simpl in leq.
    destruct leq as [eq|leq].
    -   unfold zero in eq; cbn in eq.
        unfold rat_to_real in eq; equiv_simpl in eq.
        specialize (eq 1 one_pos) as [N eq].
        specialize (eq N (refl N)).
        rewrite plus_lid in eq.
        do 2 rewrite neg_plus in eq.
        do 3 rewrite neg_neg in eq.
        apply (le_lt_trans (abs_le_pos _)) in eq.
        contradiction (lem _ eq).
    -   cbn in leq.
        destruct leq as [N leq].
        specialize (leq N (refl N)).
        do 2 rewrite <- neg_plus in leq.
        rewrite <- neg_pos in leq.
        contradiction (lem _ (le_lt_trans leq one_pos)).
Qed.

Let l := ex_val lower_ex.
Let l_lower := ex_proof lower_ex : ¬S' l.

Fixpoint p (n : nat) := match n with
    | nat_zero => (l, u)
    | nat_suc n' => let m := (fst (p n') + snd (p n')) / 2 in
        If S' m then (fst (p n'), m)
        else (m, snd (p n'))
    end.

Let a n := fst (p n).
Let b n := snd (p n).

Lemma a_lower : ∀ i, ¬S' (a i).
Proof.
    nat_induction i.
    -   unfold zero; cbn.
        exact l_lower.
    -   unfold a; cbn.
        classic_case (S' ((fst (p i) + snd (p i)) / 2)) as [p_in|p_nin]; cbn.
        +   exact IHi.
        +   exact p_nin.
Qed.

Lemma b_upper : ∀ i, S' (b i).
Proof.
    nat_induction i.
    -   unfold zero; cbn.
        exact u_upper.
    -   unfold b; cbn.
        classic_case (S' ((fst (p i) + snd (p i)) / 2)) as [p_in|p_nin]; cbn.
        +   exact p_in.
        +   exact IHi.
Qed.

Let d n := b n - a n.

Lemma d_suc : ∀ n, d (nat_suc n) = d n / 2.
Proof.
    intros n.
    unfold d, a, b; cbn.
    classic_case (S' ((fst (p n) + snd (p n)) / 2)) as [p_in|p_nin]; cbn.
    -   rewrite (plus_comm (fst (p n))).
        do 2 rewrite rdist.
        rewrite <- plus_assoc.
        rewrite half_minus.
        rewrite mult_lneg.
        reflexivity.
    -   rewrite (plus_comm (fst (p n))).
        do 2 rewrite rdist.
        rewrite neg_plus.
        rewrite plus_assoc.
        rewrite minus_half.
        rewrite mult_lneg.
        reflexivity.
Qed.

Lemma d_eq : ∀ n, d n = d 0 / 2^n.
Proof.
    nat_induction n.
    {
        rewrite nat_pow_zero.
        rewrite div_one, mult_rid.
        reflexivity.
    }
    rewrite nat_pow_suc.
    rewrite div_mult; [>|apply nat_pow_not_zero; apply two_pos|apply two_pos].
    rewrite mult_assoc.
    rewrite <- IHn.
    apply d_suc.
Qed.

Lemma d_pos : ∀ n, 0 < d n.
Proof.
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
Qed.

Lemma d_pos_leq : ∀ q n, |q - q| < d n.
Proof.
    intros q n.
    rewrite plus_rinv, <- abs_zero.
    apply d_pos.
Qed.

Lemma ab_cauchy : ∀ x, (∀ n, |x n - x (nat_suc n)| ≤ d (nat_suc n)) →
    cauchy_seq x.
Proof.
    intros x x_gap ε ε_pos.
    pose proof (lt_mult ε_pos (div_pos (d_pos 0))) as ε'_pos.
    pose proof (arch_pow2 _ ε'_pos) as [N N_lt].
    exists N.
    assert (∀ i j, N ≤ i → i ≤ j → |x i - x j| < ε) as wlog.
    {
        intros i j i_ge leq.
        apply nat_le_ex in leq as [c c_eq]; subst.
        rewrite <- lt_mult_lrmove_pos in N_lt by apply d_pos.
        rewrite mult_comm in N_lt.
        rewrite <- d_eq in N_lt.
        apply (trans2 N_lt).
        clear ε ε_pos ε'_pos N_lt.
        revert N i i_ge.
        nat_induction c; intros.
        1: rewrite plus_rid; apply d_pos_leq.
        specialize (x_gap i).
        rewrite <- nat_sucs_le in i_ge.
        specialize (IHc _ _ i_ge).
        pose proof (nat_pow_le (U := rat) 2 _ _ (land lt_1_2) i_ge) as leq.
        apply le_div_pos in leq; [>|apply nat_pow_pos2; exact two_pos].
        apply le_lmult_pos with (d 0) in leq; [>|apply d_pos].
        do 2 rewrite <- d_eq in leq.
        pose proof (trans x_gap leq) as x_gap'.
        pose proof (le_lt_lrplus x_gap' IHc) as ltq.
        apply (le_lt_trans (abs_tri _ _)) in ltq.
        rewrite plus_assoc in ltq.
        rewrite plus_rlinv in ltq.
        applys_eq ltq.
        rewrite d_suc.
        symmetry; apply plus_half.
    }
    intros i j i_ge j_ge.
    destruct (connex i j) as [leq|leq].
    -   exact (wlog _ _ i_ge leq).
    -   rewrite abs_minus.
        exact (wlog _ _ j_ge leq).
Qed.

Lemma cauchy_leq : ∀ n, 0 ≤ snd (p n) / 2 - fst (p n) / 2.
Proof.
    intros n.
    rewrite <- mult_lneg.
    rewrite <- rdist.
    rewrite <- d_suc.
    apply d_pos.
Qed.

Lemma a_cauchy : cauchy_seq a.
Proof.
    apply ab_cauchy.
    intros n.
    unfold a; cbn.
    classic_case (S' ((fst (p n) + snd (p n)) / 2)) as [S'd|S'd]; cbn.
    -   apply d_pos_leq.
    -   rewrite d_suc.
        unfold d.
        rewrite rdist, rdist, neg_plus, mult_lneg.
        rewrite plus_assoc.
        rewrite minus_half.
        rewrite abs_minus.
        rewrite abs_pos_eq by apply cauchy_leq.
        apply refl.
Qed.

Lemma b_cauchy : cauchy_seq b.
Proof.
    apply ab_cauchy.
    intros n.
    unfold b; cbn.
    classic_case (S' ((fst (p n) + snd (p n)) / 2)) as [S'd|S'd]; cbn.
    -   rewrite d_suc.
        unfold d.
        rewrite (plus_comm (fst (p n))).
        rewrite rdist, rdist, neg_plus, mult_lneg.
        rewrite plus_assoc.
        rewrite minus_half.
        rewrite abs_pos_eq by apply cauchy_leq.
        apply refl.
    -   apply d_pos_leq.
Qed.

Definition a1 := to_equiv real_equiv (make_real a a_cauchy).
Let b1 := to_equiv real_equiv (make_real b b_cauchy).

Lemma ab_eq : a1 = b1.
Proof.
    symmetry.
    unfold a1, b1; equiv_simpl.
    intros ε ε_pos.
    pose proof (arch_pow2 _ (lt_mult ε_pos (div_pos (d_pos 0)))) as [N N_ltq].
    exists N.
    intros i i_ge.
    rewrite <- lt_mult_lrmove_pos in N_ltq by apply d_pos.
    rewrite mult_comm in N_ltq.
    apply (le_lt_trans2 N_ltq).
    rewrite (abs_pos_eq _ (land (d_pos i))).
    rewrite d_eq.
    apply le_lmult_pos; [>apply d_pos|].
    apply le_div_pos; [>apply nat_pow_pos2; exact two_pos|].
    apply nat_pow_le; [>apply lt_1_2|].
    exact i_ge.
Qed.

Lemma a1_sup : is_supremum le S a1.
Proof.
    split.
    -   rewrite ab_eq.
        intros x Sx.
        apply real_leq_seq.
        intros n.
        apply b_upper.
        exact Sx.
    -   intros y y_upper.
        apply le_neg.
        unfold neg at 2; equiv_simpl.
        apply real_leq_seq.
        intros n.
        apply le_neg.
        rewrite neg_neg.
        applys_eq (land (upper_bound_leq _ _ _ (a_lower n) y_upper)).
        unfold neg at 1, rat_to_real; equiv_simpl.
        apply real_eq_zero.
        intros i.
        apply plus_linv.
Qed.

End RealComplete.
End RealComplete.

Global Instance real_sup_complete : SupremumComplete (U := real) le.
Proof.
    split.
    intros S S_ex S_upper.
    exists (RealComplete.a1 S S_ex S_upper).
    apply RealComplete.a1_sup.
Qed.

Close Scope nat_scope.
