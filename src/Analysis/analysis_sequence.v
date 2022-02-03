Require Import init.

Require Export analysis_base.
Require Import analysis_topology.
Require Import order_minmax.

Definition cauchy_seq {U} `{Metric U} (f : sequence U) :=
    ∀ ε, 0 < ε → ∃ N, ∀ i j, N <= i → N <= j → d (f i) (f j) < ε.

Definition complete U `{Metric U} := ∀ f, cauchy_seq f → seq_converges f.

Definition seq_bounded {U} `{Metric U} (f : nat → U)
    := ∃ M, ∀ m n, d (f m) (f n) <= M.
(* begin hide *)

Section AnalysisSequence.

Context {U} `{Metric U}.
(* end hide *)

Theorem metric_seq_lim : ∀ f x, seq_lim f x ↔
        ∀ ε, 0 < ε → ∃ N, ∀ n, N <= n → d x (f n) < ε.
    intros f x.
    rewrite basis_seq_lim.
    split.
    -   intros lim ε ε_pos.
        pose proof (open_ball_basis x [ε|ε_pos]) as x_basis.
        pose proof (open_ball_self x [ε|ε_pos]) as x_in.
        exact (lim _ x_basis x_in).
    -   intros lim S S_basis Sx.
        destruct S_basis as [z [ε eq]]; subst S.
        pose proof (open_ball_ex _ _ _ Sx) as [δ sub].
        specialize (lim [δ|] [|δ]) as [N lim].
        exists N.
        intros n n_gt.
        apply sub.
        apply lim.
        exact n_gt.
Qed.

Theorem metric_seq_closure : ∀ (A : U → Prop) x,
        (∃ f, (∀ n, A (f n)) ∧ seq_lim f x) ↔ closure A x.
    intros A x.
    split.
    -   intros [f [Af lim]].
        exact (seq_closure A x f Af lim).
    -   intros Ax.
        assert (∀ n, 0 < / nat_to_real (nat_suc n)) as n_pos.
        {
            intros n.
            apply div_pos.
            change 0 with (nat_to_real 0).
            rewrite nat_to_real_lt.
            apply nat_zero_lt_suc.
        }
        pose (B n := open_ball x [_|n_pos n]).
        assert (∀ n, ∃ a, B n a ∧ A a) as f_ex.
        {
            intros n.
            rewrite in_closure in Ax.
            assert (open (B n)) as B_open.
            {
                unfold B.
                apply open_ball_open.
            }
            assert (B n x) as Bnx by apply open_ball_self.
            specialize (Ax (B n) B_open Bnx).
            apply not_empty_ex in Ax as [a a_in].
            rewrite comm in a_in.
            exists a.
            exact a_in.
        }
        exists (λ n, ex_val (f_ex n)).
        split.
        +   intros n.
            rewrite_ex_val a a_in.
            apply a_in.
        +   rewrite metric_seq_lim.
            intros ε ε_pos.
            pose proof (archimedean2 _ ε_pos) as [N N_lt].
            rewrite nat_to_abstract_real in N_lt.
            exists N.
            intros n n_gt.
            rewrite_ex_val a a_in.
            destruct a_in as [Bna Aa].
            unfold B in Bna.
            apply (trans2 N_lt).
            rewrite <- nat_sucs_le in n_gt.
            rewrite <- nat_to_real_le in n_gt.
            assert (0 < nat_to_real (nat_suc N)) as N_pos.
            {
                change 0 with (nat_to_real 0).
                rewrite nat_to_real_lt.
                apply nat_zero_lt_suc.
            }
            apply le_div_pos in n_gt.
            2: exact N_pos.
            apply (lt_le_trans2 n_gt).
            exact Bna.
Qed.

Theorem metric_seq_closed :
        ∀ A, closed A ↔ (∀ f x, (∀ n, A (f n)) → seq_lim f x → A x).
    intros A.
    split.
    -   intros A_closed f x Af fx.
        apply closed_if_closure in A_closed.
        rewrite A_closed.
        exact (seq_closure A x f Af fx).
    -   intros all_f.
        apply closed_if_closure.
        apply antisym; try apply closure_sub.
        intros x Ax.
        apply metric_seq_closure in Ax.
        destruct Ax as [f [all_n f_seq]].
        exact (all_f f x all_n f_seq).
Qed.

Theorem converges_cauchy : ∀ f, seq_converges f → cauchy_seq f.
    intros f [x fx] ε ε_pos.
    pose proof (half_pos _ ε_pos) as ε2_pos.
    rewrite metric_seq_lim in fx.
    specialize (fx _ ε2_pos) as [N fx].
    exists N.
    intros i j i_gt j_gt.
    pose proof (lt_lrplus (fx i i_gt) (fx j j_gt)) as ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans2 ltq).
    rewrite (d_sym x).
    apply d_tri.
Qed.

Theorem limit_point_seq_ex :
        ∀ X x, limit_point X x → ∃ f, (∀ n, X (f n) ∧ x ≠ f n) ∧ seq_lim f x.
    intros X x x_lim.
    assert (∀ n, ∃ a, open_ball x [_|real_n_div_pos n] a ∧ X a ∧ x ≠ a) as f_ex.
    {
        intros n.
        unfold limit_point in x_lim.
        specialize (x_lim (open_ball x [_|real_n_div_pos n])).
        specialize (x_lim (open_ball_open _ _) (open_ball_self _ _)).
        apply not_empty_ex in x_lim.
        destruct x_lim as [a [[Xa nxa] a_in]].
        exists a.
        unfold singleton in nxa.
        split; [>|split]; assumption.
    }
    exists (λ n, ex_val (f_ex n)).
    split.
    -   intros n.
        rewrite_ex_val a a_H.
        split; apply a_H.
    -   rewrite metric_seq_lim.
        intros ε ε_pos.
        pose proof (archimedean2 ε ε_pos) as [N N_lt].
        rewrite nat_to_abstract_real in N_lt.
        exists N.
        intros m m_geq.
        rewrite_ex_val b b_H.
        destruct b_H as [b_in [Xb xb]].
        unfold open_ball in b_in; cbn in b_in.
        apply (trans b_in).
        apply (le_lt_trans2 N_lt).
        apply le_div_pos.
        1: apply real_n_pos.
        rewrite nat_to_real_le.
        rewrite nat_sucs_le.
        exact m_geq.
Qed.

Theorem cauchy_subseq_converge :
        ∀ a b x, cauchy_seq a → subsequence a b → seq_lim b x → seq_lim a x.
    intros a b x a_cauchy [f [f_sub ab_eq]] b_lim.
    rewrite metric_seq_lim in *.
    intros ε ε_pos.
    pose proof (half_pos ε ε_pos) as ε2_pos.
    specialize (b_lim (ε / 2) ε2_pos) as [N1 b_lim].
    specialize (a_cauchy (ε / 2) ε2_pos) as [N2 a_cauchy].
    exists (max N1 N2).
    intros n n_geq.
    specialize (b_lim n (trans (lmax N1 N2) n_geq)).
    rewrite <- ab_eq in b_lim.
    pose proof (subsequence_seq_leq f f_sub n) as fn_leq.
    apply (trans n_geq) in fn_leq.
    apply (trans (rmax N1 N2)) in n_geq, fn_leq.
    specialize (a_cauchy (f n) n fn_leq n_geq).
    pose proof (lt_lrplus b_lim a_cauchy) as ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans2 ltq).
    apply d_tri.
Qed.

(* begin hide *)
Open Scope card_scope.
(* end hide *)
Theorem cauchy_bounded : ∀ a, cauchy_seq a → seq_bounded a.
    intros a a_cauchy.
    specialize (a_cauchy 1 one_pos) as [N a_cauchy].
    classic_case (0 = N) as [N_z|N_nz].
    {
        exists 1.
        intros i j.
        subst N.
        apply a_cauchy; apply nat_le_zero.
    }
    pose (S m := ∃ i j, i < 1 + N ∧ j < 1 + N ∧ m = d (a i) (a j)).
    assert (finite (|set_type S|)) as S_fin.
    {
        unfold finite.
        apply (le_lt_trans2 (nat_is_finite ((1 + N)*(1 + N)))).
        rewrite <- nat_to_card_mult.
        unfold mult, le, nat_to_card; equiv_simpl.
        pose (to_i (x : set_type S) := ex_val [|x]).
        pose (to_j (x : set_type S) := ex_val (ex_proof [|x])).
        pose (to_i_lt (x : set_type S)
            := land (ex_proof (ex_proof [|x]))).
        pose (to_j_lt (x : set_type S)
            := land (rand (ex_proof (ex_proof [|x])))).
        exists (λ x : set_type S, ([to_i x|to_i_lt x], [to_j x|to_j_lt x])).
        intros x y eq.
        inversion eq as [[eq1 eq2]].
        clear eq to_i_lt to_j_lt.
        unfold to_i, to_j in *.
        unfold ex_val in eq1 at 1; unfold ex_proof in eq2 at 1.
        destruct (ex_to_type _) as [i C0]; cbn in *.
        rewrite_ex_val j [i_lt [j_lt x_eq]]; clear C0.
        unfold ex_val in eq1; unfold ex_proof in eq2.
        destruct (ex_to_type _) as [i' C0]; cbn in *.
        rewrite_ex_val j' [i'_lt [j'_lt y_eq]]; clear C0.
        subst i' j'.
        apply set_type_eq.
        rewrite x_eq, y_eq.
        reflexivity.
    }
    assert (∃ x, S x) as S_ex.
    {
        exists (d (a 0) (a 0)). (* Really just zero, but this is simpler. *)
        exists 0, 0.
        split.
        2: split.
        1, 2: split; try apply nat_le_zero.
        1, 2: intros contr; inversion contr.
        reflexivity.
    }
    pose proof (finite_well_ordered_set_max S S_fin S_ex) as [M[Sm M_greatest]].
    assert (∀ i j, i < 1 + N → j < 1 + N → d (a i) (a j) < M + 1) as lem1.
    {
        intros i j i_lt j_lt.
        pose proof one_pos as ltq.
        apply lt_lplus with M in ltq.
        rewrite plus_rid in ltq.
        apply (le_lt_trans2 ltq).
        apply M_greatest.
        exists i, j.
        split.
        2: split.
        -   exact i_lt.
        -   exact j_lt.
        -   reflexivity.
    }
    assert (∀ i j, 1 + N <= i → j < 1 + N → d (a i) (a j) < M + 1) as lem2.
    {
        intros i j i_ge j_lt.
        pose proof (trans (nat_le_suc N) i_ge) as i_ge2.
        specialize (a_cauchy _ _ i_ge2 (refl N)).
        assert (d (a N) (a j) <= M) as leq.
        {
            apply M_greatest.
            exists N, j.
            split.
            2: split.
            -   apply nat_lt_suc.
            -   exact j_lt.
            -   reflexivity.
        }
        pose proof (le_lt_lrplus leq a_cauchy) as ltq.
        clear - ltq.
        apply (le_lt_trans2 ltq).
        rewrite plus_comm.
        apply d_tri.
    }
    assert (∀ i j, 1 + N <= i → 1 + N <= j → d (a i) (a j) < M + 1) as lem3.
    {
        intros i j i_ge j_ge.
        assert (N <= i) as i_ge2.
        {
            apply (trans2 i_ge).
            apply nat_le_suc.
        }
        assert (N <= j) as j_ge2.
        {
            apply (trans2 j_ge).
            apply nat_le_suc.
        }
        specialize (a_cauchy i j i_ge2 j_ge2).
        apply (lt_le_trans a_cauchy).
        rewrite <- (plus_lid 1) at 1.
        apply le_rplus.
        apply M_greatest.
        exists 0, 0.
        split.
        2: split.
        1, 2: apply nat_zero_lt_suc.
        rewrite d_zero.
        reflexivity.
    }
    exists (M + 1).
    intros i j.
    classic_case (i < 1 + N) as [i_lt|i_ge];
    classic_case (j < 1 + N) as [j_lt|j_ge].
    -   apply lem1; assumption.
    -   rewrite nlt_le in j_ge.
        rewrite d_sym.
        apply lem2; assumption.
    -   rewrite nlt_le in i_ge.
        apply lem2; assumption.
    -   rewrite nlt_le in i_ge, j_ge.
        apply lem3; assumption.
Qed.
(* begin hide *)

Close Scope card_scope.

End AnalysisSequence.
(* end hide *)
