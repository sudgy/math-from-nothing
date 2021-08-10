Require Import init.

Require Import topology.
Require Import mult_div.

Section FiniteComplement.

Variable U : Type.

Open Scope card_scope.

Program Instance finite_complement_topology : Topology U := {
    open S := finite (|set_type (complement S)|) ∨ complement S = all
}.
Next Obligation.
    right.
    exact compl_empty.
Qed.
Next Obligation.
    left.
    rewrite compl_all.
    exact empty_finite.
Qed.
Next Obligation.
    rename S into SS.
    classic_case (⋃ SS = ∅) as [SS_empty|SS_nempty].
    -   right.
        rewrite SS_empty.
        exact compl_empty.
    -   left.
        rewrite big_union_compl.
        apply finite_inter_finite.
        apply not_empty_ex in SS_nempty as [x [S [SS_S Sx]]].
        exists (complement S).
        rewrite compl_compl.
        split.
        1: exact SS_S.
        apply H in SS_S.
        destruct SS_S as [SS_S|SS_S].
        1: exact SS_S.
        apply (f_equal complement) in SS_S.
        rewrite compl_compl in SS_S.
        rewrite compl_all in SS_S.
        rewrite SS_S in Sx.
        contradiction Sx.
Qed.
Next Obligation.
    rename S into SS.
    rename H0 into SS_fin.
    classic_case (⋂ SS = ∅) as [SS_empty|SS_nempty].
    -   right.
        rewrite SS_empty.
        exact compl_empty.
    -   left.
        rewrite big_inter_compl.
        apply finite_union_finite.
        +   apply (le_lt_trans2 SS_fin).
            unfold le; equiv_simpl.
            assert (∀ A, SS (complement A) → SS (complement A)) as A_in
                by trivial.
            exists (λ A : set_type (λ S, SS (complement S)), [_|A_in [A|][|A]]).
            intros A B eq.
            inversion eq as [eq2].
            apply (f_equal complement) in eq2.
            do 2 rewrite compl_compl in eq2.
            apply set_type_eq in eq2.
            exact eq2.
        +   intros S SS_S.
            specialize (H _ SS_S); cbn in H.
            rewrite compl_compl in H.
            destruct H as [H|H].
            1: exact H.
            rewrite H in SS_S.
            rewrite compl_all in SS_S.
            apply not_empty_ex in SS_nempty as [x x_in].
            specialize (x_in _ SS_S).
            contradiction x_in.
Qed.

Program Instance countable_complement_topology : Topology U := {
    open S := countable (|set_type (complement S)|) ∨ complement S = all
}.
Next Obligation.
    right.
    exact compl_empty.
Qed.
Next Obligation.
    left.
    rewrite compl_all.
    apply empty_finite.
Qed.
Next Obligation.
    rename S into SS.
    classic_case (⋃ SS = ∅) as [SS_empty|SS_nempty].
    -   right.
        rewrite SS_empty.
        exact compl_empty.
    -   left.
        rewrite big_union_compl.
        pose proof SS_nempty as SS_nempty2.
        apply not_empty_ex in SS_nempty2 as [x [S [SS_S Sx]]].
        apply (inter_le (λ A, (SS (complement A))) (complement S)).
        +   rewrite compl_compl.
            exact SS_S.
        +   apply H in SS_S.
            destruct SS_S as [SS_S|SS_S].
            1: exact SS_S.
            apply (f_equal complement) in SS_S.
            rewrite compl_compl in SS_S.
            rewrite compl_all in SS_S.
            rewrite SS_S in Sx.
            contradiction Sx.
Qed.
Next Obligation.
    rename S into SS.
    rename H0 into SS_fin.
    classic_case (⋂ SS = ∅) as [SS_empty|SS_nempty].
    -   right.
        rewrite SS_empty.
        exact compl_empty.
    -   left.
        rewrite big_inter_compl.
        apply countable_union_countable.
        +   apply (le_lt_trans2 SS_fin).
            unfold le; equiv_simpl.
            exists (λ S : set_type (λ A, SS (complement A)),
                [complement [S|] | [|S]]).
            intros a b eq.
            inversion eq as [eq2].
            apply (f_equal complement) in eq2.
            do 2 rewrite compl_compl in eq2.
            apply set_type_eq in eq2.
            exact eq2.
        +   intros S SS_S.
            specialize (H _ SS_S); cbn in H.
            rewrite compl_compl in H.
            destruct H as [H|H].
            *   exact H.
            *   rewrite H in SS_S.
                rewrite compl_all in SS_S.
                apply not_empty_ex in SS_nempty.
                destruct SS_nempty as [x SS_nempty].
                specialize (SS_nempty _ SS_S).
                contradiction SS_nempty.
Qed.

End FiniteComplement.

Open Scope card_scope.

Definition inf_compl_open {U} (S : U → Prop) :=
    infinite (|set_type (complement S)|) ∨ S = all ∨ S = ∅.

Theorem inf_compl_not_top :
        ∃ U, ¬(∃ Top : Topology U, @open U Top = inf_compl_open).
    exists nat0.
    intros [Top eq].
    pose (S1 (n : nat0) := ∃ m, n = 2*m + 1).
    pose (S2 (n : nat0) := ∃ m, n = 2*m + 2).
    assert (open S1) as S1_open.
    {
        rewrite eq.
        left.
        apply all_greater_inf.
        {
            exists 0.
            intros [m m_eq].
            rewrite plus_comm in m_eq.
            inversion m_eq.
        }
        intros [a a_even].
        unfold complement, S1 in a_even.
        assert (complement S1 (a + 2)) as a2_even.
        {
            intros [m a_eq].
            nat0_destruct m.
            -   rewrite mult_ranni, plus_lid in a_eq.
                rewrite plus_comm in a_eq.
                inversion a_eq.
            -   rewrite nat0_mult_rsuc in a_eq.
                rewrite plus_comm, <- (plus_assoc 2) in a_eq.
                apply plus_lcancel in a_eq.
                rewrite not_ex in a_even.
                specialize (a_even m).
                contradiction.
        }
        exists [_|a2_even].
        split; cbn.
        -   unfold le; cbn.
            rewrite <- (plus_rid a) at 1.
            apply le_lplus.
            apply nat0_le_zero.
        -   clear.
            intros eq.
            inversion eq as [eq2].
            (* TODO: Get plus_rr0 working here *)
            rewrite <- (plus_rid a) in eq2 at 1.
            apply plus_lcancel in eq2.
            inversion eq2.
    }
    assert (¬S1 0) as z_S1.
    {
        intros [m m_eq].
        rewrite plus_comm in m_eq.
        inversion m_eq.
    }
    assert (¬S2 0) as z_S2.
    {
        intros [m m_eq].
        rewrite plus_comm in m_eq.
        inversion m_eq.
    }
    assert (S1 1) as o_S1.
    {
        exists 0.
        rewrite mult_ranni, plus_lid.
        reflexivity.
    }
    assert (¬S2 1) as o_S2.
    {
        unfold complement, S2.
        intros [m m_eq].
        rewrite plus_comm in m_eq.
        inversion m_eq.
    }
    assert (open S2) as S2_open.
    {
        rewrite eq.
        left.
        apply all_greater_inf.
        1: exists 0; exact z_S2.
        intros [a a_odd].
        classic_case (0 = a) as [a_z|a_nz].
        {
            subst.
            exists [1|o_S2].
            split; cbn.
            -   unfold le; cbn.
                apply nat0_le_zero.
            -   intros contr; inversion contr.
        }
        unfold complement, S2 in a_odd.
        assert (complement S2 (a + 2)) as a2_odd.
        {
            intros [m a_eq].
            nat0_destruct m.
            -   rewrite mult_ranni, plus_lid in a_eq.
                rewrite plus_comm in a_eq.
                inversion a_eq as [a_eq2].
                symmetry in a_eq2; contradiction.
            -   rewrite nat0_mult_rsuc in a_eq.
                rewrite plus_comm, <- (plus_assoc 2) in a_eq.
                apply plus_lcancel in a_eq.
                rewrite not_ex in a_odd.
                specialize (a_odd m).
                contradiction.
        }
        exists [_|a2_odd].
        split; cbn.
        -   unfold le; cbn.
            rewrite <- (plus_rid a) at 1.
            apply le_lplus.
            apply nat0_le_zero.
        -   clear.
            intros eq.
            inversion eq as [eq2].
            (* TODO: Get plus_rr0 working here *)
            rewrite <- (plus_rid a) in eq2 at 1.
            apply plus_lcancel in eq2.
            inversion eq2.
    }
    pose proof (union_open2 _ _ S1_open S2_open) as S12_open.
    rewrite eq in S12_open.
    destruct S12_open as [S12_open|[S12_all|S12_empty]].
    2: {
        assert (all (zero (U := nat0))) as z_in by exact true.
        rewrite <- S12_all in z_in.
        destruct z_in; contradiction.
    }
    2: {
        assert ((S1 ∪ S2) 1) as contr by (left; exact o_S1).
        rewrite S12_empty in contr.
        contradiction contr.
    }
    assert (complement (S1 ∪ S2) = singleton 0) as S_eq.
    {
        unfold complement, union.
        apply antisym.
        2: {
            intros n n0.
            rewrite not_or.
            rewrite <- n0.
            split; assumption.
        }
        intros n n_not.
        unfold singleton; cbn.
        rewrite not_or in n_not.
        unfold S1, S2 in n_not.
        destruct n_not as [n_even n_odd].
        rewrite not_ex in n_even, n_odd.
        assert ((zero (U := nat0)) ≠ 2) as neq
            by (intros contr; inversion contr).
        pose proof (euclidean_division n 2 neq) as [q [r [n_eq r_lt]]].
        cbn in r_lt.
        nat0_destruct r.
        -   rewrite plus_rid in n_eq.
            nat0_destruct q.
            +   rewrite mult_ranni in n_eq.
                symmetry; exact n_eq.
            +   rewrite nat0_mult_rsuc in n_eq.
                rewrite plus_comm in n_eq.
                specialize (n_odd q).
                contradiction.
        -   nat0_destruct r.
            +   specialize (n_even q).
                contradiction.
            +   change (nat0_suc (nat0_suc r)) with (2 + r) in r_lt.
                rewrite <- (plus_rid 2) in r_lt at 2.
                apply lt_plus_lcancel in r_lt.
                apply nat0_lt_zero in r_lt.
                contradiction r_lt.
    }
    rewrite S_eq in S12_open.
    rewrite singleton_size in S12_open.
    pose proof (nat0_is_finite 1) as one_fin.
    pose proof (lt_le_trans one_fin S12_open) as contr.
    destruct contr; contradiction.
Qed.
