Require Import init.

(* TODO: Prove all of these using grading *)

Require Export linear_base.
Require Import linear_span.
Require Import linear_subspace.
Require Import unordered_list.
Require Import set.
Require Import zorn.
Require Import card.
Require Import plus_sum.

Definition linearly_independent {U V} `{Zero U}
    `{Zero V, VP : Plus V, @PlusComm V VP, @PlusAssoc V VP, ScalarMult U V}
    (S : V → Prop) :=
    ∀ l, linear_list_in S l →
    0 = linear_combination l → ulist_prop (λ x, 0 = fst x) [l|].
Definition linearly_dependent {U V} `{Zero U}
    `{Zero V, VP : Plus V, @PlusComm V VP, @PlusAssoc V VP, ScalarMult U V}
    (S : V → Prop) := ¬linearly_independent S.

Definition basis {U V} `{Zero U}
    `{Zero V, VP : Plus V, @PlusComm V VP, @PlusAssoc V VP, ScalarMult U V}
    (S : V → Prop) := linearly_independent S ∧ linear_span U S = all.

(* begin hide *)
Section Basis.

Context {U V} `{VectorSpace U V}.

(* end hide *)
Theorem empty_linearly_independent : linearly_independent ∅.
Proof.
    intros l l_in eq.
    destruct l as [l l_comb].
    destruct l using ulist_destruct.
    -   apply ulist_prop_end.
    -   exfalso.
        unfold linear_list_in in l_in; cbn in l_in.
        clear l_comb eq.
        rewrite ulist_prop_add in l_in.
        contradiction (land l_in).
Qed.

Theorem zero_linearly_dependent : ∀ (S : V → Prop), S 0 → linearly_dependent S.
Proof.
    intros S S0 ind.
    pose (l := (1, 0) ::: ulist_end).
    assert (linear_combination_set l) as l_comb.
    {
        unfold linear_combination_set, l.
        rewrite ulist_image_add, ulist_unique_add.
        rewrite ulist_image_end.
        split.
        -   apply in_ulist_end.
        -   apply ulist_unique_end.
    }
    pose proof (ind [l|l_comb]) as eq.
    prove_parts eq.
    -   unfold linear_list_in, l; cbn.
        rewrite ulist_prop_add; cbn.
        split.
        +   exact S0.
        +   apply ulist_prop_end.
    -   unfold linear_combination, l; cbn.
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid.
        rewrite scalar_ranni.
        reflexivity.
    -   unfold l in eq; cbn in eq.
        rewrite ulist_prop_add in eq; cbn in eq.
        apply not_trivial_one.
        apply eq.
Qed.

Theorem singleton_linearly_independent :
    ∀ v, 0 ≠ v → linearly_independent (singleton v).
Proof.
    intros v v_neq [l uni] in_l eq.

    destruct l using ulist_destruct.
    2: destruct l using ulist_destruct.
    -   apply ulist_prop_end.
    -   unfold linear_combination in eq; cbn in eq.
        rewrite ulist_image_add, ulist_sum_add in eq.
        rewrite ulist_image_end, ulist_sum_end in eq.
        rewrite plus_rid in eq.
        cbn; rewrite ulist_prop_add.
        split; [>|apply ulist_prop_end].
        unfold linear_list_in in in_l; cbn in in_l.
        rewrite ulist_prop_add in in_l.
        destruct in_l as [v_eq in_l]; clear in_l.
        unfold singleton in v_eq.
        subst v.
        classic_contradiction contr.
        apply lscalar with (/fst a) in eq.
        rewrite scalar_ranni in eq.
        rewrite scalar_comp in eq.
        rewrite mult_linv in eq by exact contr.
        rewrite scalar_id in eq.
        contradiction.
    -   exfalso.
        clear eq.
        unfold linear_list_in in in_l; cbn in in_l.
        unfold linear_combination_set in uni; cbn in uni.
        do 2 rewrite ulist_image_add, ulist_unique_add in uni.
        rewrite in_ulist_add in uni.
        rewrite not_or in uni.
        apply (land (land uni)).
        do 2 rewrite ulist_prop_add in in_l.
        unfold singleton in in_l.
        rewrite <- (land in_l), <- (land (rand in_l)).
        reflexivity.
Qed.

Theorem basis_linear_combination : ∀ S, basis S →
    ∀ v, linear_combination_of S v.
Proof.
    intros S S_basis v.
    rewrite <- (span_linear_combination U).
    destruct S_basis as [S_ind S_eq].
    rewrite S_eq.
    exact true.
Qed.

Definition basis_coefficients (S : V → Prop) (S_basis : basis S) (v : V)
    := linear_remove_zeros (ex_val (basis_linear_combination S S_basis v)).
Arguments basis_coefficients : simpl never.

Theorem basis_coefficients_combination : ∀ S S_basis v,
    v = linear_combination (basis_coefficients S S_basis v).
Proof.
    intros S S_basis v.
    unfold basis_coefficients.
    rewrite_ex_val l [v_eq Sl].
    rewrite <- linear_combination_remove_zeros.
    exact v_eq.
Qed.

Theorem basis_coefficients_in : ∀ S S_basis v,
    linear_list_in S (basis_coefficients S S_basis v).
Proof.
    intros S S_basis v.
    unfold basis_coefficients.
    rewrite_ex_val l [v_eq Sl].
    apply ulist_prop_filter.
    exact Sl.
Qed.

Lemma basis_unique2_wlog : ∀ S, linearly_independent S →
    ∀ v al bl, linear_list_in S al → linear_list_in S bl →
    v = linear_combination al → v = linear_combination bl →
    ∀ x, in_ulist [linear_remove_zeros al|] x →
         in_ulist [linear_remove_zeros bl|] x.
Proof.
    intros S S_ind v al bl Sal Sbl v_eq1 v_eq2 x al_x.
    remember (linear_remove_zeros al) as al'.
    remember (linear_remove_zeros bl) as bl'.
    assert (v = linear_combination al') as v_eq1'.
    {
        rewrite Heqal'.
        rewrite <- linear_combination_remove_zeros.
        exact v_eq1.
    }
    assert (v = linear_combination bl') as v_eq2'.
    {
        rewrite Heqbl'.
        rewrite <- linear_combination_remove_zeros.
        exact v_eq2.
    }
    clear v_eq1 v_eq2.
    assert (linear_list_in S al') as Sal'.
    {
        rewrite Heqal'.
        apply linear_list_in_remove_zeros.
        exact Sal.
    }
    assert (linear_list_in S bl') as Sbl'.
    {
        rewrite Heqbl'.
        apply linear_list_in_remove_zeros.
        exact Sbl.
    }
    assert (∀ x, in_ulist [al'|] x → 0 ≠ fst x) as al'_nz.
    {
        intros y y_in.
        rewrite Heqal' in y_in.
        cbn in y_in.
        unfold linear_remove_zeros_base in y_in.
        apply (ulist_filter_in_S _ [al|] _ y_in).
    }
    assert (∀ x, in_ulist [bl'|] x → 0 ≠ fst x) as bl'_nz.
    {
        intros y y_in.
        rewrite Heqbl' in y_in.
        cbn in y_in.
        unfold linear_remove_zeros_base in y_in.
        apply (ulist_filter_in_S _ [bl|] _ y_in).
    }
    clear Sal Sbl al bl Heqal' Heqbl'.
    destruct al' as [al' al'_comb].
    destruct bl' as [bl' bl'_comb].
    change [[al'|al'_comb]|] with al' in *.
    change [[bl'|bl'_comb]|] with bl' in *.
    classic_contradiction bl_x.
    assert (∃ a l,
            0 ≠ a ∧ linear_list_in (S - singleton (snd x))%set l ∧
            0 = a · snd x + linear_combination l) as [a [l [a_nz [l_in eq]]]].
    {
        apply in_ulist_split in al_x as [al al_eq].
        subst al'.
        rename al into al'.
        assert (linear_combination_set al') as al_comb'.
        {
            clear v_eq1' Sal'.
            unfold linear_combination_set in al'_comb.
            rewrite ulist_image_add, ulist_unique_add in al'_comb.
            apply al'_comb.
        }
        assert (linear_list_in (S - singleton (snd x))%set [al'|al_comb'])
            as Sxal'.
        {
            unfold linear_list_in in Sal'; cbn in Sal'.
            rewrite ulist_prop_add in Sal'.
            apply ulist_prop_split; cbn.
            intros a l al_eq.
            subst al'.
            split.
            -   rewrite ulist_prop_add in Sal'.
                apply Sal'.
            -   unfold singleton.
                clear - al'_comb.
                unfold linear_combination_set in al'_comb.
                do 2 rewrite ulist_image_add, ulist_unique_add in al'_comb.
                rewrite in_ulist_add in al'_comb.
                rewrite not_or in al'_comb.
                rewrite neq_sym.
                apply al'_comb.
        }
        classic_case (∃ a, in_ulist bl' (a, snd x)).
        -   destruct e as [a bl_ax].
            exists (fst x - a).
            apply in_ulist_split in bl_ax as [bl bl_eq].
            subst bl'.
            rename bl into bl'.
            assert (linear_combination_set bl') as bl_comb'.
            {
                clear - bl'_comb.
                unfold linear_combination_set in bl'_comb.
                rewrite ulist_image_add, ulist_unique_add in bl'_comb.
                apply bl'_comb.
            }
            assert (linear_list_in (S - singleton (snd x))%set [bl'|bl_comb'])
                as Sxbl'.
            {
                apply ulist_prop_split; cbn.
                intros b l bl_eq.
                subst bl'.
                split.
                -   unfold linear_list_in in Sbl'; cbn in Sbl'.
                    rewrite ulist_swap in Sbl'.
                    rewrite ulist_prop_add in Sbl'.
                    apply Sbl'.
                -   unfold singleton.
                    clear - bl'_comb.
                    unfold linear_combination_set in bl'_comb.
                    do 2 rewrite ulist_image_add, ulist_unique_add in bl'_comb.
                    rewrite in_ulist_add in bl'_comb.
                    rewrite not_or in bl'_comb.
                    rewrite neq_sym.
                    apply bl'_comb.
            }
            apply (f_equal neg) in v_eq2'.
            pose proof (lrplus v_eq1' v_eq2') as v_eq.
            rewrite plus_rinv in v_eq.
            rewrite (linear_combination_add _ _ _ al_comb') in v_eq.
            rewrite (linear_combination_add _ _ _ bl_comb') in v_eq.
            cbn in v_eq.
            rewrite neg_plus in v_eq.
            rewrite plus_assoc in v_eq.
            rewrite <- (plus_assoc (fst x · snd x)) in v_eq.
            rewrite (plus_comm _ (-(a · snd x))) in v_eq.
            rewrite plus_assoc in v_eq.
            rewrite <- scalar_lneg in v_eq.
            rewrite <- scalar_rdist in v_eq.
            assert (linear_combination_of (S - singleton (snd x))%set
                (linear_combination [al' | al_comb'] -
                 linear_combination [bl' | bl_comb'])) as eq.
            {
                apply linear_combination_of_plus.
                -   exists [al'|al_comb'].
                    split.
                    +   reflexivity.
                    +   exact Sxal'.
                -   rewrite <- scalar_neg_one.
                    apply linear_combination_of_scalar.
                    exists [bl'|bl_comb'].
                    split.
                    +   reflexivity.
                    +   exact Sxbl'.
            }
            destruct eq as [l [l_eq l_in]].
            exists l.
            split.
            2: split.
            +   intros contr.
                rewrite plus_0_anb_a_b in contr.
                subst a.
                apply bl_x.
                rewrite in_ulist_add.
                left.
                destruct x; reflexivity.
            +   exact l_in.
            +   rewrite <- plus_assoc in v_eq.
                rewrite l_eq in v_eq.
                exact v_eq.
        -   exists (fst x).
            assert (linear_list_in (S - singleton (snd x))%set [bl'|bl'_comb])
                as Sxbl'.
            {
                apply ulist_prop_split; cbn.
                intros a l bl_eq.
                subst bl'.
                split.
                -   unfold linear_list_in in Sbl'; cbn in Sbl'.
                    rewrite ulist_prop_add in Sbl'.
                    apply Sbl'.
                -   unfold singleton.
                    rewrite not_ex in n.
                    specialize (n (fst a)).
                    rewrite in_ulist_add in n.
                    rewrite not_or in n.
                    destruct n as [neq x_nin].
                    intros contr.
                    rewrite contr in neq.
                    apply neq.
                    destruct a; reflexivity.
            }
            apply (f_equal neg) in v_eq2'.
            pose proof (lrplus v_eq1' v_eq2') as v_eq.
            rewrite plus_rinv in v_eq.
            rewrite (linear_combination_add _ _ _ al_comb') in v_eq.
            assert (linear_combination_of (S - singleton (snd x))%set
                (linear_combination [al' | al_comb'] -
                 linear_combination [bl' | bl'_comb])) as eq.
            {
                apply linear_combination_of_plus.
                -   exists [al'|al_comb'].
                    split.
                    +   reflexivity.
                    +   exact Sxal'.
                -   rewrite <- scalar_neg_one.
                    apply linear_combination_of_scalar.
                    exists [bl'|bl'_comb].
                    split.
                    +   reflexivity.
                    +   exact Sxbl'.
            }
            destruct eq as [l [l_eq l_in]].
            exists l.
            split.
            2: split.
            +   intros contr.
                apply (al'_nz x).
                *   rewrite in_ulist_add.
                    left.
                    reflexivity.
                *   exact contr.
            +   exact l_in.
            +   rewrite <- plus_assoc in v_eq.
                rewrite l_eq in v_eq.
                exact v_eq.
    }
    pose (l' := (a, snd x) ::: [l|]).
    assert (linear_combination_set l') as l'_comb.
    {
        unfold linear_combination_set, l'.
        rewrite ulist_image_add, ulist_unique_add; cbn.
        split.
        -   intros contr.
            unfold linear_list_in in l_in.
            apply image_in_ulist in contr as [x' [x_eq x'_in]].
            apply in_ulist_split in x'_in as [l'' l_eq].
            rewrite l_eq in l_in.
            clear - l_in x_eq.
            rename l'' into l.
            rewrite ulist_prop_add in l_in.
            apply (rand (land l_in)).
            rewrite x_eq.
            reflexivity.
        -   apply [|l].
    }
    apply a_nz.
    pose proof (S_ind [l'|l'_comb]) as a_z.
    prove_parts a_z.
    -   unfold linear_list_in, l'; cbn.
        rewrite ulist_prop_add; cbn.
        split.
        +   apply in_ulist_split in al_x as [al al_eq].
            subst al'.
            unfold linear_list_in in Sal'; cbn in Sal'.
            rewrite ulist_prop_add in Sal'.
            exact (land Sal').
        +   eapply (ulist_prop_sub _ _ _ _ l_in).
            Unshelve.
            intros y [Sy yx].
            exact Sy.
    -   unfold linear_combination, l'; cbn.
        rewrite ulist_image_add, ulist_sum_add; cbn.
        exact eq.
    -   unfold l' in a_z; cbn in a_z.
        rewrite ulist_prop_add in a_z.
        apply a_z.
Qed.

Theorem basis_unique2 : ∀ S, linearly_independent S →
    ∀ v al bl, linear_list_in S al → linear_list_in S bl →
    v = linear_combination al → v = linear_combination bl →
    [linear_remove_zeros al|] = [linear_remove_zeros bl|].
Proof.
    intros S S_ind v al bl Sal Sbl v_eq1 v_eq2.
    apply ulist_in_unique_eq.
    1: {
        clear.
        destruct al as [al al_comb].
        unfold linear_remove_zeros, linear_remove_zeros_base; cbn.
        apply ulist_image_unique in al_comb.
        apply ulist_filter_unique.
        exact al_comb.
    }
    1: {
        clear.
        destruct bl as [bl bl_comb].
        unfold linear_remove_zeros, linear_remove_zeros_base; cbn.
        apply ulist_image_unique in bl_comb.
        apply ulist_filter_unique.
        exact bl_comb.
    }
    intros x; split; apply (basis_unique2_wlog S S_ind v); assumption.
Qed.

Theorem basis_unique : ∀ S S_basis v,
    ∀ l, linear_list_in S l → v = linear_combination l →
    [linear_remove_zeros l|] = [basis_coefficients S S_basis v|].
Proof.
    intros S S_basis v l Sl v_eq1.
    pose proof (basis_coefficients_combination S S_basis v) as v_eq2.
    pose proof (basis_coefficients_in S S_basis v) as Sv.
    pose proof (basis_unique2 S (land S_basis) v _ _ Sl Sv v_eq1 v_eq2) as eq.
    clear - eq.
    unfold basis_coefficients in *.
    unfold linear_remove_zeros, linear_remove_zeros_base in *.
    cbn in *.
    rewrite <- ulist_filter_filter in eq.
    exact eq.
Qed.

Theorem basis_single : 0 ≠ 1 → ∀ (S : V → Prop) S_basis v, S v →
    [basis_coefficients S S_basis v|] = (1, v) ::: ulist_end.
Proof.
    intros not_trivial2 S S_basis v Sv.
    pose (l := (1, v) ::: ulist_end).
    assert (linear_combination_set l) as l_comb.
    {
        unfold linear_combination_set, l.
        rewrite ulist_image_add, ulist_unique_add.
        rewrite ulist_image_end.
        split.
        -   apply in_ulist_end.
        -   apply ulist_unique_end.
    }
    assert (linear_list_in S [l|l_comb]) as l_in.
    {
        unfold linear_list_in, l; cbn.
        rewrite ulist_prop_add; cbn.
        split.
        -   exact Sv.
        -   apply ulist_prop_end.
    }
    assert (v = linear_combination [l|l_comb]) as v_eq.
    {
        unfold linear_combination, l; cbn.
        rewrite ulist_image_add, ulist_sum_add.
        rewrite ulist_image_end, ulist_sum_end; cbn.
        rewrite scalar_id.
        rewrite plus_rid.
        reflexivity.
    }
    pose proof (basis_unique S S_basis v [l|l_comb] l_in v_eq) as v_eq'.
    cbn in v_eq'.
    clear v_eq.
    rewrite <- v_eq'.
    unfold linear_remove_zeros_base, l; cbn.
    classic_case (0 ≠ 1) as [o_nz|o_z].
    -   rewrite ulist_filter_add_in by apply o_nz.
        rewrite ulist_filter_end.
        reflexivity.
    -   contradiction.
Qed.

Theorem basis_coefficients_S_ex : ∀ S S_basis v, ∃ l : ulist (U * set_type S),
    [basis_coefficients S S_basis v|] =
    ulist_image l (λ x, (fst x, [snd x|])).
Proof.
    intros S S_basis v.
    remember (basis_coefficients S S_basis v) as l.
    destruct l as [l l_comb]; cbn.
    pose proof (basis_coefficients_in S S_basis v) as l_in.
    rewrite <- Heql in l_in.
    unfold linear_list_in in l_in; cbn in l_in.
    clear l_comb Heql.
    induction l using ulist_induction; intros.
    -   exists ulist_end.
        rewrite ulist_image_end.
        reflexivity.
    -   destruct a as [a u]; cbn in *.
        rewrite ulist_prop_add in l_in; cbn in l_in.
        specialize (IHl (rand l_in)) as [l' l'_eq].
        exists ((a, [u|land l_in]) ::: l').
        subst l.
        rewrite ulist_image_add; cbn.
        reflexivity.
Qed.

Theorem basis_coefficients_zero : ∀ S S_basis,
    [basis_coefficients S S_basis 0|] = ulist_end.
Proof.
    intros S S_basis.
    assert (linear_combination_set (U := U) (V := V) ulist_end) as end_in.
    {
        unfold linear_combination_set; cbn.
        rewrite ulist_image_end.
        apply ulist_unique_end.
    }
    assert (linear_list_in (U := U) S [ulist_end|end_in]) as l_in.
    {
        unfold linear_list_in; cbn.
        apply ulist_prop_end.
    }
    assert (0 = linear_combination [ulist_end|end_in]) as v_eq.
    {
        unfold linear_combination; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    }
    pose proof (basis_unique S S_basis 0 [ulist_end|end_in] l_in v_eq) as v_eq'.
    rewrite <- v_eq'.
    unfold linear_remove_zeros, linear_remove_zeros_base; cbn.
    apply ulist_filter_end.
Qed.

Local Instance subset_order : Order (V → Prop) := {
    le A B := A ⊆ B
}.
(* begin hide *)
Local Open Scope card_scope.

(* end hide *)
Theorem basis_extend_ex : ∀ S, linearly_independent S → ∃ B, S ⊆ B ∧ basis B.
Proof.
    intros S S_ind.
    pose (SS T := S ⊆ T ∧ linearly_independent T).
    assert (SS S) as SS_S.
    {
        split.
        -   apply refl.
        -   exact S_ind.
    }
    assert (∀ F : (set_type SS) → Prop, is_chain le F → has_upper_bound le F)
        as zorn_piece.
    {
        intros F F_chain.
        classic_case (F = ∅) as [F_empty|F_nempty].
        {
            subst F.
            exists [S|SS_S].
            intros T T_empty.
            contradiction T_empty.
        }
        apply empty_neq in F_nempty as [A F_A].
        pose (M x := ∃ T, F T ∧ [T|] x).
        assert (SS M) as SS_M.
        {
            split.
            -   intros x Sx.
                exists A.
                split.
                +   exact F_A.
                +   apply [|A].
                    exact Sx.
            -   intros l Ml l_eq.
                assert (∃ T, F T ∧ linear_list_in [T|] l) as [T [FT Tl]].
                {
                    clear l_eq.
                    destruct l as [l l_comb].
                    induction l using ulist_induction; intros.
                    -   exists A.
                        split; [>exact F_A|].
                        unfold linear_list_in; cbn.
                        apply ulist_prop_end.
                    -   assert (linear_combination_set l) as l_comb'.
                        {
                            unfold linear_combination_set in *.
                            clear Ml.
                            rewrite ulist_image_add, ulist_unique_add in l_comb.
                            apply l_comb.
                        }
                        assert (linear_list_in M [l|l_comb']) as Ml'.
                        {
                            unfold linear_list_in in *.
                            cbn in Ml; rewrite ulist_prop_add in Ml.
                            apply Ml.
                        }
                        specialize (IHl l_comb' Ml') as [T [FT T_in]].
                        assert (M (snd a)) as Ma.
                        {
                            unfold linear_list_in in Ml; cbn in Ml.
                            rewrite ulist_prop_add in Ml.
                            apply Ml.
                        }
                        destruct Ma as [T2 [FT2 T2a]].
                        specialize (F_chain T T2 FT FT2) as [leq|leq].
                        +   exists T2.
                            split; [>exact FT2|].
                            unfold linear_list_in; cbn.
                            rewrite ulist_prop_add.
                            split; [>exact T2a|].
                            eapply (ulist_prop_sub _ _ _ _ T_in).
                            Unshelve.
                            intros x.
                            apply leq.
                        +   exists T.
                            split; [>exact FT|].
                            unfold linear_list_in; cbn.
                            rewrite ulist_prop_add.
                            split; [>|exact T_in].
                            apply leq.
                            exact T2a.
                }
                destruct T as [T [T_sub T_ind]].
                apply (T_ind l Tl l_eq).
        }
        exists [M|SS_M].
        intros [T SS_T] F_T.
        unfold le; cbn.
        intros x Tx.
        exists [T|SS_T].
        split; assumption.
    }
    pose proof (zorn le zorn_piece) as [[B [B_sub B_ind]] B_max].
    clear zorn_piece.
    exists B.
    repeat split; try assumption.
    apply antisym.
    1: intros x x_in; exact true.
    intros v v_in; clear v_in.
    rewrite (span_linear_combination U B).
    classic_case (0 = v) as [v_z|v_nz].
    {
        subst v.
        apply linear_combination_of_zero.
    }
    classic_contradiction contr.
    pose (B' := B ∪ singleton v).
    assert (SS B') as SS_B'.
    {
        split.
        -   apply (trans B_sub).
            intros x Bx.
            left.
            exact Bx.
        -   intros [l l_comb] B'l l_eq.
            classic_case (∃ a, in_ulist l (a, v)) as [v_in|v_nin].
            +   destruct v_in as [a v_in].
                apply in_ulist_split in v_in as [l' l'_eq].
                subst l.
                assert (linear_combination_set l') as l'_comb.
                {
                    unfold linear_combination_set in *.
                    clear l_eq B'l.
                    rewrite ulist_image_add, ulist_unique_add in l_comb.
                    apply l_comb.
                }
                assert (linear_list_in B [l'|l'_comb]) as Bl'.
                {
                    unfold linear_list_in in *; cbn in *.
                    rewrite ulist_prop_add in B'l; cbn in B'l.
                    destruct B'l as [B'v B'l].
                    clear l'_comb l_eq.
                    induction l' using ulist_induction.
                    -   apply ulist_prop_end.
                    -   rewrite ulist_prop_add.
                        rewrite ulist_prop_add in B'l.
                        destruct B'l as [B'a0 B'l].
                        split.
                        +   destruct B'a0 as [Ba0|va0].
                            *   exact Ba0.
                            *   unfold singleton in va0.
                                subst v.
                                unfold linear_combination_set in l_comb.
                                do 2 rewrite ulist_image_add, ulist_unique_add
                                    in l_comb; cbn in l_comb.
                                rewrite in_ulist_add in l_comb.
                                rewrite not_or in l_comb.
                                contradiction (land (land l_comb)).
                                reflexivity.
                        +   apply IHl'.
                            *   rewrite ulist_swap in l_comb.
                                unfold linear_combination_set in l_comb.
                                rewrite ulist_image_add, ulist_unique_add
                                    in l_comb.
                                apply l_comb.
                            *   exact B'l.
                }
                classic_case (0 = a) as [a_z|a_nz].
                *   subst a.
                    rewrite (linear_combination_add _ _ _ l'_comb) in l_eq.
                    cbn in l_eq.
                    rewrite scalar_lanni, plus_lid in l_eq.
                    cbn; rewrite ulist_prop_add.
                    split; [>reflexivity|].
                    apply (B_ind [l'|l'_comb] Bl' l_eq).
                *   exfalso; apply contr.
                    clear S S_ind SS SS_S B_sub B_ind B_max v_nz contr B'
                          B'l.
                    rewrite (linear_combination_add _ _ _ l'_comb) in l_eq.
                    cbn in l_eq.
                    rewrite <- scalar_id.
                    rewrite <- (mult_linv a a_nz).
                    rewrite <- scalar_comp.
                    apply linear_combination_of_scalar.
                    rewrite <- neg_neg.
                    rewrite <- scalar_neg_one.
                    apply linear_combination_of_scalar.
                    exists [l' | l'_comb].
                    split.
                    2: exact Bl'.
                    rewrite <- plus_0_ab_na_b.
                    exact l_eq.
            +   assert (linear_list_in B [l | l_comb]) as Bl.
                {
                    unfold linear_list_in in *; cbn in *.
                    clear l_eq l_comb.
                    induction l using ulist_induction.
                    -   apply ulist_prop_end.
                    -   rewrite ulist_prop_add.
                        rewrite ulist_prop_add in B'l.
                        destruct B'l as [B'a B'l].
                        split.
                        +   destruct B'a as [Ba|av]; [>exact Ba|].
                            unfold singleton in av.
                            subst v.
                            exfalso; apply v_nin.
                            exists (fst a).
                            rewrite in_ulist_add.
                            left; destruct a; reflexivity.
                        +   apply IHl.
                            *   exact B'l.
                            *   intros [b v_in].
                                apply v_nin.
                                exists b.
                                rewrite in_ulist_add.
                                right; exact v_in.
                }
                apply (B_ind [l|l_comb] Bl l_eq).
    }
    apply (B_max [B'|SS_B']).
    split.
    -   unfold le; cbn.
        unfold le; cbn.
        apply union_lsub.
    -   intros contr2.
        apply set_type_eq in contr2; cbn in contr2.
        subst B'.
        apply contr.
        pose (l := (1, v) ::: ulist_end).
        assert (linear_combination_set l) as l_comb.
        {
            unfold l, linear_combination_set.
            rewrite ulist_image_add, ulist_unique_add.
            rewrite ulist_image_end.
            split.
            -   apply in_ulist_end.
            -   apply ulist_unique_end.
        }
        exists [l|l_comb].
        split.
        +   unfold l, linear_combination; cbn.
            rewrite ulist_image_add, ulist_sum_add; cbn.
            rewrite ulist_image_end, ulist_sum_end.
            rewrite scalar_id, plus_rid.
            reflexivity.
        +   unfold linear_list_in, l; cbn.
            rewrite ulist_prop_add; cbn.
            split; [>|apply ulist_prop_end].
            rewrite contr2.
            right.
            reflexivity.
Qed.

Theorem basis_ex : ∃ B, basis B.
Proof.
    pose proof (basis_extend_ex ∅ empty_linearly_independent)
        as [B [B_sub B_basis]].
    exists B.
    exact B_basis.
Qed.
(* begin hide *)

End Basis.
(* end hide *)
