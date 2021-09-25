Require Import init.

Require Export linear_base.
Require Import linear_span.
Require Import linear_subspace.
Require Import list.
Require Import set.
Require Import plus_sum.

Definition linearly_independent {U V} `{Zero U, Zero V, Plus V, ScalarMult U V}
    (S : V → Prop) :=
    ∀ l, linear_list_in S l →
    0 = linear_combination l → (∀ α, (∃ v, in_list [l|] (α, v)) → 0 = α).
Definition linearly_dependent {U V} `{Zero U, Zero V, Plus V, ScalarMult U V}
    (S : V → Prop) := ¬linearly_independent S.

Definition basis {U V} `{Zero U, Zero V, Plus V, Neg V, ScalarMult U V}
    (S : V → Prop) := linearly_independent S ∧ linear_span U S = all.

Section Basis.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    UD : Div U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    @MultAssoc U UM,
    @MultLid U UM UO,
    @MultLinv U UZ UM UO UD,
    @NotTrivial U UZ UO,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarComp U V UM SM,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM
}.

Theorem zero_linearly_dependent : ∀ (S : V → Prop), S 0 → linearly_dependent S.
    intros S S0 ind.
    pose (l := (1, 0) :: list_end).
    assert (linear_combination_set l) as l_comb.
    {
        cbn.
        rewrite not_false.
        split; exact true.
    }
    apply not_trivial.
    apply (ind [l|l_comb]).
    -   intros v [α v_in].
        cbn in v_in.
        destruct v_in as [v_in|v_in]; try contradiction.
        inversion v_in.
        exact S0.
    -   cbn.
        rewrite plus_rid.
        rewrite scalar_ranni.
        reflexivity.
    -   cbn.
        exists 0.
        left.
        reflexivity.
Qed.

Theorem singleton_linearly_independent :
        ∀ v, 0 ≠ v → linearly_independent (singleton v).
    intros v v_neq [l uni] in_l eq α α_in.
    classic_contradiction α_nz.
    assert (l = (1, v) :: list_end) as l_eq.
    {
        destruct l.
        -   cbn in *.
            destruct α_in; contradiction.
        -   cbn in *.
            destruct uni as [uni1 uni2].
            assert (p = (1, v)) as p_eq.
            {
                destruct p as [β v0]; cbn in *.
                assert (v0 = v) as eq'.
                {
                    symmetry; apply in_l.
                    exists β.
                    left; reflexivity.
                }
                subst v0.
                apply f_equal2.
                2: reflexivity.
                destruct l.
                -   cbn in *.
                    destruct α_in as [u α_in].
                    destruct α_in as [α_eq|α_in].
                    2: contradiction.
                    inversion α_eq.
                    subst β u.
                    rewrite plus_rid in eq.
                    apply lscalar with (/α) in eq.
                    rewrite scalar_ranni in eq.
                    rewrite scalar_comp in eq.
                    rewrite mult_linv in eq by exact α_nz.
                    rewrite scalar_id in eq.
                    contradiction.
                -   clear - uni1 in_l.
                    destruct p as [α v0]; cbn in *.
                    assert (v0 = v) as eq.
                    {
                        symmetry; apply in_l.
                        exists α.
                        right; left.
                        reflexivity.
                    }
                    subst v0.
                    unfold linear_list_in in in_l; cbn in in_l.
                    rewrite not_or in uni1.
                    contradiction (land uni1).
                    reflexivity.
            }
            subst p.
            apply f_equal2.
            1: reflexivity.
            destruct l.
            1: reflexivity.
            cbn in *.
            destruct uni2 as [uni2 uni3].
            unfold linear_list_in in in_l; cbn in in_l.
            rewrite not_or in uni1.
            exfalso; apply (land uni1).
            symmetry; apply in_l.
            exists (fst p).
            right; left.
            destruct p; reflexivity.
    }
    subst l.
    cbn in *.
    rewrite plus_rid in eq.
    rewrite scalar_id in eq.
    contradiction.
Qed.

Theorem basis_linear_combination : ∀ S, basis S →
        ∀ v, linear_combination_of S v.
    intros S S_basis v.
    rewrite <- (span_linear_combination U).
    destruct S_basis as [S_ind S_eq].
    rewrite S_eq.
    exact true.
Qed.

Definition basis_coefficients (S : V → Prop) (S_basis : basis S) (v : V)
    := linear_remove_zeros (ex_val (basis_linear_combination S S_basis v)).

Theorem basis_coefficients_combination : ∀ S S_basis v,
        v = linear_combination (basis_coefficients S S_basis v).
    intros S S_basis v.
    unfold basis_coefficients.
    rewrite_ex_val l [v_eq Sl].
    rewrite <- linear_combination_remove_zeros.
    exact v_eq.
Qed.

Theorem basis_coefficients_in : ∀ S S_basis v,
        linear_list_in S (basis_coefficients S S_basis v).
    intros S S_basis v.
    unfold basis_coefficients.
    rewrite_ex_val l [v_eq Sl].
    unfold linear_list_in.
    intros u [a u_in].
    apply list_filter_in in u_in.
    apply Sl.
    exists a.
    exact u_in.
Qed.

Lemma basis_unique2_wlog : ∀ S, linearly_independent S →
        ∀ v al bl, linear_list_in S al → linear_list_in S bl →
        v = linear_combination al → v = linear_combination bl →
        ∀ x, in_list [linear_remove_zeros al|] x →
             in_list [linear_remove_zeros bl|] x.
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
    assert (∀ x, in_list [al'|] x → 0 ≠ fst x) as al'_nz.
    {
        intros y y_in.
        rewrite Heqal' in y_in.
        cbn in y_in.
        unfold linear_remove_zeros_base in y_in.
        apply (list_filter_in_S _ [al|] _ y_in).
    }
    assert (∀ x, in_list [bl'|] x → 0 ≠ fst x) as bl'_nz.
    {
        intros y y_in.
        rewrite Heqbl' in y_in.
        cbn in y_in.
        unfold linear_remove_zeros_base in y_in.
        apply (list_filter_in_S _ [bl|] _ y_in).
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
        pose proof (in_list_split al' x al_x) as [al1 [al2 al_eq]].
        pose (al := x :: al1 ++ al2).
        assert (list_permutation al' al) as al_perm.
        {
            rewrite al_eq; unfold al.
            apply (list_perm_trans (list_perm_conc _ _)).
            cbn.
            apply list_perm_skip.
            apply list_perm_conc.
        }
        assert (linear_combination_set al) as al_comb.
        {
            unfold linear_combination_set.
            apply (list_image_perm snd) in al_perm.
            apply (list_perm_unique al_perm).
            exact al'_comb.
        }
        assert (v = linear_combination [al | al_comb]) as v_eq1.
        {
            rewrite v_eq1'.
            apply list_sum_perm.
            apply list_image_perm.
            exact al_perm.
        }
        assert (linear_list_in S [al | al_comb]) as Sal.
        {
            intros u [α u_in].
            apply Sal'.
            exists α.
            apply (list_perm_in al_perm).
            exact u_in.
        }
        assert (∀ x, in_list al x → 0 ≠ fst x) as al_nz.
        {
            intros y y_in.
            apply al'_nz.
            apply (list_perm_in al_perm).
            exact y_in.
        }
        clear al'_comb v_eq1' Sal' al' al_x al'_nz al_eq al_perm.
        remember (al1 ++ al2) as al'.
        clear Heqal' al1 al2.
        unfold al in *; clear al.
        assert (linear_combination_set al') as al'_comb by apply al_comb.
        assert (linear_list_in (S - singleton (snd x))%set [al'|al'_comb])
            as Sxal'.
        {
            intros u [b u_in].
            split.
            -   apply Sal.
                exists b.
                right.
                exact u_in.
            -   unfold singleton.
                intro contr; subst u.
                apply al_comb.
                exact (in_list_image _ _ snd u_in).
        }
        classic_case (∃ a, in_list bl' (a, snd x)).
        -   destruct e as [a bl_ax].
            exists (fst x - a).
            pose proof (in_list_split _ _ bl_ax) as [bl1 [bl2 bl_eq]].
            pose (bl := (a, snd x) :: bl1 ++ bl2).
            assert (list_permutation bl' bl) as bl_perm.
            {
                rewrite bl_eq; unfold bl.
                apply (list_perm_trans (list_perm_conc _ _)).
                cbn.
                apply list_perm_skip.
                apply list_perm_conc.
            }
            assert (linear_combination_set bl) as bl_comb.
            {
                unfold linear_combination_set.
                apply (list_image_perm snd) in bl_perm.
                apply (list_perm_unique bl_perm).
                exact bl'_comb.
            }
            assert (v = linear_combination [bl | bl_comb]) as v_eq2.
            {
                rewrite v_eq2'.
                apply list_sum_perm.
                apply list_image_perm.
                exact bl_perm.
            }
            assert (linear_list_in S [bl | bl_comb]) as Sbl.
            {
                intros u [α u_in].
                apply Sbl'.
                exists α.
                apply (list_perm_in bl_perm).
                exact u_in.
            }
            assert (∀ x, in_list bl x → 0 ≠ fst x) as bl_nz.
            {
                intros y y_in.
                apply bl'_nz.
                apply (list_perm_in bl_perm).
                exact y_in.
            }
            clear bl'_comb v_eq2' Sbl' bl'_nz bl_eq bl_perm.
            rename bl' into bl''.
            remember (bl1 ++ bl2) as bl'.
            clear Heqbl' bl1 bl2.
            unfold bl in *; clear bl.
            assert (linear_combination_set bl') as bl'_comb by apply bl_comb.
            assert (linear_list_in (S - singleton (snd x))%set [bl'|bl'_comb])
                as Sxbl'.
            {
                intros u [b u_in].
                split.
                -   apply Sbl.
                    exists b.
                    right.
                    exact u_in.
                -   unfold singleton.
                    intro contr; subst u.
                    apply bl_comb.
                    exact (in_list_image _ _ snd u_in).
            }
            apply (f_equal neg) in v_eq2.
            pose proof (lrplus v_eq1 v_eq2) as v_eq.
            rewrite plus_rinv in v_eq.
            rewrite (linear_combination_add _ _ _ al'_comb) in v_eq.
            rewrite (linear_combination_add _ _ _ bl'_comb) in v_eq.
            change (fst (a, snd x) · snd (a, snd x)) with (a · snd x) in v_eq.
            rewrite neg_plus in v_eq.
            rewrite plus_assoc in v_eq.
            rewrite <- (plus_assoc (fst x · snd x)) in v_eq.
            rewrite (plus_comm _ (-(a · snd x))) in v_eq.
            rewrite plus_assoc in v_eq.
            rewrite <- scalar_lneg in v_eq.
            rewrite <- scalar_rdist in v_eq.
            assert (linear_combination_of (S - singleton (snd x))%set
                (linear_combination [al' | al'_comb] -
                 linear_combination [bl' | bl'_comb])) as eq.
            {
                apply linear_combination_of_plus.
                -   exists [al'|al'_comb].
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
                rewrite plus_0_anb_a_b in contr.
                subst a.
                apply bl_x.
                destruct x; exact bl_ax.
            +   exact l_in.
            +   rewrite <- plus_assoc in v_eq.
                rewrite l_eq in v_eq.
                exact v_eq.
        -   exists (fst x).
            assert (linear_list_in (S - singleton (snd x))%set [bl'|bl'_comb])
                as Sxbl'.
            {
                intros u [b u_in].
                split.
                -   apply Sbl'.
                    exists b.
                    exact u_in.
                -   unfold singleton.
                    intro contr; subst u.
                    apply n.
                    exists b.
                    exact u_in.
            }
            apply (f_equal neg) in v_eq2'.
            pose proof (lrplus v_eq1 v_eq2') as v_eq.
            rewrite plus_rinv in v_eq.
            rewrite (linear_combination_add _ _ _ al'_comb) in v_eq.
            assert (linear_combination_of (S - singleton (snd x))%set
                (linear_combination [al' | al'_comb] -
                 linear_combination [bl' | bl'_comb])) as eq.
            {
                apply linear_combination_of_plus.
                -   exists [al'|al'_comb].
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
                apply (al_nz x).
                *   left.
                    reflexivity.
                *   exact contr.
            +   exact l_in.
            +   rewrite <- plus_assoc in v_eq.
                rewrite l_eq in v_eq.
                exact v_eq.
    }
    pose (l' := (a, snd x) :: [l|]).
    assert (linear_combination_set l') as l'_comb.
    {
        cbn.
        split.
        -   intros contr.
            unfold linear_list_in in l_in.
            assert ((S - singleton (snd x))%set (snd x)) as contr2.
            {
                apply l_in.
                destruct l as [l l_comb]; cbn in *.
                clear - contr.
                induction l.
                -   contradiction contr.
                -   cbn in contr.
                    destruct contr as [eq|contr].
                    +   rewrite <- eq.
                        exists (fst a).
                        left.
                        destruct a; reflexivity.
                    +   specialize (IHl contr) as [α IHl].
                        exists α.
                        right.
                        exact IHl.
            }
            destruct contr2 as [Sx contr2].
            apply contr2.
            reflexivity.
        -   apply [|l].
    }
    apply a_nz.
    apply (S_ind [l'|l'_comb]).
    -   intros u [b u_in].
        cbn in u_in.
        destruct u_in as [u_eq|u_in].
        +   inversion u_eq; subst u b.
            apply Sal'.
            exists (fst x).
            destruct x; exact al_x.
        +   unfold linear_list_in in l_in.
            apply l_in.
            exists b.
            exact u_in.
    -   cbn.
        exact eq.
    -   exists (snd x).
        cbn.
        left.
        reflexivity.
Qed.

Theorem basis_unique2 : ∀ S, linearly_independent S →
        ∀ v al bl, linear_list_in S al → linear_list_in S bl →
        v = linear_combination al → v = linear_combination bl →
        list_permutation [linear_remove_zeros al|] [linear_remove_zeros bl|].
    intros S S_ind v al bl Sal Sbl v_eq1 v_eq2.
    apply list_in_unique_perm.
    1: {
        clear.
        destruct al as [al al_comb].
        cbn.
        apply list_image_unique in al_comb.
        apply list_filter_unique.
        exact al_comb.
    }
    1: {
        clear.
        destruct bl as [bl bl_comb].
        cbn.
        apply list_image_unique in bl_comb.
        apply list_filter_unique.
        exact bl_comb.
    }
    intros x; split; apply (basis_unique2_wlog S S_ind v); assumption.
Qed.

Theorem basis_unique : ∀ S S_basis v,
        ∀ l, linear_list_in S l → v = linear_combination l →
        list_permutation [linear_remove_zeros l|]
                         [basis_coefficients S S_basis v|].
    intros S S_basis v l Sl v_eq1.
    pose proof (basis_coefficients_combination S S_basis v) as v_eq2.
    pose proof (basis_coefficients_in S S_basis v) as Sv.
    pose proof (basis_unique2 S (land S_basis) v _ _ Sl Sv v_eq1 v_eq2) as eq.
    clear - eq.
    unfold basis_coefficients in *.
    unfold linear_remove_zeros, linear_remove_zeros_base in *.
    cbn in *.
    rewrite <- list_filter_filter in eq.
    exact eq.
Qed.

End Basis.
