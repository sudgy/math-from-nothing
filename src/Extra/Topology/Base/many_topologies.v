Require Import init.

Require Import topology.

Section ManyTopologies.

Context {U} (Tops : (Topology U) → Prop).
Definition opens SS := ∃ Top, Tops Top ∧ (@open U Top = SS).

Program Instance opens_inter_topology : Topology U := {
    open := ⋂ opens
}.
Next Obligation.
    destruct H as [Top [Tops_Top open_eq]].
    rewrite <- open_eq.
    apply empty_open.
Qed.
Next Obligation.
    destruct H as [Top [Tops_Top open_eq]].
    rewrite <- open_eq.
    apply all_open.
Qed.
Next Obligation.
    rename H0 into A_opens.
    pose proof A_opens as [Top [Tops_top open_eq]].
    rewrite <- open_eq.
    rename S into SS, H into SS_sub.
    apply union_open.
    apply (trans SS_sub).
    intros S S_open.
    specialize (S_open A A_opens).
    rewrite open_eq.
    exact S_open.
Qed.
Next Obligation.
    rename S into SS, H into SS_sub, H0 into SS_fin, H1 into A_opens.
    pose proof A_opens as [Top [Tops_top open_eq]].
    rewrite <- open_eq.
    apply inter_open.
    2: exact SS_fin.
    apply (trans SS_sub).
    intros S S_open.
    specialize (S_open A A_opens).
    rewrite open_eq.
    exact S_open.
Qed.

Program Instance opens_union_topology : Topology U := {
    open S := (∃ SS, SS ⊆ (⋃ opens) ∧ S = ⋃ SS) ∨ S = all ∨ S = ∅
}.
(* It handled all/empty on its own *)
Next Obligation.
    rename S into SS.
    rename H into SS_open.
    classic_case (∃ Top, Tops Top) as [Top|NoTop].
    2: {
        right.
        classic_case (SS all) as [SS_all|SS_nall].
        -   left.
            apply all_is_all.
            intros x.
            exists all.
            split.
            +   exact SS_all.
            +   exact true.
        -   right.
            apply not_ex_empty.
            intros x [A [SS_A Ax]].
            apply SS_open in SS_A as SS_A2.
            destruct SS_A2 as [SS_A2|[A_all|A_empty]].
            +   destruct SS_A2 as [SS' [SS'_sub A_eq]].
                rewrite A_eq in Ax.
                destruct Ax as [B [SS'B Bx]].
                apply SS'_sub in SS'B.
                destruct SS'B as [TT [TT_opens TT_B]].
                unfold opens in TT_opens.
                apply NoTop.
                destruct TT_opens as [Top [TopsTop TT_open]].
                exists Top.
                exact TopsTop.
            +   rewrite A_all in SS_A.
                contradiction.
            +   rewrite A_empty in Ax.
                contradiction.
    }
    destruct Top as [Top TopsTop].
    left.
    assert (∀ S, (SS S ∧ S ≠ ∅) → ∃ TT, TT ⊆ ⋃ opens ∧ S = ⋃ TT) as TT_ex.
    {
        intros S [SS_S S_nempty].
        apply SS_open in SS_S.
        destruct SS_S as [SS_S|[S_all|S_empty]].
        2: {
            exists open.
            split.
            -   intros T T_open.
                exists open.
                split; try assumption.
                exists Top.
                split; trivial.
            -   rewrite S_all.
                symmetry; apply all_is_all.
                intros x.
                exists all.
                split.
                +   apply all_open.
                +   exact true.
        }
        2: contradiction.
        exact SS_S.
    }
    clear SS_open.
    pose (to_TT S H := ex_val (TT_ex S H)).
    assert (∀ S H, to_TT S H ⊆ ⋃ opens) as TT_opens.
    {
        intros S H.
        unfold to_TT.
        old_unpack_ex_val TT TT_H.
        apply TT_H.
    }
    assert (∀ S H, S = ⋃ (to_TT S H)) as TT_union_eq.
    {
        intros S H.
        unfold to_TT.
        old_unpack_ex_val TT TT_H.
        apply TT_H.
    }
    pose (SS_split T := ∃ TT S H, TT = to_TT S H ∧ TT T).
    exists SS_split.
    split.
    -   intros S SS_split_S.
        destruct SS_split_S as [TT [S' [H [TT_eq TT_T]]]].
        subst TT.
        apply TT_opens in TT_T.
        exact TT_T.
    -   apply antisym.
        +   intros x [A [SS_A Ax]].
            assert (A ≠ ∅) as A_nempty.
            {
                apply ex_not_empty.
                exists x.
                exact Ax.
            }
            pose (H := make_and SS_A A_nempty).
            rewrite (TT_union_eq A H) in Ax.
            destruct Ax as [A' [TT_A' A'x]].
            exists A'.
            split; try exact A'x.
            exists (to_TT A H), A, H.
            split; trivial.
        +   intros x [A [[TT [S [H [TT_eq TT_T]]]] Ax]].
            subst TT.
            exists S.
            split; try apply H.
            rewrite (TT_union_eq S H).
            exists A.
            split; assumption.
Qed.
Next Obligation.
