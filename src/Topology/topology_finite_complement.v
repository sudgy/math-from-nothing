Require Import init.

Require Export topology_base.

Section FiniteComplement.

Variable U : Type.

Open Scope card_scope.

Program Instance finite_complement_topology : Topology U := {
    open S := finite (|set_type (𝐂 S)|) ∨ 𝐂 S = all
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
    rename H into SS_sub.
    classic_case (⋃ SS = ∅) as [SS_empty|SS_nempty].
    -   right.
        rewrite SS_empty.
        exact compl_empty.
    -   left.
        rewrite big_union_compl.
        apply finite_inter_finite.
        apply empty_neq in SS_nempty as [x [S [SS_S Sx]]].
        exists (𝐂 S).
        rewrite compl_compl.
        split; [>exact SS_S|].
        apply SS_sub in SS_S.
        destruct SS_S as [SS_S|SS_S]; [>exact SS_S|].
        apply (f_equal 𝐂) in SS_S.
        rewrite compl_compl in SS_S.
        rewrite compl_all in SS_S.
        rewrite SS_S in Sx.
        contradiction Sx.
Qed.
Next Obligation.
    rename S into SS, H into SS_sub, H0 into SS_fin.
    classic_case (⋂ SS = ∅) as [SS_empty|SS_nempty].
    -   right.
        rewrite SS_empty.
        exact compl_empty.
    -   left.
        rewrite big_inter_compl.
        apply finite_union_finite.
        +   apply (le_lt_trans2 SS_fin).
            unfold le; equiv_simpl.
            exists (λ A : set_type (λ S, SS (𝐂 S)), [𝐂 [A|]| [|A]]).
            split.
            intros A B eq.
            rewrite set_type_eq2 in eq.
            apply (f_equal 𝐂) in eq.
            do 2 rewrite compl_compl in eq.
            rewrite set_type_eq in eq.
            exact eq.
        +   intros S SS_S.
            specialize (SS_sub _ SS_S); cbn in SS_sub.
            rewrite compl_compl in SS_sub.
            destruct SS_sub as [SS_sub|SS_sub]; [>exact SS_sub|].
            rewrite SS_sub in SS_S.
            rewrite compl_all in SS_S.
            apply empty_neq in SS_nempty as [x x_in].
            specialize (x_in _ SS_S).
            contradiction x_in.
Qed.

End FiniteComplement.
