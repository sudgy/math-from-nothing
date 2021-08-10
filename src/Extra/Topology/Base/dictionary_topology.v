Require Import init.

Require Import topology.
Require Import order_minmax.
Require Import order_dict.

Lemma real2_distinct : ∃ a b : (real * real), a ≠ b.
    exists (0, 0), (0, 1).
    intros contr.
    apply (f_equal snd) in contr.
    cbn in contr.
    apply not_trivial.
    exact contr.
Qed.

Definition dict_order := dictionary_order real real.

Existing Instance dict_order.

Definition dict_topology1 := order_topology real2_distinct.

Program Instance dict_topology2 : TopologyBasis (real * real) := {
    top_basis S := ∃ a b d, S = (λ x, snd x = a ∧ b < fst x ∧ fst x < d)
}.
Next Obligation.
    destruct x as [x1 x2].
    exists (λ x, snd x = x2 ∧ (x1 - 1) < fst x ∧ fst x < (x1 + 1)).
    split.
    -   exists x2, (x1 - 1), (x1 + 1).
        reflexivity.
    -   cbn.
        split.
        2: split.
        +   reflexivity.
        +   apply lt_plus_rrmove.
            apply plus_one_pos.
        +   apply plus_one_pos.
Qed.
Next Obligation.
    rename H into a1, H6 into b1, H7 into d1, H0 into a2, H3 into b2, H4 into d2.
    destruct x as [x1 x2]; cbn in *.
    destruct H1 as [a1_eq [b1_lt d1_gt]].
    destruct H2 as [a2_eq [b2_lt d2_gt]].
    subst a1 a2.
    exists (λ x, snd x = x2 ∧ (max b1 b2) < fst x ∧ fst x < (min d1 d2)).
    cbn.
    split.
    2: split.
    -   exists x2, (max b1 b2), (min d1 d2).
        reflexivity.
    -   split.
        2: split.
        +   reflexivity.
        +   unfold max; case_if; assumption.
        +   unfold min; case_if; assumption.
    -   intros [y1 y2] [y1_eq [y2_gt y2_lt]].
        split; cbn in *.
        +   split.
            2: split.
            *   exact y1_eq.
            *   exact (le_lt_trans (lmax _ _) y2_gt).
            *   exact (lt_le_trans y2_lt (lmin _ _)).
        +   split.
            2: split.
            *   exact y1_eq.
            *   exact (le_lt_trans (rmax _ _) y2_gt).
            *   exact (lt_le_trans y2_lt (rmin _ _)).
Qed.

Theorem dict_topology_eq :
        @basis_topology _ dict_topology1 = @basis_topology _ dict_topology2.
    apply topology_finer_antisym.
    all: apply topology_basis_finer.
    -   intros x B2 B2_basis B2x.
        exists B2.
        split.
        2: split.
        +   left.
            unfold top_basis in B2_basis; cbn in B2_basis.
            destruct B2_basis as [a [b [d B2_eq]]].
            subst B2.
            exists (b, a), (d, a).
            unfold open_interval; cbn.
            apply predicate_ext.
            intros [x1 x2]; cbn.
            split.
            *   intros [eq [x1_gt x1_lt]].
                subst a.
                split.
                --  split.
                    ++  right.
                        split; try reflexivity.
                        apply x1_gt.
                    ++  intro contr.
                        inversion contr.
                        subst.
                        destruct x1_gt; contradiction.
                --  split.
                    ++  right.
                        split; try reflexivity.
                        apply x1_lt.
                    ++  intro contr.
                        inversion contr.
                        subst.
                        destruct x1_lt; contradiction.
            *   intros [[leq1 neq1] [leq2 neq2]].
                destruct leq1 as [ltq1|leq1]; destruct leq2 as [ltq2|leq2].
                --  destruct (trans ltq1 ltq2); contradiction.
                --  destruct leq2; subst.
                    destruct ltq1; contradiction.
                --  destruct leq1; subst.
                    destruct ltq2; contradiction.
                --  destruct leq1 as [leq1], leq2 as [leq2]; subst a.
                    split.
                    2: split.
                    ++  reflexivity.
                    ++  split; try exact leq1.
                        intro contr.
                        subst.
                        contradiction.
                    ++  split; try exact leq2.
                        intro contr.
                        subst.
                        contradiction.
        +   exact B2x.
        +   apply refl.
    -   intros [x1 x2] B2 B2_basis B2x.
        unfold top_basis in *; cbn in *.
        destruct B2_basis as [B2_basis|B2_basis].
        2: {
            destruct B2_basis as [B2_basis|B2_basis].
            -   destruct B2_basis as [[a1 a2] [[b1 b2] [B2_eq b_min]]].
                specialize (b_min (b1 + 1, b2)).
                unfold le in b_min; cbn in b_min.
                destruct b_min as [[b_min]|[leq eq]]; try contradiction.
                rewrite <- nlt_le in leq.
                exfalso; apply leq.
                apply plus_one_pos.
            -   destruct B2_basis as [[a1 a2] [[b1 b2] [B2_eq a_max]]].
                specialize (a_max (a1 - 1, a2)).
                unfold le in a_max; cbn in a_max.
                destruct a_max as [[a_max]|[leq eq]]; try contradiction.
                rewrite <- nlt_le in leq.
                exfalso; apply leq.
                apply lt_plus_rrmove.
                apply plus_one_pos.
        }
        destruct B2_basis as [[a1 a2] [[b1 b2] B2_eq]].
        subst B2.
        pose (b := If a1 < x1 then a1 else x1 - 1).
        pose (d := If x1 < b1 then b1 else x1 + 1).
        exists (λ x, snd x = x2 ∧ b < fst x ∧ fst x < d).
        cbn.
        split.
        2: split.
        +   exists x2, b, d.
            reflexivity.
        +   split.
            2: split.
            *   reflexivity.
            *   unfold b; case_if; try assumption.
                apply lt_plus_rrmove.
                apply plus_one_pos.
            *   unfold d; case_if; try assumption.
                apply plus_one_pos.
        +   intros [y1 y2] [x2_eq [y1_gt y1_lt]]; cbn in *.
            subst y2.
            destruct B2x as [[leq1 neq1] [leq2 neq2]].
            unfold b in y1_gt; case_if;
            unfold d in y1_lt; case_if.
            *   split; split.
                --  unfold le; cbn.
                    destruct leq1 as [leq1|leq1].
                    ++  left; exact leq1.
                    ++  right.
                        split.
                        **  apply y1_gt.
                        **  apply leq1.
                --  intro contr.
                    inversion contr; subst.
                    destruct y1_gt; contradiction.
                --  unfold le; cbn.
                    destruct leq2 as [leq2|leq2].
                    ++  left; exact leq2.
                    ++  right.
                        split.
                        **  apply y1_lt.
                        **  apply leq2.
                --  intro contr.
                    inversion contr; subst.
                    destruct y1_lt; contradiction.
            *   split; split.
                --  unfold le; cbn.
                    destruct leq1 as [leq1|leq1].
                    ++  left; exact leq1.
                    ++  right.
                        split.
                        **  apply y1_gt.
                        **  apply leq1.
                --  intro contr.
                    inversion contr; subst.
                    destruct y1_gt; contradiction.
                --  unfold le; cbn.
                    destruct leq2 as [leq2|leq2].
                    ++  left; exact leq2.
                    ++  destruct leq2 as [leq2 eq2].
                        rewrite nlt_le in n.
                        pose proof (antisym leq2 n).
                        subst.
                        contradiction.
                --  intro contr.
                    inversion contr; subst.
                    destruct leq2 as [leq2|leq2].
                    ++  destruct leq2; contradiction.
                    ++  destruct leq2 as [leq2 eq2].
                        rewrite nlt_le in n.
                        pose proof (antisym leq2 n).
                        subst.
                        contradiction.
            *   split; split.
                --  unfold le; cbn.
                    destruct leq1 as [leq1|leq1].
                    ++  left; exact leq1.
                    ++  destruct leq1 as [leq1 eq1].
                        rewrite nlt_le in n.
                        pose proof (antisym leq1 n).
                        subst.
                        contradiction.
                --  intro contr.
                    inversion contr; subst.
                    destruct leq1 as [leq1|leq1].
                    ++  destruct leq1; contradiction.
                    ++  destruct leq1 as [leq1 eq1].
                        rewrite nlt_le in n.
                        pose proof (antisym leq1 n).
                        subst.
                        contradiction.
                --  unfold le; cbn.
                    destruct leq2 as [leq2|leq2].
                    ++  left; exact leq2.
                    ++  right.
                        split.
                        **  apply y1_lt.
                        **  apply leq2.
                --  intro contr.
                    inversion contr; subst.
                    destruct y1_lt; contradiction.
            *   split; split.
                --  unfold le; cbn.
                    destruct leq1 as [leq1|leq1].
                    ++  left; exact leq1.
                    ++  destruct leq1 as [leq1 eq1].
                        rewrite nlt_le in n.
                        pose proof (antisym leq1 n).
                        subst.
                        contradiction.
                --  intro contr.
                    inversion contr; subst.
                    destruct leq1 as [leq1|leq1].
                    ++  destruct leq1; contradiction.
                    ++  destruct leq1 as [leq1 eq1].
                        rewrite nlt_le in n.
                        pose proof (antisym leq1 n).
                        subst.
                        contradiction.
                --  unfold le; cbn.
                    destruct leq2 as [leq2|leq2].
                    ++  left; exact leq2.
                    ++  destruct leq2 as [leq2 eq2].
                        rewrite nlt_le in n0.
                        pose proof (antisym leq2 n0).
                        subst.
                        contradiction.
                --  intro contr.
                    inversion contr; subst.
                    destruct leq2 as [leq2|leq2].
                    ++  destruct leq2; contradiction.
                    ++  destruct leq2 as [leq2 eq2].
                        rewrite nlt_le in n0.
                        pose proof (antisym leq2 n0).
                        subst.
                        contradiction.
Qed.
