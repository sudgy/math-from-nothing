Require Import init.

Require Export topology_basis.
Require Export topology_axioms.

(* begin hide *)
Section ProductTopology.

Local Open Scope set_scope.

Context {U V} `{Topology U, Topology V}.
(* end hide *)
Program Instance product_topology : TopologyBasis (U * V) := {
    top_basis S := ∃ A B, open A ∧ open B ∧ S = (A * B)
}.
Next Obligation.
    exists all.
    split; try exact true.
    exists all, all.
    repeat split; try apply all_open.
    apply predicate_ext.
    intros y.
    repeat split.
Qed.
Next Obligation.
    rename H1 into S1, H9 into T1, H2 into S2, H5 into T2.
    rename H10 into S1_open, H11 into T1_open, H6 into S2_open, H7 into T2_open.
    destruct x as [u v].
    destruct H3 as [S1u T1v], H4 as [S2u T2v]; cbn in *.
    exists (λ x, (S1 ∩ S2) (fst x) ∧ (T1 ∩ T2) (snd x)); cbn.
    split.
    2: split.
    2: split.
    -   exists (S1 ∩ S2), (T1 ∩ T2).
        repeat split.
        all: apply inter_open2.
        all: assumption.
    -   split; assumption.
    -   split; assumption.
    -   intros [u' v'] [[S1u' S2u'] [T1v' T2v']]; cbn in *.
        repeat split.
        all: assumption.
Qed.

Theorem product_open : ∀ A B, open A → open B → open (A * B).
    intros A B A_open B_open [x1 x2] ABx.
    exists (A * B).
    split. 2: split.
    -   exists A, B.
        repeat split; trivial.
    -   exact ABx.
    -   apply refl.
Qed.

(* begin hide *)
End ProductTopology.
(* end hide *)
Section ProductHausdorff.

(* begin hide *)
Local Open Scope set_scope.
(* end hide *)
Context {U V} `{HausdorffSpace U, HausdorffSpace V}.
Existing Instance product_topology.

Program Instance product_hausdorff : HausdorffSpace (U * V).
Next Obligation.
    rename H3 into neq.
    destruct x1 as [u1 v1], x2 as [u2 v2].
    classic_case (u1 = u2) as [u_eq|u_neq].
    -   subst.
        assert (v1 ≠ v2) as v_neq by (intro contr; subst; contradiction).
        pose proof (hausdorff_space v1 v2 v_neq)
            as [S1 [S2 [S1_open [S2_open [S1v1 [S2v2 dis]]]]]].
        exists (all * S1), (all * S2).
        repeat split.
        +   apply product_open; try assumption.
            exact all_open.
        +   apply product_open; try assumption.
            exact all_open.
        +   exact S1v1.
        +   exact S2v2.
        +   apply not_ex_empty.
            intros [x1 x2] [[C0 S1x] [C1 S2x]]; clear C0 C1; cbn in *.
            apply (empty_not_ex _ dis x2).
            split; assumption.
    -   pose proof (hausdorff_space u1 u2 u_neq)
            as [S1 [S2 [S1_open [S2_open [S1u1 [S2u2 dis]]]]]].
        exists (S1 * all), (S2 * all).
        repeat split.
        +   apply product_open; try assumption.
            exact all_open.
        +   apply product_open; try assumption.
            exact all_open.
        +   exact S1u1.
        +   exact S2u2.
        +   apply not_ex_empty.
            intros [x1 x2] [[S1x C0] [S2x C1]]; clear C0 C1; cbn in *.
            apply (empty_not_ex _ dis x1).
            split; assumption.
Qed.

End ProductHausdorff.
