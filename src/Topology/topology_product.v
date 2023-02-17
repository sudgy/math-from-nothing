Require Import init.

Require Export topology_basis.
Require Export topology_subbasis.
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
Proof.
    intros A B A_open B_open [x1 x2] ABx.
    exists (A * B).
    split. 2: split.
    -   exists A, B.
        repeat split; trivial.
    -   exact ABx.
    -   apply refl.
Qed.
(* begin hide *)

Program Instance subbasis_product_topology : TopologySubbasis (U * V) := {
    top_subbasis S := (∃ A, S = inverse_image fst A ∧ open A) ∨
                      (∃ A, S = inverse_image snd A ∧ open A)
}.
Next Obligation.
    apply all_eq.
    intros x.
    exists all.
    split; [>|exact true].
    left.
    exists all.
    split; [>|apply all_open].
    symmetry; apply all_eq.
    clear x.
    intros x.
    unfold inverse_image.
    exact true.
Qed.

Theorem subbasis_product_topology_eq :
    @basis_topology _ product_topology =
    @basis_topology _ (@subbasis_topology _ subbasis_product_topology).
Proof.
    apply topology_finer_antisym.
    -   apply subbasis_finer.
        intros S [S_basis|S_basis].
        +   destruct S_basis as [A [S_eq A_open]]; subst S.
            apply basis_open.
            exists A, all.
            split; [>|split].
            *   exact A_open.
            *   apply all_open.
            *   apply antisym.
                --  intros x Ax.
                    split; [>exact Ax|exact true].
                --  intros x [Ax Bx].
                    exact Ax.
        +   destruct S_basis as [A [S_eq A_open]]; subst S.
            apply basis_open.
            exists all, A.
            split; [>|split].
            *   apply all_open.
            *   exact A_open.
            *   apply antisym.
                --  intros x Ax.
                    split; [>exact true|exact Ax].
                --  intros x [Bx Ax].
                    exact Ax.
    -   apply basis_finer.
        intros S [A [B [A_open [B_open S_eq]]]]; subst S.
        assert (A * B = (A * all) ∩ (all * B)) as AB_eq.
        {
            apply antisym.
            -   intros [a b] [Aa Bb].
                repeat split; trivial.
            -   intros [a b] [[Aa C0] [C1 Bb]].
                split; assumption.
        }
        rewrite AB_eq.
        apply inter_open2; apply subbasis_open.
        +   left.
            exists A.
            split; [>|exact A_open].
            apply antisym.
            *   intros x [Ax Bx].
                exact Ax.
            *   intros x Ax.
                split; [>exact Ax|exact true].
        +   right.
            exists B.
            split; [>|exact B_open].
            apply antisym.
            *   intros x [Bx Ax].
                exact Ax.
            *   intros x Ax.
                split; [>exact true|exact Ax].
Qed.

End ProductTopology.

Section BasisProduct.

Context {U V} `{TopologyBasis U, TopologyBasis V}.

Local Existing Instance product_topology.
Local Open Scope set_scope.
(* end hide *)

Definition product_basis (S : U * V → Prop) :=
    ∃ A B, top_basis A ∧ top_basis B ∧ S = (A * B).

Theorem product_basis_open : product_basis ⊆ open.
Proof.
    intros S [A [B [A_basis [B_basis S_eq]]]]; subst S.
    apply basis_open.
    exists A, B.
    split; [>|split].
    -   exact (basis_open _ A_basis).
    -   exact (basis_open _ B_basis).
    -   reflexivity.
Qed.

Theorem product_basis_contains :
    ∀ S x, open S → S x → ∃ B, product_basis B ∧ B ⊆ S ∧ B x.
Proof.
    intros S x S_open Sx.
    specialize (S_open x Sx).
    destruct S_open as [B [B_basis [Bx B_sub]]].
    destruct B_basis as [A1 [A2 [A1_open [A2_open B_eq]]]]; subst B.
    destruct Bx as [A1x A2x].
    specialize (A1_open _ A1x) as [B1 [B1_basis [B1x B1_sub]]].
    specialize (A2_open _ A2x) as [B2 [B2_basis [B2x B2_sub]]].
    exists (B1 * B2).
    split; [>|split].
    -   exists B1, B2.
        split; [>|split]; trivial.
    -   apply (trans2 B_sub).
        apply cartesian_product_sub; assumption.
    -   split; assumption.
Qed.

Definition product_basis_topology :=
    make_basis_topology product_basis product_basis_open product_basis_contains.

Theorem product_basis_eq : @basis_topology _ product_basis_topology =
                           @basis_topology _ product_topology.
Proof.
    apply make_basis_equal.
Qed.

(* begin hide *)
End BasisProduct.
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
        +   apply empty_eq.
            intros [x1 x2] [[C0 S1x] [C1 S2x]]; clear C0 C1; cbn in *.
            apply ((land (empty_eq _)) dis x2).
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
        +   apply empty_eq.
            intros [x1 x2] [[S1x C0] [S2x C1]]; clear C0 C1; cbn in *.
            apply ((land (empty_eq _)) dis x1).
            split; assumption.
Qed.

End ProductHausdorff.
