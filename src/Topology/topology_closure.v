Require Import init.

Require Export topology_base.
Require Import topology_basis.
Require Import topology_axioms.
Require Import topology_subspace.
Require Import nat.

(* begin hide *)
Section ClosureInterior.

Local Open Scope set_scope.
(* end hide *)
Definition closure {U} `{Topology U} A := ⋂ (λ S, closed S ∧ A ⊆ S).
Definition interior {U} `{Topology U} A := ⋃ (λ S, open S ∧ S ⊆ A).

(* begin hide *)
Context {U} `{Topology U}.
(* end hide *)
Theorem closure_closed : ∀ A, closed (closure A).
Proof.
    intros A.
    apply inter_closed.
    intros S [S_closed sub].
    exact S_closed.
Qed.

Theorem interior_open : ∀ A, open (interior A).
Proof.
    intros A.
    apply union_open.
    intros S [S_open sub].
    exact S_open.
Qed.

Theorem closure_sub : ∀ A, A ⊆ closure A.
Proof.
    intros A x Ax S [S_closed sub].
    apply sub.
    exact Ax.
Qed.

Theorem interior_sub : ∀ A, interior A ⊆ A.
Proof.
    intros A x [S [[S_open sub] Sx]].
    apply sub.
    exact Sx.
Qed.

Theorem in_closure : ∀ x A,
    (closure A) x ↔ (∀ S, open S → S x → intersects A S).
Proof.
    intros x A.
    split.
    -   intros A'x S S_open Sx eq.
        apply (A'x (𝐂 S)); try exact Sx.
        split.
        +   unfold closed.
            rewrite compl_compl.
            exact S_open.
        +   intros y Ay.
            classic_contradiction Sy.
            assert ((A ∩ S) y) as contr.
            {
                split; try exact Ay.
                unfold 𝐂 in Sy.
                rewrite not_not in Sy.
                exact Sy.
            }
            rewrite eq in contr.
            exact contr.
    -   intros all_S.
        intros B [B_closed sub].
        classic_contradiction Bx.
        assert (open (𝐂 B)) as B'_open by exact B_closed.
        specialize (all_S (𝐂 B) B_closed Bx).
        unfold intersects in all_S.
        apply all_S.
        apply empty_eq.
        intros y [Ay B'y].
        apply sub in Ay.
        contradiction.
Qed.

Theorem closed_if_closure : ∀ A, closed A ↔ A = closure A.
Proof.
    intros A.
    split.
    -   intros A_closed.
        apply predicate_ext; intros x; split.
        +   intros Ax.
            apply closure_sub.
            exact Ax.
        +   intros Ax.
            specialize (Ax A (make_and A_closed (refl _))).
            exact Ax.
    -   intros eq; rewrite eq.
        apply closure_closed.
Qed.

Theorem open_if_interior : ∀ A, open A ↔ A = interior A.
Proof.
    intros A.
    split.
    -   intros A_open.
        apply predicate_ext; intros x; split.
        +   intros Ax.
            exists A.
            repeat split.
            *   exact A_open.
            *   apply refl.
            *   exact Ax.
        +   intros [S [[S_open sub] Sx]].
            apply sub.
            exact Sx.
    -   intros eq; rewrite eq.
        apply interior_open.
Qed.

Theorem closure_eq_if_closed : ∀ A, closed A → A = closure A.
Proof.
    intros A.
    apply closed_if_closure.
Qed.

Theorem closure_sub_closure : ∀ A B, A ⊆ B → closure A ⊆ closure B.
Proof.
    intros A B AB x Ax.
    intros C [C_closed BC].
    exact (Ax C (make_and C_closed (trans AB BC))).
Qed.

(* begin hide *)
End ClosureInterior.

Section SubspaceClosure.

Context {U} `{Topology U}.

Existing Instance subspace_topology.
(* end hide *)
Theorem subspace_closure : ∀ X A, A ⊆ X →
    closure (to_set_type X A) = to_set_type X (closure A).
Proof.
    intros X A sub.
    apply antisym.
    -   assert (closed (to_set_type X (closure A))) as AX_closed.
        {
            rewrite to_set_type_inter.
            apply (subspace_inter_closed _ _ (closure A)).
            -   apply closure_closed.
            -   reflexivity.
        }
        assert (to_set_type X A ⊆ to_set_type X (closure A)) as sub2.
        {
            apply to_set_type_sub.
            apply closure_sub.
        }
        intros x Ax.
        apply Ax; cbn.
        split; assumption.
    -   pose proof (closure_closed (to_set_type X A)) as A'_closed.
        pose proof (from_set_type_sub_X X (closure (to_set_type X A)))
            as A_sub.
        rewrite <- to_from_set_type in A'_closed.
        apply (subspace_closed_inter _ _ A_sub) in A'_closed.
        destruct A'_closed as [B [B_closed A_eq]].
        assert (A ⊆ B) as sub2.
        {
            assert (A ⊆ (from_set_type (closure (to_set_type X A)))) as sub2.
            {
                apply to_from_set_type_sub.
                -   exact sub.
                -   apply closure_sub.
            }
            apply (trans sub2).
            rewrite A_eq.
            apply inter_lsub.
        }
        assert (closure A ⊆ B) as sub3.
        {
            intros x Ax.
            apply Ax.
            split.
            -   exact B_closed.
            -   exact sub2.
        }
        rewrite <- to_from_set_type.
        rewrite A_eq.
        intros [x Xx] Ax.
        split.
        +   apply sub3.
            exact Ax.
        +   exact Xx.
Qed.

(* begin hide *)
End SubspaceClosure.

Section ClosureBasis.

Context {U} `{TopologyBasis U}.
(* end hide *)
Theorem basis_in_closure : ∀ x A,
    (closure A) x ↔ ∀ B, top_basis B → B x → intersects A B.
Proof.
    intros x A.
    split.
    -   intros Ax B B_basis Bx.
        rewrite in_closure in Ax.
        exact (Ax B (basis_open _ B_basis) Bx).
    -   intros all_B A' [A'_closed sub].
        classic_contradiction Ax.
        unfold closed in A'_closed.
        rewrite <- (compl_compl A') in Ax.
        unfold 𝐂 in Ax at 1.
        rewrite not_not in Ax.
        unfold open in A'_closed; cbn in A'_closed.
        specialize (A'_closed x Ax) as [B [B_basis [Bx B_sub]]].
        specialize (all_B B B_basis Bx).
        apply all_B.
        apply empty_eq.
        intros y [Ay By].
        apply B_sub in By.
        apply sub in Ay.
        contradiction.
Qed.

(* begin hide *)
End ClosureBasis.

(* end hide *)
Section ClosureHausdorff.

(* begin hide *)
Local Open Scope card_scope.
Local Open Scope set_scope.
(* end hide *)
Context {U} `{HausdorffSpace U}.

Theorem point_closed : ∀ x, closed ❴x❵.
Proof.
    intros x.
    rewrite closed_if_closure.
    apply (antisym (op := subset)).
    -   apply closure_sub.
    -   intros y y_closure.
        apply singleton_eq.
        classic_contradiction contr.
        pose proof (hausdorff_space x y contr)
            as [S1 [S2 [S1_open [S2_open [S1x [S2y S1S2]]]]]].
        rewrite in_closure in y_closure.
        specialize (y_closure S2 S2_open S2y).
        assert ((S1 ∩ S2) x) as x_in.
        {
            split; try exact S1x.
            apply empty_neq in y_closure.
            destruct y_closure as [x' [x'_eq S2x']].
            rewrite singleton_eq in x'_eq; subst.
            exact S2x'.
        }
        unfold disjoint in S1S2.
        rewrite S1S2 in x_in.
        contradiction x_in.
Qed.

Theorem finite_point_closed : ∀ A, finite (|set_type A|) → closed A.
Proof.
    intros A A_fin.
    apply fin_nat_ex in A_fin as [n A_fin].
    revert A A_fin.
    nat_induction n.
    -   intros.
        apply zero_is_empty in A_fin.
        rewrite A_fin.
        apply empty_closed.
    -   intros A A_fin.
        assert (set_type A) as [x Ax].
        {
            clear - A_fin.
            classic_contradiction contr.
            rewrite <- card_0_false in contr.
            rewrite contr in A_fin.
            apply nat_to_card_eq in A_fin.
            inversion A_fin.
        }
        symmetry in A_fin.
        pose proof (card_plus_one_nat A n [x|Ax] A_fin) as A'_fin; cbn in *.
        remember (A - ❴x❵) as A'.
        assert (A = A' ∪ ❴x❵) as eq.
        {
            apply predicate_ext; intros y; split.
            -   intros Ay.
                classic_case (x = y) as [eq|neq].
                +   rewrite eq.
                    right; reflexivity.
                +   left.
                    rewrite HeqA'; split.
                    *   exact Ay.
                    *   exact neq.
            -   intros [A'y|xy].
                +   rewrite HeqA' in A'y.
                    apply A'y.
                +   rewrite singleton_eq in xy; rewrite <- xy.
                    exact Ax.
        }
        rewrite eq.
        apply union_closed2.
        +   apply IHn.
            symmetry; exact A'_fin.
        +   apply point_closed.
Qed.

End ClosureHausdorff.
