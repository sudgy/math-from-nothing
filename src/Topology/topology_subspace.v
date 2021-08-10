Require Import init.

Require Export topology_base.
Require Export topology_axioms.
Require Export topology_basis.

(* begin hide *)
Section SubspaceTopology.

Local Open Scope set_scope.

Context {U} `{Topology U}.
(* end hide *)

Variable X : U → Prop.

Program Instance subspace_topology : Topology (set_type X) := {
    open S := ∃ T, open T ∧ S = to_set_type X T
}.
Next Obligation.
    exists ∅.
    split.
    -   apply empty_open.
    -   apply predicate_ext.
        intros x.
        split; contradiction.
Qed.
Next Obligation.
    exists all.
    split.
    -   apply all_open.
    -   apply predicate_ext.
        intros x.
        repeat split; exact I.
Qed.
Next Obligation.
    rename H0 into sub.
    unfold subset in sub.
    pose (S' A := ∃ s, A = ex_val (sub [s|] [|s])).
    exists (⋃ S').
    split.
    -   apply union_open.
        intros A [s A_eq].
        rewrite A_eq; clear A A_eq.
        rewrite_ex_val A A_H.
        apply A_H.
    -   apply predicate_ext.
        intros x.
        split.
        +   intros [A [SA Ax]].
            exists (ex_val (sub A SA)).
            split.
            --  exists [A|SA].
                cbn.
                reflexivity.
            --  rewrite_ex_val B B_H.
                destruct B_H as [B_open A_eq].
                subst A.
                apply Ax.
        +   intros [A [[s A_eq] Ax]].
            subst A.
            rewrite_ex_val t tH.
            destruct tH as [t_open s_eq].
            exists [s|].
            split.
            *   exact [|s].
            *   rewrite s_eq.
                assumption.
Qed.
Next Obligation.
    rename H0 into sub, H1 into S_fin.
    unfold subset in sub.
    pose (S' A := ∃ s, A = ex_val (sub [s|] [|s])).
    exists (⋂ S').
    split.
    -   apply inter_open.
        +   intros A [s A_eq].
            rewrite A_eq; clear A A_eq.
            rewrite_ex_val A A_H.
            apply A_H.
        +   apply (le_lt_trans2 S_fin).
            clear S_fin.
            unfold le; equiv_simpl.
            exists (λ (A : set_type S'), ex_val [|A]).
            intros [A [[A' SA'] A_eq]] [B [[B' SB'] B_eq]] eq; cbn in *.
            apply set_type_eq; cbn.
            subst A B.
            cbn in *.
            revert eq.
            rewrite_ex_val x x_eq.
            rewrite_ex_val y y_eq.
            intros eq.
            rewrite x_eq, y_eq.
            subst x.
            reflexivity.
    -   apply predicate_ext.
        intros x.
        split.
        +   intros all_A.
            intros A [s A_eq].
            rewrite A_eq; clear A A_eq.
            rewrite_ex_val A A_H.
            destruct A_H as [A_open s_eq].
            specialize (all_A [s|] [|s]).
            rewrite s_eq in all_A.
            apply all_A.
        +   intros all_A A SA.
            assert (S' (ex_val (sub A SA))) as S'A.
            {
                exists [A|SA].
                reflexivity.
            }
            specialize (all_A (ex_val (sub A SA)) S'A).
            rewrite_ex_val A' A'H.
            destruct A'H as [A'_open A_eq].
            rewrite A_eq.
            exact all_A.
Qed.

Theorem subspace_open : ∀ S : U → Prop, open S → open (to_set_type X S).
    intros S S_open.
    exists S.
    split.
    -   exact S_open.
    -   reflexivity.
Qed.

Theorem open_subspace_open : open X → ∀ S : U → Prop,
        S ⊆ X → open (to_set_type X S) → open S.
    intros X_open S sub S_open.
    unfold open in S_open; cbn in S_open.
    destruct S_open as [T [T_open T_eq]].
    assert (S = T ∩ X) as eq.
    {
        apply predicate_ext.
        intros x; split.
        -   intros Sx.
            specialize (sub x Sx).
            assert (to_set_type X S [x|sub]) as x_in by exact Sx.
            rewrite T_eq in x_in.
            split.
            +   exact x_in.
            +   exact sub.
        -   intros [Tx Xx].
            assert (to_set_type X T [x|Xx]) as x_in by exact Tx.
            rewrite <- T_eq in x_in.
            exact x_in.
    }
    rewrite eq.
    apply inter_open2; assumption.
Qed.

Theorem subspace_inter_closed : ∀ A B, closed B → A = B ∩ X →
        closed (to_set_type X A).
    intros A B B_closed A_eq.
    unfold closed in B_closed.
    assert (open (λ x : set_type X, (complement B) [x|])) as B'_open.
    {
        unfold open; cbn.
        exists (complement B).
        split.
        -   exact B_closed.
        -   apply antisym; cbn.
            +   intros [x Xx] nBx; cbn in *.
                exact nBx.
            +   intros [x Xx] nBx; cbn in *.
                exact nBx.
    }
    unfold closed.
    assert (complement (to_set_type X A) =
        (λ x : set_type X, complement B [x|])) as eq.
    {
        apply antisym.
        -   intros [x Xx] nAx Bx; cbn in *.
            apply nAx.
            rewrite A_eq.
            split; assumption.
        -   intros [x Xx] nBx Ax; cbn in *.
            rewrite A_eq in Ax.
            destruct Ax; contradiction.
    }
    rewrite eq.
    exact B'_open.
Qed.
Theorem subspace_closed_inter : ∀ A, A ⊆ X → closed (to_set_type X A) →
        ∃ B, closed B ∧ A = B ∩ X.
    intros A sub A'_closed.
    unfold closed in A'_closed.
    destruct A'_closed as [S [S_open S_eq]].
    exists (complement S).
    split.
    +   apply open_complement_closed.
        exact S_open.
    +   apply (f_equal complement) in S_eq.
        rewrite compl_compl in S_eq.
        unfold complement in S_eq.
        apply antisym.
        *   intros x Ax.
            assert (to_set_type X A [x|sub x Ax]) as x_in.
            {
                exact Ax.
            }
            rewrite S_eq in x_in.
            split.
            ++  exact x_in.
            ++  exact (sub x Ax).
        *   intros x [nSx Xx].
            assert ((λ x : set_type X, ¬to_set_type X S x) [x|Xx])
                as x_in by exact nSx.
            rewrite <- S_eq in x_in.
            exact x_in.
Qed.

Theorem closed_subspace_closed : closed X → ∀ S : U → Prop,
        S ⊆ X → closed (to_set_type X S) → closed S.
    intros X_closed S sub S_closed.
    unfold closed, open in S_closed; cbn in S_closed.
    destruct S_closed as [T [T_open T_eq]].
    unfold closed.
    assert (complement S = T ∪ (complement X)) as eq.
    {
        apply antisym.
        -   intros x nSx.
            classic_case (X x) as [Xx|nXx].
            +   assert ((complement (to_set_type X S)) [x|Xx]) as x_in
                    by exact nSx.
                rewrite T_eq in x_in.
                left; apply x_in.
            +   right; exact nXx.
        -   intros x x_in.
            classic_case (X x) as [Xx|nXx].
            +   destruct x_in as [Tx|nXx]; try contradiction.
                assert (to_set_type X T [x|Xx]) as x_in by exact Tx.
                rewrite <- T_eq in x_in.
                exact x_in.
            +   intros Sx.
                apply sub in Sx.
                contradiction.
    }
    rewrite eq.
    apply union_open2; assumption.
Qed.

(* begin hide *)
End SubspaceTopology.

Section SubspaceBasis.

Context {U} `{TopologyBasis U}.
Existing Instance subspace_topology.
Variable X : U → Prop.
(* end hide *)

Let C S := ∃ B, top_basis B ∧ S = to_set_type X B.

Lemma subspace_basis_open : C ⊆ open.
    intros S [B [B_basis eq]].
    rewrite eq.
    exists B.
    split; try reflexivity.
    apply basis_open.
    exact B_basis.
Qed.

Lemma subspace_basis_contains : ∀ S x, open S → S x → ∃ B, C B ∧ B ⊆ S ∧ B x.
    intros S x [T [T_open S_eq]] Sx.
    subst S.
    specialize (T_open [x|] Sx) as [B [B_basis [Bx B_sub]]].
    exists (to_set_type X B).
    repeat split.
    -   exists B.
        split; trivial.
    -   apply to_set_type_sub.
        exact B_sub.
    -   exact Bx.
Qed.

Definition subspace_basis_topology :=
    (make_basis_topology C subspace_basis_open subspace_basis_contains).

Existing Instance subspace_basis_topology.

Theorem subspace_basis_eq : basis_topology = (subspace_topology X).
    apply make_basis_equal.
Qed.

(* begin hide *)
End SubspaceBasis.
(* end hide *)

Section SubspaceHausdorff.

Local Open Scope set_scope.
Context {U} `{HausdorffSpace U}.
Variable X : U → Prop.

Existing Instance subspace_topology.

Program Instance subspace_hausdorff : HausdorffSpace (set_type X).
Next Obligation.
    rename H1 into neq'.
    destruct x1 as [x1 Xx1], x2 as [x2 Xx2]; cbn.
    assert (x1 ≠ x2) as neq.
    {
        intro; subst.
        apply neq'.
        apply set_type_eq; reflexivity.
    }
    clear neq'.
    pose proof (hausdorff_space x1 x2 neq)
        as [S1 [S2 [S1_open [S2_open [S1x [S2x dis]]]]]].
    exists (λ x, S1 [x|]), (λ x, S2 [x|]).
    repeat split.
    -   exists S1.
        split.
        +   exact S1_open.
        +   apply predicate_ext.
            intros x.
            reflexivity.
    -   exists S2.
        split.
        +   exact S2_open.
        +   apply predicate_ext.
            intros x.
            reflexivity.
    -   exact S1x.
    -   exact S2x.
    -   apply not_ex_empty.
        intros [y y_in] [S1y S2y]; cbn in *.
        apply (empty_not_ex _ dis y).
        split; assumption.
Qed.

End SubspaceHausdorff.
