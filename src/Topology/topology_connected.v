Require Import init.

Require Export topology_base.
Require Export topology_subspace.
Require Export topology_closure.
Require Export topology_limit.

Definition separation {U} `{Topology U} A B :=
    A ≠ ∅ ∧ B ≠ ∅ ∧ open A ∧ open B ∧ disjoint A B ∧ A ∪ B = all.
Definition sub_separation {U} `{Topology U} X A B :=
    A ≠ ∅ ∧ B ≠ ∅ ∧ disjoint A B ∧ A ∪ B = X ∧
    (∀ x, limit_point A x → ¬B x) ∧ (∀ x, limit_point B x → ¬A x).

Definition connected U `{Topology U} := ∀ A B, ¬separation A B.

(* begin hide *)
Section Connected.

Context {U} `{Topology U}.
(* end hide *)
Theorem separation_comm : ∀ A B, separation A B ↔ separation B A.
Proof.
    intros A B.
    split.
    -   intros [A_empty [B_empty [A_open [B_open [AB_dis AB_all]]]]].
        unfold disjoint in AB_dis.
        rewrite inter_comm in AB_dis.
        rewrite union_comm in AB_all.
        repeat split; assumption.
    -   intros [B_empty [A_empty [B_open [A_open [AB_dis AB_all]]]]].
        unfold disjoint in AB_dis.
        rewrite inter_comm in AB_dis.
        rewrite union_comm in AB_all.
        repeat split; assumption.
Qed.

Theorem connected_clopen : connected U ↔ (∀ S, clopen S → S = all ∨ S = ∅).
Proof.
    split.
    -   intros connect S [S_open S_closed].
        classic_contradiction contr.
        rewrite not_or in contr.
        destruct contr as [S_all S_empty].
        unfold connected in connect.
        apply (connect S (𝐂 S)).
        repeat split.
        +   exact S_empty.
        +   apply empty_neq.
            apply all_neq in S_all.
            exact S_all.
        +   exact S_open.
        +   exact S_closed.
        +   apply empty_eq.
            intros x [Sx nSx].
            contradiction.
        +   apply (antisym (op := subset)).
            *   apply all_sub.
            *   intros x C0; clear C0.
                classic_case (S x) as [Sx|nSx].
                --  left; exact Sx.
                --  right; exact nSx.
    -   intros all_clopen.
        intros A B [A_nempty [B_nempty [A_open [B_open [AB_dis AB_all]]]]].
        assert (A = 𝐂 B) as A_eq.
        {
            apply (antisym (op := subset)).
            -   intros x Ax Bx.
                assert ((A ∩ B) x) as x_in by (split; assumption).
                unfold disjoint in AB_dis.
                rewrite AB_dis in x_in.
                exact x_in.
            -   intros x nBx.
                assert (all x) as x_in by exact true.
                rewrite <- AB_all in x_in.
                destruct x_in as [Ax|Bx].
                +   exact Ax.
                +   contradiction.
        }
        assert (clopen A) as A_clopen.
        {
            split; try exact A_open.
            rewrite A_eq.
            apply open_complement_closed.
            exact B_open.
        }
        assert (clopen B) as B_clopen.
        {
            split; try exact B_open.
            unfold closed.
            rewrite <- A_eq.
            exact A_open.
        }
        pose proof (all_clopen _ A_clopen) as [A_all|A_empty].
        1: pose proof (all_clopen _ B_clopen) as [B_all|B_empty].
        +   subst.
            rewrite compl_all in A_nempty.
            contradiction.
        +   contradiction.
        +   contradiction.
Qed.
Existing Instance subspace_topology.

Theorem sub_connected1 : ∀ (X : U → Prop) (A B : U → Prop),
    sub_separation X A B → separation (to_set_type X A) (to_set_type X B).
Proof.
    -   intros X A B [A_empty [B_empty [AB_dis [AB_X [A_lim B_lim]]]]].
        assert (closure A ∩ B = ∅) as cAB_empty.
        {
            apply empty_eq.
            intros x [Ax Bx].
            rewrite closure_limit_points in Ax.
            destruct Ax as [Ax|lim].
            -   unfold disjoint in AB_dis.
                assert ((A ∩ B) x) as x_in by (split; assumption).
                rewrite AB_dis in x_in.
                exact x_in.
            -   exact (A_lim _ lim Bx).
        }
        assert (A ∩ closure B = ∅) as AcB_empty.
        {
            apply empty_eq.
            intros x [Ax Bx].
            rewrite closure_limit_points in Bx.
            destruct Bx as [Bx|lim].
            -   unfold disjoint in AB_dis.
                assert ((A ∩ B) x) as x_in by (split; assumption).
                rewrite AB_dis in x_in.
                exact x_in.
            -   exact (B_lim _ lim Ax).
        }
        assert (closure A ∩ X = A) as A_eq.
        {
            rewrite <- AB_X.
            rewrite inter_ldist.
            rewrite cAB_empty.
            rewrite union_rid.
            apply rsub_inter_equal.
            apply closure_sub.
        }
        assert (closure B ∩ X = B) as B_eq.
        {
            rewrite <- AB_X.
            rewrite inter_ldist.
            rewrite inter_comm in AcB_empty.
            rewrite AcB_empty.
            rewrite union_lid.
            apply rsub_inter_equal.
            apply closure_sub.
        }
        pose proof (union_lsub A B) as AX.
        pose proof (union_rsub A B) as BX.
        rewrite AB_X in AX, BX.
        assert (closed (to_set_type X A)) as A'_closed.
        {
            rewrite <- A_eq.
            rewrite <- to_set_type_inter.
            rewrite <- (subspace_closure _ _ AX).
            apply closure_closed.
        }
        assert (closed (to_set_type X B)) as B'_closed.
        {
            rewrite <- B_eq.
            rewrite <- to_set_type_inter.
            rewrite <- (subspace_closure _ _ BX).
            apply closure_closed.
        }
        assert (to_set_type X A = 𝐂 (to_set_type X B)) as A'_eq.
        {
            apply (antisym (op := subset)).
            -   intros x Ax Bx.
                unfold disjoint in AB_dis.
                assert ((A ∩ B) [x|]) as x_in by (split; assumption).
                rewrite AB_dis in x_in.
                exact x_in.
            -   intros [x Xx] nBx.
                pose proof Xx as Xx2.
                rewrite <- AB_X in Xx2.
                destruct Xx2 as [Ax|Bx].
                +   exact Ax.
                +   contradiction.
        }
        assert ((to_set_type X B) = 𝐂 (to_set_type X A)) as B'_eq.
        {
            rewrite A'_eq.
            rewrite compl_compl.
            reflexivity.
        }
        repeat split.
        +   apply empty_neq.
            apply empty_neq in A_empty.
            destruct A_empty as [x Ax].
            exists [x|AX x Ax].
            exact Ax.
        +   apply empty_neq.
            apply empty_neq in B_empty.
            destruct B_empty as [x Bx].
            exists [x|BX x Bx].
            exact Bx.
        +   rewrite A'_eq.
            exact B'_closed.
        +   rewrite B'_eq.
            exact A'_closed.
        +   rewrite A'_eq.
            apply empty_eq.
            intros x [nBx Bx]; contradiction.
        +   rewrite B'_eq.
            apply union_compl_all.
Qed.

Theorem sub_connected2 : ∀ (X : U → Prop) (A B : set_type X → Prop),
    separation A B → sub_separation X (from_set_type A) (from_set_type B).
Proof.
    intros X A B [A_empty [B_empty [A_open [B_open [AB_dis AB_all]]]]].
    assert (A = 𝐂 B) as A_eq.
    {
        apply antisym.
        -   intros x Ax Bx.
            unfold disjoint in AB_dis.
            assert ((A ∩ B) x) as x_in by (split; assumption).
            rewrite AB_dis in x_in.
            exact x_in.
        -   intros x nBx.
            assert (all x) as x_in by exact true.
            rewrite <- AB_all in x_in.
            destruct x_in as [Ax|Bx].
            +   exact Ax.
            +   contradiction.
    }
    assert (B = 𝐂 A) as B_eq.
    {
        rewrite A_eq.
        rewrite compl_compl.
        reflexivity.
    }
    assert (closed A) as A_closed.
    {
        unfold closed.
        rewrite <- B_eq.
        exact B_open.
    }
    assert (closed B) as B_closed.
    {
        unfold closed.
        rewrite <- A_eq.
        exact A_open.
    }
    unfold disjoint in AB_dis.
    repeat split.
    -   apply empty_neq.
        apply empty_neq in A_empty.
        destruct A_empty as [x Ax].
        exists [x|].
        exists x.
        split; trivial.
    -   apply empty_neq.
        apply empty_neq in B_empty.
        destruct B_empty as [x Bx].
        exists [x|].
        exists x.
        split; trivial.
    -   apply empty_eq.
        intros x [[[x1 Xx1] [x1_eq Ax]] [[x2 Xx2] [x2_eq Bx]]].
        cbn in *.
        subst x1 x2.
        rewrite (proof_irrelevance Xx1 Xx2) in Ax.
        assert (∅ [x|Xx2]) as x_in.
        {
            rewrite <- AB_dis.
            split; assumption.
        }
        exact x_in.
    -   rewrite from_set_type_union; trivial.
    -   assert (from_set_type A ⊆ X) as sub.
        {
            intros x' [[x Xx] [x_eq Ax]]; subst x'.
            exact Xx.
        }
        pose proof (subspace_closure X (from_set_type A) sub) as eq.
        rewrite to_from_set_type in eq.
        assert (closure A ∩ B = ∅) as AB_eq.
        {
            rewrite <- (closure_eq_if_closed _ A_closed).
            exact AB_dis.
        }
        intros x' x_lim [x [x'_eq Bx]]; subst x'.
        assert ((closure A ∩ B) x) as x_in.
        {
            split; try exact Bx.
            rewrite closure_limit_points.
            right.
            rewrite <- (to_from_set_type X A).
            exact (subspace_limit_point _ _ _ sub x_lim).
        }
        rewrite AB_eq in x_in.
        contradiction x_in.
    -   assert (from_set_type B ⊆ X) as sub.
        {
            intros x' [[x Xx] [x_eq Bx]]; subst x'.
            exact Xx.
        }
        pose proof (subspace_closure X (from_set_type B) sub) as eq.
        rewrite to_from_set_type in eq.
        assert (A ∩ closure B = ∅) as AB_eq.
        {
            rewrite <- (closure_eq_if_closed _ B_closed).
            exact AB_dis.
        }
        intros x' x_lim [x [x'_eq Ax]]; subst x'.
        assert ((A ∩ closure B) x) as x_in.
        {
            split; try exact Ax.
            rewrite closure_limit_points.
            right.
            rewrite <- (to_from_set_type X B).
            exact (subspace_limit_point _ _ _ sub x_lim).
        }
        rewrite AB_eq in x_in.
        contradiction x_in.
Qed.

Theorem sub_connected :
    ∀ X, connected (set_type X) ↔ (∀ A B, ¬sub_separation X A B).
Proof.
    intros X.
    split.
    -   intros con A B AB_sep.
        apply sub_connected1 in AB_sep.
        exact (con _ _ AB_sep).
    -   intros con A B AB_sep.
        apply sub_connected2 in AB_sep.
        exact (con _ _ AB_sep).
Qed.

Theorem connected_sub_separation :
    ∀ A B X, separation A B → connected (set_type X) → X ⊆ A ∨ X ⊆ B.
Proof.
    intros A B X [A_empty [B_empty [A_open [B_open [AB_dis AB_all]]]]] X_con.
    specialize (X_con (to_set_type X A) (to_set_type X B)).
    unfold separation in X_con.
    repeat rewrite not_and in X_con.
    do 2 rewrite not_not in X_con.
    destruct X_con
        as [A'_empty|[B'_empty|[A'_open|[B'_open|[AB'_disjoint|AB'_all]]]]].
    -   right.
        intros x Xx.
        assert (all x) as ABx by exact true.
        rewrite <- AB_all in ABx.
        destruct ABx as [Ax|Bx].
        +   assert (to_set_type X A [x|Xx]) as x_in by exact Ax.
            rewrite A'_empty in x_in.
            contradiction x_in.
        +   exact Bx.
    -   left.
        intros x Xx.
        assert (all x) as ABx by exact true.
        rewrite <- AB_all in ABx.
        destruct ABx as [Ax|Bx].
        +   exact Ax.
        +   assert (to_set_type X B [x|Xx]) as x_in by exact Bx.
            rewrite B'_empty in x_in.
            contradiction x_in.
    -   pose proof (subspace_open X A A_open).
        contradiction.
    -   pose proof (subspace_open X B B_open).
        contradiction.
    -   apply empty_neq in AB'_disjoint.
        destruct AB'_disjoint as [[x Xx] [Ax Bx]].
        assert ((A ∩ B) x) as x_in by (split; assumption).
        unfold disjoint in AB_dis.
        rewrite AB_dis in x_in.
        contradiction x_in.
    -   apply all_neq in AB'_all.
        destruct AB'_all as [[x Xx] ABx].
        unfold union in ABx.
        rewrite not_or in ABx.
        destruct ABx as [Ax Bx].
        assert (all x) as x_in by exact true.
        rewrite <- AB_all in x_in.
        destruct x_in; contradiction.
Qed.

Theorem to_set_type_connected : ∀ A B, A ⊆ B →
    connected (set_type A) → connected (set_type (to_set_type B A)).
Proof.
    intros A B sub A_con C D
        [C_empty [D_empty [C_open [D_open [CD_dis CD_all]]]]].
    apply (A_con (to_set_type A (from_set_type (from_set_type C)))
                 (to_set_type A (from_set_type (from_set_type D)))).
    repeat split.
    -   apply empty_neq.
        apply empty_neq in C_empty.
        destruct C_empty as [x Cx].
        pose proof [|x] as Ax.
        unfold to_set_type in Ax.
        exists [_|Ax].
        exists [x|].
        split; try reflexivity.
        exists x.
        split; trivial.
    -   apply empty_neq.
        apply empty_neq in D_empty.
        destruct D_empty as [x Dx].
        pose proof [|x] as Ax.
        unfold to_set_type in Ax.
        exists [_|Ax].
        exists [x|].
        split; try reflexivity.
        exists x.
        split; trivial.
    -   destruct C_open as [C' [C'_open C_eq]].
        destruct C'_open as [C'' [C''_open C'_eq]].
        exists C''.
        split; try exact C''_open.
        rewrite C_eq.
        rewrite C'_eq.
        apply antisym.
        +   intros x [x' [x'_eq [x'' [x''_eq Cx]]]].
            unfold to_set_type.
            rewrite x'_eq.
            rewrite x''_eq.
            exact Cx.
        +   intros [x Ax] Cx.
            unfold to_set_type at 1.
            exists [_|sub _ Ax].
            split; try reflexivity.
            unfold from_set_type at 1.
            assert (to_set_type B A [_|sub _ Ax]) as Ax' by exact Ax.
            exists [_|Ax']; cbn.
            split; trivial.
    -   destruct D_open as [D' [D'_open D_eq]].
        destruct D'_open as [D'' [D''_open D'_eq]].
        exists D''.
        split; try exact D''_open.
        rewrite D_eq.
        rewrite D'_eq.
        apply antisym.
        +   intros x [x' [x'_eq [x'' [x''_eq Dx]]]].
            unfold to_set_type.
            rewrite x'_eq.
            rewrite x''_eq.
            exact Dx.
        +   intros [x Ax] Dx.
            unfold to_set_type at 1.
            exists [_|sub _ Ax].
            split; try reflexivity.
            unfold from_set_type at 1.
            assert (to_set_type B A [_|sub _ Ax]) as Ax' by exact Ax.
            exists [_|Ax']; cbn.
            split; trivial.
    -   apply empty_eq.
        intros [x Ax] [Cx Dx].
        unfold disjoint in CD_dis.
        assert (to_set_type B A [x|sub x Ax]) as Ax' by exact Ax.
        assert ((C ∩ D) [_|Ax']) as x_in.
        {
            split.
            -   destruct Cx as [x' [eq1 [x'' [eq2 Cx'']]]]; cbn in *.
                subst.
                destruct x'' as [[x'' Bx'] Ax''].
                cbn.
                rewrite (proof_irrelevance _ Bx').
                rewrite (proof_irrelevance _ Ax'').
                exact Cx''.
            -   destruct Dx as [x' [eq1 [x'' [eq2 Dx'']]]]; cbn in *.
                subst.
                destruct x'' as [[x'' Bx'] Ax''].
                cbn.
                rewrite (proof_irrelevance _ Bx').
                rewrite (proof_irrelevance _ Ax'').
                exact Dx''.
        }
        rewrite CD_dis in x_in.
        exact x_in.
    -   apply antisym; try apply all_sub.
        intros x C0; clear C0.
        assert (to_set_type B A [_|sub _ [|x]]) as Ax by exact [|x].
        assert (all [_|Ax]) as x_in by exact true.
        rewrite <- CD_all in x_in.
        destruct x_in as [Cx|Dx].
        +   left.
            exists [_ | sub _ [|x]].
            split; try reflexivity.
            destruct x as [x Ax']; cbn in *.
            exists [_|Ax].
            split; trivial.
        +   right.
            exists [_ | sub _ [|x]].
            split; try reflexivity.
            destruct x as [x Ax']; cbn in *.
            exists [_|Ax].
            split; trivial.
Qed.

(* begin hide *)
End Connected.
Section Connected.

Context {U} `{Topology U}.
Existing Instance subspace_topology.
(* end hide *)
Theorem empty_connected : connected (set_type ∅).
Proof.
    intros A B [A_empty AB].
    apply empty_neq in A_empty.
    destruct A_empty as [[x x_in]].
    exact x_in.
Qed.

Theorem connected_union_connected : ∀ (SS : (U → Prop) → Prop) x,
   (∀ S, SS S → connected (set_type S) ∧ S x) → connected (set_type (⋃ SS)).
Proof.
    intros SS x all_SS.
    classic_case (⋃ SS = ∅) as [SS_empty|SS_nempty].
    {
        rewrite SS_empty.
        exact empty_connected.
    }
    apply empty_neq in SS_nempty.
    destruct SS_nempty as [x' [E [SSE Ex']]].
    pose proof (all_SS E SSE) as [E_con Ex].
    assert ((⋃ SS) x) as x_in.
    {
        exists E.
        split; assumption.
    }
    assert (∀ A B : (set_type (⋃ SS)) → Prop, A [x|x_in] → ¬(separation A B))
        as wlog.
    {
        intros A B Ax AB_sep.
        assert (∀ S, SS S → to_set_type (⋃ SS) S ⊆ A) as sub.
        {
            intros S SS_S a Sa.
            assert (S ⊆ ⋃ SS) as S_sub.
            {
                intros y Sy.
                exists S.
                split; assumption.
            }
            apply all_SS in SS_S as [S_con Sx].
            apply (to_set_type_connected S (⋃ SS) S_sub) in S_con.
            destruct (connected_sub_separation
                    A B (to_set_type (⋃ SS) S) AB_sep S_con) as [sub_A|sub_B].
            -   apply sub_A.
                exact Sa.
            -   assert ((A ∩ B) [x|x_in]) as x_in2.
                {
                    split; try exact Ax.
                    apply sub_B.
                    exact Sx.
                }
                pose proof (land (rand (rand (rand (rand AB_sep)))))
                    as AB_dis.
                unfold disjoint in AB_dis.
                rewrite AB_dis in x_in2.
                contradiction x_in2.
        }
        apply (land (rand AB_sep)).
        apply empty_eq.
        intros a Ba.
        pose proof [|a] as [S [SS_S Sa]].
        specialize (sub _ SS_S _ Sa).
        pose proof (land (rand (rand (rand (rand AB_sep))))) as AB_dis.
        unfold disjoint in AB_dis.
        assert ((A ∩ B) a) as a_in by (split; assumption).
        rewrite AB_dis in a_in.
        exact a_in.
    }
    intros A B [A_empty [B_empty [A_open [B_open [AB_dis AB_all]]]]].
    assert (all [x|x_in]) as x_in2 by exact true.
    rewrite <- AB_all in x_in2.
    destruct x_in2 as [Ax|Bx].
    -   apply (wlog A B Ax).
        repeat split; assumption.
    -   apply (wlog B A Bx).
        unfold separation, disjoint.
        repeat split; try rewrite inter_comm; try rewrite union_comm; assumption.
Qed.

Theorem connected_union_connected2 : ∀ (A B : U → Prop) x,
    A x → B x → connected (set_type A) → connected (set_type B) →
    connected (set_type (A ∪ B)).
Proof.
    intros A B x Ax Bx a_con B_con.
    rewrite collection2_union.
    apply (connected_union_connected _ x).
    intros S [SA|SB]; subst; split; assumption.
Qed.

Theorem sub_separation_closure_disjoint : ∀ X A B, sub_separation X A B →
    disjoint (closure A) B.
Proof.
    intros X A B [A_empty [B_empty [AB_dis [AB_X [A_lim B_lim]]]]].
    unfold disjoint.
    rewrite closure_limit_points.
    rewrite inter_rdist.
    apply empty_eq.
    intros x [ABx|[Ax Bx]].
    -   unfold disjoint in AB_dis.
        rewrite AB_dis in ABx.
        exact ABx.
    -   exact (A_lim x Ax Bx).
Qed.

Theorem connected_in_closure : ∀ A B, connected (set_type A) →
    A ⊆ B → B ⊆ closure A → connected (set_type B).
Proof.
    intros A B A_con AB BA.
    assert (∀ C D, to_set_type B A ⊆ C → ¬separation C D) as wlog.
    {
        intros C D sub CD_sep.
        pose proof CD_sep as CD_dis.
        apply sub_connected2 in CD_dis.
        apply sub_separation_closure_disjoint in CD_dis.
        apply (to_from_set_type_sub _ _ _ AB) in sub.
        apply closure_sub_closure in sub.
        pose proof (trans BA sub) as leq.
        unfold disjoint in CD_dis.
        pose proof (rand (rand (rand (rand (rand CD_sep))))) as eq.
        apply from_set_type_union in eq.
        rewrite <- eq in leq at 1; clear eq.
        pose proof (land (rand CD_sep)) as D_empty.
        apply empty_neq in D_empty.
        destruct D_empty as [[x Bx] Dx].
        assert (from_set_type D x) as x_in.
        {
            exists [x|Bx].
            split; trivial.
        }
        assert ((from_set_type C ∪ from_set_type D) x) as x_in2
            by (right; exact x_in).
        apply leq in x_in2.
        assert ((closure (from_set_type C) ∩ from_set_type D) x) as x_in3
            by (split; assumption).
        rewrite CD_dis in x_in3.
        exact x_in3.
    }
    intros C D CD_sep.
    apply (to_set_type_connected A B AB) in A_con.
    pose proof (connected_sub_separation C D (to_set_type B A) CD_sep A_con)
        as [sub|sub].
    -   exact (wlog _ _ sub CD_sep).
    -   apply separation_comm in CD_sep.
        exact (wlog _ _ sub CD_sep).
Qed.
(* begin hide *)
End Connected.
(* end hide *)
