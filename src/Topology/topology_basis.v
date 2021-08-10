Require Import init.

Require Export topology_base.

(* begin hide *)
Open Scope card_scope.
Open Scope set_scope.
(* end hide *)
#[universes(template)]
Class TopologyBasis U := {
    top_basis : (U → Prop) → Prop;
    top_basis_in : ∀ x, ∃ B, top_basis B ∧ B x;
    top_basis_int : ∀ x B1 B2, top_basis B1 → top_basis B2 → B1 x → B2 x →
        ∃ B3, top_basis B3 ∧ B3 x ∧ B3 ⊆ (B1 ∩ B2);
}.

Program Instance basis_topology {U} `{b:TopologyBasis U} : Topology U :={
    open S := ∀ x, S x → ∃ B, top_basis B ∧ B x ∧ B ⊆ S
}.
Next Obligation.
    contradiction H.
Qed.
Next Obligation.
    clear H.
    pose proof (top_basis_in x) as [B [B_basis Bx]].
    exists B.
    repeat split; assumption.
Qed.
Next Obligation.
    rename H into sub.
    rename H0 into s.
    rename H1 into Ss.
    rename H2 into sx.
    unfold subset in sub; cbn in sub.
    specialize (sub s Ss x sx) as [B [B_basis [Bx Bs]]].
    exists B.
    repeat split; try assumption.
    intros y By.
    exists s.
    split; try assumption.
    apply Bs.
    exact By.
Qed.
Next Obligation.
    rename H into sub.
    rename H0 into S_fin.
    rename H1 into x_in_int.
    apply fin_nat0_ex in S_fin.
    destruct S_fin as [n S_fin].
    revert S sub S_fin x x_in_int.
    nat0_induction n.
    -   intros.
        destruct (top_basis_in x) as [B [B_basis Bx]].
        exists B.
        repeat split; try assumption.
        intros y By A SA.
        exfalso.
        clear - S_fin SA.
        symmetry in S_fin.
        rewrite card_0_false in S_fin.
        apply S_fin.
        exact [A|SA].
    -   intros.
        assert (set_type S) as T.
        {
            clear - S_fin.
            classic_contradiction contr.
            rewrite <- card_0_false in contr.
            rewrite contr in S_fin.
            apply nat0_to_card_eq in S_fin.
            inversion S_fin.
        }
        symmetry in S_fin.
        pose proof (card_plus_one_nat0 S n T S_fin) as S'_fin.
        remember (S - singleton [T|]) as S'.
        symmetry in S'_fin.
        assert (S' ⊆ (λ S0, ∀ x, S0 x → ∃ B, top_basis B ∧ B x ∧ B ⊆ S0))
            as sub2.
        {
            apply (trans2 sub).
            intros s S's.
            rewrite HeqS' in S's.
            apply S's.
        }
        assert (∀ A, S' A → A x) as x_in_int'.
        {
            intros A S'A.
            apply x_in_int.
            rewrite HeqS' in S'A.
            apply S'A.
        }
        specialize (IHn S' sub2 S'_fin x x_in_int')
            as [B1 [B1_basis [B1x B1_sub]]].
        destruct T as [T ST].
        cbn in HeqS'.
        assert (T x) as Tx.
        {
            apply x_in_int.
            exact ST.
        }
        apply sub in ST.
        specialize (ST x Tx) as [B2 [B2_basis [B2x B2_sub]]].
        pose proof (top_basis_int x B1 B2 B1_basis B2_basis B1x B2x)
            as [B3 [B3_basis [B3x B3_sub]]].
        exists B3.
        repeat split; try assumption.
        intros y B3y A SA.
        apply B3_sub in B3y.
        destruct B3y as [B1y B2y].
        apply B1_sub in B1y.
        apply B2_sub in B2y.
        classic_case (A = T) as [AT|AT_neq].
        +   rewrite AT.
            exact B2y.
        +   apply B1y.
            rewrite HeqS'.
            split.
            *   exact SA.
            *   rewrite neq_sym in AT_neq.
                exact AT_neq.
Qed.

(* begin hide *)
Section Basis.

Context {U} `{TopologyBasis U}.
(* end hide *)
Theorem basis_open : ∀ B, top_basis B → open B.
    intros B B_basis x Bx.
    exists B.
    repeat split; try assumption.
    apply refl.
Qed.

Let open' S := ∃ (SS : (U → Prop) → Prop), (∀ T, SS T → top_basis T) ∧ ⋃ SS = S.

Theorem basis_open_unions : open = open'.
    apply predicate_ext.
    intros S.
    unfold open, open'; cbn.
    split.
    -   intros S_open.
        pose (SS T := ∃ x, T = ex_val (S_open [x|] [|x])).
        exists SS.
        split.
        +   intros T SST.
            destruct SST as [x T_eq].
            rewrite_ex_val T' [T_basis [Tx T_sub]].
            subst T'.
            exact T_basis.
        +   apply predicate_ext.
            intros x.
            split.
            *   intros [T [[y T_eq] Tx]].
                rewrite_ex_val T' [T_basis [Ty T_sub]].
                subst T'.
                apply T_sub.
                exact Tx.
            *   intros Sx.
                exists (ex_val (S_open x Sx)).
                split.
                --  exists [x|Sx].
                    cbn.
                    reflexivity.
                --  rewrite_ex_val a aH.
                    apply aH.
    -   intros [SS [SS_basis SS_S]].
        intros x Sx.
        subst S.
        destruct Sx as [B [SSB Bx]].
        exists B.
        repeat split.
        +   apply SS_basis.
            exact SSB.
        +   exact Bx.
        +   intros a Ba.
            exists B.
            split; assumption.
Qed.

Theorem open_all_basis :
        ∀ A : U → Prop, (∀ x, A x → ∃ S, top_basis S ∧ S x ∧ S ⊆ A) ↔ open A.
    clear open'.
    intros A.
    split.
    -   intros all_x.
        apply open_all_neigh.
        intros x Ax.
        specialize (all_x x Ax) as [S [S_basis [Sx S_sub]]].
        exists S.
        repeat split.
        +   apply basis_open.
            exact S_basis.
        +   exact Sx.
        +   exact S_sub.
    -   intros A_open x Ax.
        destruct (A_open x Ax) as [B [B_basis [Bx B_sub]]].
        exists B.
        repeat split; assumption.
Qed.

(* begin hide *)
End Basis.

Section MakeBasis.

Context {U} `{top : Topology U}.
Variable C : (U → Prop) → Prop.
Hypothesis C_open : C ⊆ open.
Hypothesis C_contains : ∀ S x, open S → S x → ∃ B, C B ∧ B ⊆ S ∧ B x.

Program Instance make_basis_topology : TopologyBasis U := {
    top_basis := C
}.
Next Obligation.
    specialize (C_contains all x all_open true) as [B [CB [B_sub Bx]]].
    exists B.
    split; assumption.
Qed.
Next Obligation.
    rename H into CB1, H0 into CB2, H1 into B1x, H2 into B2x.
    apply C_open in CB1, CB2.
    pose proof (inter_open2 _ _ CB1 CB2) as B12_open.
    assert ((B1 ∩ B2) x) as B12x by (split; assumption).
    specialize (C_contains _ _ B12_open B12x) as [B [CB [sub Bx]]].
    exists B.
    split.
    2: split.
    all: assumption.
Qed.

Theorem make_basis_equal : basis_topology = top.
    apply topology_equal.
    intros S.
    split.
    -   rewrite basis_open_unions.
        intros [SS [SS_basis S_union]].
        rewrite <- S_union.
        apply union_open.
        intros B SSB.
        specialize (SS_basis B SSB).
        apply C_open.
        exact SS_basis.
    -   unfold open at 2; cbn.
        intros S_open x Sx.
        pose proof (C_contains S x S_open Sx) as [B [CB [sub Bx]]].
        exists B.
        repeat split; assumption.
Qed.

(* begin hide *)
End MakeBasis.
(* end hide *)
Theorem topology_basis_equal : ∀U (T1 : TopologyBasis U) (T2 : TopologyBasis U),
        (∀ S, @top_basis U T1 S ↔ @top_basis U T2 S) → T1 = T2.
    intros U [T1 T1_in T1_int] [T2 T2_in T2_int] S.
    apply predicate_ext in S.
    unfold top_basis in S; cbn in S.
    subst.
    rewrite (proof_irrelevance T1_in T2_in).
    rewrite (proof_irrelevance T1_int T2_int).
    reflexivity.
Qed.

Theorem topology_basis_finer {U} : ∀ (T1 T2 : TopologyBasis U),
        topology_finer (@basis_topology U T1) (@basis_topology U T2) ↔
        ∀ x B2, @top_basis U T2 B2 → B2 x →
        ∃ B1, @top_basis U T1 B1 ∧ B1 x ∧ B1 ⊆ B2.
    intros T1 T2.
    unfold topology_finer; cbn.
    split.
    -   intros finer x B2 B2_b B2x.
        pose proof (basis_open _ B2_b) as B2_open.
        apply finer in B2_open.
        unfold open in B2_open; cbn in B2_open.
        specialize (B2_open x B2x).
        exact B2_open.
    -   intros finer B2 B2_open.
        unfold open; cbn.
        intros x B2x.
        unfold open in B2_open; cbn in B2_open.
        specialize (B2_open x B2x) as [B2' [B2'_basis [B2'x B2'_sub]]].
        specialize (finer x B2' B2'_basis B2'x) as [B1 [B1_basis [B1x B1_sub]]].
        exists B1.
        repeat split.
        +   exact B1_basis.
        +   exact B1x.
        +   exact (trans B1_sub B2'_sub).
Qed.
(* begin hide *)
Close Scope set_scope.
Close Scope card_scope.
(* end hide *)
