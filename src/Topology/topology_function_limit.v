Require Import init.

Require Export topology_limit.
Require Import topology_axioms.
Require Import topology_continuous.

Definition func_lim {U V} `{Topology U, Topology V}
    (A : U → Prop)
    (f : set_type A → V)
    (c : U)
    (l : V)
    :=
    limit_point A c ∧
    ∀ T : V → Prop, neighborhood l T →
        ∃ S : U → Prop, neighborhood c S ∧
            image_under f (λ x, S [x|] ∧ c ≠ [x|]) ⊆ T.

(* begin hide *)
Section TopologyFunction.

Context {U V} `{Topology U, HausdorffSpace V}.

Local Open Scope set_scope.
(* end hide *)
Theorem func_lim_unique : ∀ (A : U → Prop) (f : set_type A → V) c l1 l2,
        func_lim A f c l1 → func_lim A f c l2 → l1 = l2.
    intros A f c l1 l2 [c_lim l1_lim] [c_lim' l2_lim]; clear c_lim'.
    classic_contradiction contr.
    pose proof (hausdorff_space l1 l2 contr)
        as [T1 [T2 [T1_open [T2_open [Tl1 [Tl2 T12]]]]]].
    specialize (l1_lim T1 (make_and T1_open Tl1)) as [S1 [S1c S1_sub]].
    specialize (l2_lim T2 (make_and T2_open Tl2)) as [S2 [S2c S2_sub]].
    specialize (c_lim (S1 ∩ S2)).
    prove_parts c_lim.
    {
        apply inter_open2.
        -   apply S1c.
        -   apply S2c.
    }
    {
        split.
        -   apply S1c.
        -   apply S2c.
    }
    unfold intersects in c_lim.
    apply not_empty_ex in c_lim as [x [[Ax xc] [S1x S2x]]].
    unfold disjoint in T12.
    apply (empty_not_ex _ T12 (f [x|Ax])).
    split.
    -   apply S1_sub.
        exists [x|Ax]; cbn.
        repeat split.
        +   exact S1x.
        +   exact xc.
    -   apply S2_sub.
        exists [x|Ax]; cbn.
        repeat split.
        +   exact S2x.
        +   exact xc.
Qed.

Theorem func_seq_lim : ∀ (A : U → Prop) (f : set_type A → V) c l,
        func_lim A f c l → ∀ xn : nat → set_type (A - singleton c),
        seq_lim (λ n, [xn n|]) c → seq_lim (λ n, f [[xn n|] | land [|xn n]]) l.
    intros A f c l [c_lim cl] xn xn_lim.
    intros T T_open Tl.
    specialize (cl T (make_and T_open Tl)) as [S [[S_open Sc] S_sub]].
    specialize (xn_lim S S_open Sc) as [N xn_lim].
    exists N.
    intros n n_leq.
    specialize (xn_lim n n_leq).
    apply S_sub.
    exists [[xn n|] | land [|xn n]]; cbn.
    repeat split.
    -   exact xn_lim.
    -   apply [|xn n].
Qed.

Theorem func_lim_restrict : ∀ (A : U → Prop) (f : set_type A → V) c l,
        func_lim A f c l → ∀ (B : U → Prop), limit_point (A ∩ B) c →
        func_lim (A ∩ B) (λ x, f [[x|] | land [|x]]) c l.
    intros A f c l [c_lim Af] B c_lim'.
    split; [>exact c_lim'|].
    intros T Tl.
    specialize (Af T Tl) as [S [Sc S_sub]].
    exists S.
    split; [>exact Sc|].
    intros y [[x [Ax Bx]] [[Sx x_neq] y_eq]]; cbn in *.
    apply S_sub.
    exists [x|Ax]; cbn.
    repeat split.
    -   exact Sx.
    -   exact x_neq.
    -   rewrite (proof_irrelevance _ Ax) in y_eq.
        exact y_eq.
Qed.

Theorem func_lim_continuous : ∀ (f : U → V) c, limit_point all c →
        continuous_at f c ↔ func_lim all (λ x, f [x|]) c (f c).
    intros f c c_lim.
    split.
    -   intros f_cont.
        split; [>exact c_lim|].
        intros T T_neigh.
        specialize (f_cont T T_neigh) as [S [Sc S_sub]].
        exists S.
        split; [>exact Sc|].
        intros y [[x C0] [[Sx x_neq] y_eq]]; cbn in *; clear C0.
        apply S_sub.
        exists x.
        split; assumption.
    -   intros [C0 f_lim] T T_neigh; clear C0.
        specialize (f_lim T T_neigh) as [S [S_neigh S_sub]].
        exists S.
        split; [>exact S_neigh|].
        intros y [x [Sx y_eq]].
        classic_case (c = x) as [eq|neq].
        {
            subst x.
            rewrite y_eq.
            apply T_neigh.
        }
        apply S_sub.
        exists [x|true]; cbn.
        repeat split; assumption.
Qed.
(* begin hide *)
End TopologyFunction.

Section BasisFunction.

Context {U V} `{TopologyBasis U, TopologyBasis V}.
(* end hide *)
Theorem basis_func_lim : ∀ (A : U → Prop) (f : set_type A → V) c l,
        limit_point A c → func_lim A f c l ↔
        (∀ T, top_basis T → T l → ∃ S, top_basis S ∧ S c ∧
            image_under f (λ x, S [x|] ∧ c ≠ [x|]) ⊆ T).
    intros A f c l Ac.
    split.
    -   intros [Ac' f_lim] T T_basis Tx; clear Ac'.
        apply basis_open in T_basis.
        specialize (f_lim T (make_and T_basis Tx)) as [S [[S_open Sc] S_sub]].
        specialize (S_open c Sc) as [B [B_basis [Bc B_sub]]].
        exists B.
        repeat split; [>exact B_basis|exact Bc|].
        intros y [[x Ax] [[Bx c_neq] y_eq]]; cbn in *.
        apply S_sub.
        exists [x|Ax]; cbn.
        repeat split.
        +   apply B_sub.
            exact Bx.
        +   exact c_neq.
        +   exact y_eq.
    -   intros all_T.
        split; [>exact Ac|].
        intros T [T_open Tl].
        specialize (T_open l Tl) as [B [B_basis [Bl B_sub]]].
        specialize (all_T B B_basis Bl) as [S [S_basis [Sc S_sub]]].
        exists S.
        split.
        +   split; [>|exact Sc].
            apply basis_open.
            exact S_basis.
        +   apply (trans S_sub).
            exact B_sub.
Qed.
(* begin hide *)
End BasisFunction.
(* end hide *)
