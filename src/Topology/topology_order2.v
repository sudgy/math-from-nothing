Require Import init.

Require Export topology_order.
Require Import topology_continuous.
Require Import topology_connected.
Require Import topology_subspace.
Require Import topology_subbasis.

(* begin hide *)
Section OrderTopology.
(* end hide *)
Context {U} `{
    Order U,
    Reflexive U le,
    Connex U le,
    Antisymmetric U le,
    Transitive U le,
    SupremumComplete U le,
    Dense U (strict le),
    NotTrivial U
}.

(* begin hide *)
Existing Instance order_topology.
Existing Instance subspace_topology.
(* end hide *)
Theorem complete_connected : connected U.
Proof.
    pose (f (x : set_type (@all U)) := [x|]).
    apply (continuous_connected f).
    -   intros x T T_neigh.
        exists (λ a, T [a|]).
        split.
        +   destruct T_neigh as [T_open Tfx].
            split.
            *   unfold open; cbn.
                exists T.
                split; try exact T_open.
                reflexivity.
            *   exact Tfx.
        +   intros y [y' [Ty eq]].
            rewrite eq; exact Ty.
    -   split.
        intros y.
        exists [y|true].
        reflexivity.
    -   apply convex_connected.
        intros a b C0 C1; clear C0 C1.
        intros x x_in.
        exact true.
Qed.

Local Program Instance order_subbasis : TopologySubbasis U := {
    top_subbasis S := ∃ a, ❴inf_open_interval a, open_inf_interval a❵ S
}.
Next Obligation.
    apply all_eq.
    intros x.
    pose proof (not_trivial2 x) as [y neq].
    destruct (trichotomy x y) as [[ltq|eq]|ltq]; [>|contradiction|].
    -   exists (inf_open_interval y).
        split.
        +   exists y.
            left.
            reflexivity.
        +   exact ltq.
    -   exists (open_inf_interval y).
        split.
        +   exists y.
            right.
            reflexivity.
        +   exact ltq.
Qed.

Theorem order_subbasis_eq :
    @basis_topology U order_topology = @basis_topology U subbasis_topology.
Proof.
    apply topology_finer_antisym.
    -   apply subbasis_finer.
        intros S [a S_eq].
        destruct S_eq; subst S.
        +   apply inf_open_interval_open.
        +   apply open_inf_interval_open.
    -   apply basis_finer.
        intros S S_basis.
        destruct S_basis as [S_basis|[S_basis|S_basis]].
        +   destruct S_basis as [a [b S_eq]].
            assert (S = inf_open_interval b ∩ open_inf_interval a) as S_eq2.
            {
                subst S.
                apply antisym; intros x [x_lt x_gt]; split; assumption.
            }
            rewrite S_eq2.
            apply inter_open2.
            *   apply subbasis_open.
                exists b.
                left; reflexivity.
            *   apply subbasis_open.
                exists a.
                right; reflexivity.
        +   destruct S_basis as [a [b [S_eq b_max]]]; subst S.
            apply subbasis_open.
            exists a.
            right.
            apply antisym.
            *   intros x x_lt.
                split.
                --  exact x_lt.
                --  apply b_max.
            *   intros x x_lt.
                apply x_lt.
        +   destruct S_basis as [a [b [S_eq a_min]]]; subst S.
            apply subbasis_open.
            exists b.
            left.
            apply antisym.
            *   intros x x_lt.
                split.
                --  apply a_min.
                --  exact x_lt.
            *   intros x x_lt.
                apply x_lt.
Qed.

(* begin hide *)
End OrderTopology.
(* end hide *)
