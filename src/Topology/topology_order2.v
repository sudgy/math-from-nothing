Require Import init.

Require Export topology_order.
Require Import topology_continuous.
Require Import topology_connected.
Require Import topology_subspace.

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
    Dense U lt,
    NotTrivial U
}.

(* begin hide *)
Existing Instance order_topology.
Existing Instance subspace_topology.
(* end hide *)
Theorem complete_connected : connected U.
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
    -   intros y.
        exists [y|true].
        reflexivity.
    -   apply convex_connected.
        intros a b C0 C1; clear C0 C1.
        intros x x_in.
        exact true.
Qed.

(* begin hide *)
End OrderTopology.
(* end hide *)
