Require Import init.

Require Export topology_base.
Require Export topology_order.
Require Export topology_continuous.
Require Export topology_connected.
Require Export topology_real.

(* begin hide *)
Section Path.

Existing Instance real_order_topology.
Existing Instance subspace_topology.
(* end hide *)
Definition p0 : set_type (closed_interval 0 1)
    := [0 | make_and (refl _) (land one_pos)].
Definition p1 : set_type (closed_interval 0 1)
    := [1 | make_and (land one_pos) (refl _)].

Definition path {U} `{Topology U} x y (f : set_type (closed_interval 0 1) → U)
    := continuous f ∧ f p0 = x ∧ f p1 = y.

Definition path_connected U `{Topology U} := ∀ x y, ∃ f, path x y f.

(* begin hide *)
Context {U} `{Topology U}.
(* end hide *)
Theorem path_connected_connected : path_connected U → connected U.
Proof.
    intros U_path A B AB_sep.
    pose proof (land AB_sep) as A_empty.
    pose proof (land (rand AB_sep)) as B_empty.
    pose proof (land (rand (rand (rand (rand AB_sep))))) as AB_dis.
    unfold disjoint in AB_dis.
    apply not_empty_ex in A_empty, B_empty.
    destruct A_empty as [a Aa], B_empty as [b Bb].
    specialize (U_path a b) as [f [f_cont [fa fb]]].
    apply continuous_connected_image in f_cont.
    2: apply closed_interval_connected.
    pose proof (connected_sub_separation _ _ _ AB_sep f_cont) as [sub_A|sub_B].
    -   assert (∅ b) as contr.
        {
            rewrite <- AB_dis.
            split; try exact Bb.
            apply sub_A.
            exists p1.
            symmetry; exact fb.
        }
        exact contr.
    -   assert (∅ a) as contr.
        {
            rewrite <- AB_dis.
            split; try exact Aa.
            apply sub_B.
            exists p0.
            symmetry; exact fa.
        }
        exact contr.
Qed.

(* begin hide *)
End Path.
(* end hide *)
