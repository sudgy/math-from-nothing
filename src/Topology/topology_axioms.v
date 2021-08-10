Require Import init.

Require Export topology_base.

(* begin hide *)
Open Scope set_scope.
(* end hide *)
Class HausdorffSpace U `{Topology U} := {
    hausdorff_space : ∀ x1 x2, x1 ≠ x2 →
        ∃ S1 S2, open S1 ∧ open S2 ∧ S1 x1 ∧ S2 x2 ∧ disjoint S1 S2
}.
(* begin hide *)
Close Scope set_scope.
(* end hide *)
