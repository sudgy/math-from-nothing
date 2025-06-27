Require Import init.

Require Export group_category.
Require Export group_subgroup.

Require Import set.
Require Export card.
Require Import card_types.
Require Export int.

Require Import mult_div.
Require Import nat_domain.

Section CyclicGroup.

Local Open Scope int_scope.

Context {G : Group} (a : G).

Definition cyclic_set (x : G) := ∃ n : int, x = n × a.

Program Definition cyclic_Subgroup := {|subgroup_set := cyclic_set|}.
Next Obligation.
    exists 0.
    rewrite int_mult_lanni.
    reflexivity.
Qed.
Next Obligation.
    destruct H as [m m_eq], H0 as [n n_eq].
    exists (m + n).
    rewrite int_mult_rdist.
    rewrite m_eq, n_eq.
    reflexivity.
Qed.
Next Obligation.
    destruct H as [n n_eq].
    exists (-n).
    rewrite n_eq.
    apply int_mult_lneg.
Qed.

Definition cyclic_subgroup := subgroup cyclic_Subgroup : Group.

Local Open Scope card_scope.

Definition group_order := |cyclic_subgroup|.

Theorem group_order_countable : group_order ≤ |nat|.
Proof.
    unfold group_order.
    rewrite <- int_size.
    unfold le; equiv_simpl.
    exists (λ (x : set_type cyclic_set), ex_val [|x]).
    split.
    intros [x x'] [y y']; cbn.
    rewrite_ex_val m m_eq.
    rewrite_ex_val n n_eq.
    subst x y.
    intro; subst.
    apply set_type_refl.
Qed.

(** Proving that this definition is equivalent to the usual definition requires
proving that the integers are a Euclidean domain which I haven't done yet *)

End CyclicGroup.
