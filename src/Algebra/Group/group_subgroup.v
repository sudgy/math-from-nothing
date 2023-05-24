Require Import init.

Require Export group_category.

Require Import set.

Record Subgroup (G : Group) := make_subgroup {
    subgroup_set : G → Prop;
    subgroup_zero : subgroup_set 0;
    subgroup_plus : ∀ a b, subgroup_set a → subgroup_set b → subgroup_set (a+b);
    subgroup_neg : ∀ a, subgroup_set a → subgroup_set (-a);
}.

Arguments subgroup_set {G}.
Arguments subgroup_zero {G}.
Arguments subgroup_plus {G}.
Arguments subgroup_neg {G}.

Section SubgroupGroup.

Context {G : Group} (S : Subgroup G).

Let U := set_type (subgroup_set S).

Local Instance subgroup_plus_class : Plus U := {
    plus a b := [[a|] + [b|] | subgroup_plus S [a|] [b|] [|a] [|b]]
}.
Local Instance subgroup_zero_class : Zero U := {
    zero := [_ | subgroup_zero S]
}.
Local Instance subgroup_neg_class : Neg U := {
    neg a := [-[a|] | subgroup_neg S [a|] [|a]]
}.
Local Instance subgroup_plus_assoc : PlusAssoc U.
Proof.
    split.
    intros a b c.
    apply set_type_eq.
    apply plus_assoc.
Qed.
Local Instance subgroup_plus_lid : PlusLid U.
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply plus_lid.
Qed.
Local Instance subgroup_plus_rid : PlusRid U.
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply plus_rid.
Qed.
Local Instance subgroup_plus_linv : PlusLinv U.
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply plus_linv.
Qed.
Local Instance subgroup_plus_rinv : PlusRinv U.
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply plus_rinv.
Qed.

Definition subgroup := make_group _ subgroup_plus_class subgroup_zero_class
    subgroup_neg_class subgroup_plus_assoc subgroup_plus_lid subgroup_plus_rid
    subgroup_plus_linv subgroup_plus_rinv.

End SubgroupGroup.
