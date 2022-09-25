Require Import init.

Require Import zorn_real_base.

Require Import nat.
Require Import rat.
Require Import set.
Require Import card.
Require Import card_types.

Section AOFEx.

Context {U} `{
    UP : Plus U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    UZ : Zero U,
    @PlusLid U UP UZ,
    UN : Neg U,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    @MultComm U UM,
    @MultAssoc U UM,
    @Ldist U UP UM,
    UE : One U,
    @MultLid U UM UE,
    UO : Order U,
    @Antisymmetric U le,
    @Transitive U le,
    @Connex U le,
    @OrderLplus U UP UO,
    @OrderMult U UZ UM UO,
    NotTrivial U,
    UD : Div U,
    @MultLinv U UZ UM UE UD,
    @Archimedean U UP UZ UO
}.

Lemma aof_ex_ex : ∃ f : U → (nat → Prop), injective f.
Proof.
    pose proof arch_ordered_size as f_ex.
    rewrite <- power_set_size in f_ex.
    unfold le in f_ex; equiv_simpl in f_ex.
    exact f_ex.
Qed.

Definition aof_ex_f_base := ex_val aof_ex_ex.

Definition aof_ex_set := image aof_ex_f_base.

Theorem aof_ex_f_in : ∀ x, aof_ex_set (aof_ex_f_base x).
Proof.
    intros x.
    exists x.
    reflexivity.
Qed.

Definition aof_ex_f (x : U)
    := [aof_ex_f_base x|aof_ex_f_in x] : set_type aof_ex_set.

Theorem aof_ex_f_inj : injective aof_ex_f.
Proof.
    intros a b eq.
    apply set_type_eq in eq; cbn in eq.
    apply (ex_proof aof_ex_ex) in eq.
    exact eq.
Qed.

Theorem aof_ex_f_sur : surjective aof_ex_f.
Proof.
    intros [y [x eq]].
    exists x.
    apply set_type_eq; cbn.
    symmetry; exact eq.
Qed.

Theorem aof_ex_f_bij : bijective aof_ex_f.
Proof.
    split; [>exact aof_ex_f_inj|exact aof_ex_f_sur].
Qed.

Definition aof_ex_f_inv := bij_inv aof_ex_f aof_ex_f_bij.

Theorem aof_ex_f_eq1 : ∀ x, aof_ex_f_inv (aof_ex_f x) = x.
Proof.
    apply inverse_eq1.
    apply bij_inv_inv.
Qed.
Theorem aof_ex_f_eq2 : ∀ x, aof_ex_f (aof_ex_f_inv x) = x.
Proof.
    apply inverse_eq2.
    apply bij_inv_inv.
Qed.

Global Instance aof_ex_plus : Plus (set_type aof_ex_set) := {
    plus a b := aof_ex_f (aof_ex_f_inv a + aof_ex_f_inv b)
}.
Global Instance aof_ex_zero : Zero (set_type aof_ex_set) := {
    zero := aof_ex_f 0
}.
Global Instance aof_ex_neg : Neg (set_type aof_ex_set) := {
    neg a := aof_ex_f (-aof_ex_f_inv a)
}.
Global Program Instance aof_ex_plus_comm : PlusComm (set_type aof_ex_set).
Next Obligation.
    unfold plus; cbn.
    rewrite plus_comm.
    reflexivity.
Qed.
Global Program Instance aof_ex_plus_assoc : PlusAssoc (set_type aof_ex_set).
Next Obligation.
    unfold plus; cbn.
    do 2 rewrite aof_ex_f_eq1.
    rewrite plus_assoc.
    reflexivity.
Qed.
Global Program Instance aof_ex_plus_lid : PlusLid (set_type aof_ex_set).
Next Obligation.
    unfold plus, zero; cbn.
    rewrite aof_ex_f_eq1.
    rewrite plus_lid.
    apply aof_ex_f_eq2.
Qed.
Global Program Instance aof_ex_plus_linv : PlusLinv (set_type aof_ex_set).
Next Obligation.
    unfold plus, zero, neg; cbn.
    rewrite aof_ex_f_eq1.
    rewrite plus_linv.
    reflexivity.
Qed.
Global Instance aof_ex_mult : Mult (set_type aof_ex_set) := {
    mult a b := aof_ex_f (aof_ex_f_inv a * aof_ex_f_inv b)
}.
Global Instance aof_ex_one : One (set_type aof_ex_set) := {
    one := aof_ex_f 1
}.
Global Instance aof_ex_div : Div (set_type aof_ex_set) := {
    div a := aof_ex_f (/aof_ex_f_inv a)
}.
Global Program Instance aof_ex_mult_comm : MultComm (set_type aof_ex_set).
Next Obligation.
    unfold mult; cbn.
    rewrite mult_comm.
    reflexivity.
Qed.
Global Program Instance aof_ex_mult_assoc : MultAssoc (set_type aof_ex_set).
Next Obligation.
    unfold mult; cbn.
    do 2 rewrite aof_ex_f_eq1.
    rewrite mult_assoc.
    reflexivity.
Qed.
Global Program Instance aof_ex_ldist : Ldist (set_type aof_ex_set).
Next Obligation.
    unfold plus, mult; cbn.
    do 3 rewrite aof_ex_f_eq1.
    rewrite ldist.
    reflexivity.
Qed.
Global Program Instance aof_ex_mult_lid : MultLid (set_type aof_ex_set).
Next Obligation.
    unfold one, mult; cbn.
    rewrite aof_ex_f_eq1.
    rewrite mult_lid.
    apply aof_ex_f_eq2.
Qed.
Global Program Instance aof_ex_mult_linv : MultLinv (set_type aof_ex_set).
Next Obligation.
    rename H15 into a_nz.
    unfold div, mult, one; cbn.
    rewrite aof_ex_f_eq1.
    rewrite mult_linv; [>reflexivity|].
    intros contr.
    apply a_nz; clear a_nz.
    destruct a as [a' [a a_eq]]; subst a'.
    apply set_type_eq; cbn.
    unfold zero; cbn.
    apply (f_equal aof_ex_f) in contr.
    rewrite aof_ex_f_eq2 in contr.
    apply set_type_eq in contr; cbn in contr.
    exact contr.
Qed.
Global Instance aof_ex_le : Order (set_type aof_ex_set) := {
    le a b := aof_ex_f_inv a ≤ aof_ex_f_inv b
}.
Global Program Instance aof_ex_le_antisym : Antisymmetric le.
Next Obligation.
    rename H15 into xy, H16 into yx.
    unfold le in xy, yx; cbn in xy, yx.
    pose proof (antisym xy yx) as eq.
    apply (f_equal aof_ex_f) in eq.
    do 2 rewrite aof_ex_f_eq2 in eq.
    exact eq.
Qed.
Global Program Instance aof_ex_le_trans : Transitive le.
Next Obligation.
    rename H15 into xy, H16 into yz.
    unfold le in *; cbn in *.
    exact (trans xy yz).
Qed.
Global Program Instance aof_ex_le_connex : Connex le.
Next Obligation.
    unfold le; cbn.
    apply connex.
Qed.
Global Program Instance aof_ex_le_lplus : OrderLplus (set_type aof_ex_set).
Next Obligation.
    rename H15 into leq.
    unfold le in *; cbn in *.
    unfold plus; cbn.
    do 2 rewrite aof_ex_f_eq1.
    apply le_lplus.
    exact leq.
Qed.
Global Program Instance aof_ex_le_mult : OrderMult (set_type aof_ex_set).
Next Obligation.
    rename H15 into a_pos, H16 into b_pos.
    unfold zero, le, mult in *; cbn in *.
    rewrite aof_ex_f_eq1 in *.
    rewrite aof_ex_f_eq1.
    apply (le_mult a_pos b_pos).
Qed.
Global Program Instance aof_ex_not_trivial : NotTrivial (set_type aof_ex_set) := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Next Obligation.
    unfold zero, one; cbn.
    intros contr.
    apply aof_ex_f_inj in contr.
    exact (not_trivial_one contr).
Qed.
Lemma aof_ex_lt : ∀ a b, a < b ↔ aof_ex_f_inv a < aof_ex_f_inv b.
Proof.
    intros a b.
    split.
    -   intros [leq neq].
        split.
        +   exact leq.
        +   intros contr.
            apply (f_equal aof_ex_f) in contr.
            do 2 rewrite aof_ex_f_eq2 in contr.
            contradiction.
    -   intros [leq neq].
        split.
        +   exact leq.
        +   intros contr.
            subst.
            contradiction.
Qed.
Global Program Instance aof_ex_arch : Archimedean (set_type aof_ex_set).
Next Obligation.
    rename H15 into x_pos, H16 into y_pos.
    rewrite aof_ex_lt in x_pos, y_pos.
    unfold zero in x_pos, y_pos; cbn in x_pos, y_pos.
    rewrite aof_ex_f_eq1 in x_pos, y_pos.
    pose proof (archimedean _ _ x_pos y_pos) as [n n_gt].
    exists n.
    rewrite aof_ex_lt.
    assert (aof_ex_f_inv (n × y) = n × aof_ex_f_inv y) as eq.
    {
        clear n_gt.
        nat_induction n.
        -   do 2 rewrite nat_mult_lanni.
            unfold zero at 1; cbn.
            apply aof_ex_f_eq1.
        -   do 2 rewrite nat_mult_suc.
            unfold plus at 1; cbn.
            rewrite aof_ex_f_eq1.
            rewrite IHn.
            reflexivity.
    }
    rewrite eq.
    exact n_gt.
Qed.

Definition aof_ex := make_arch_ordered
    aof_ex_set
    aof_ex_plus
    aof_ex_zero
    aof_ex_neg
    aof_ex_plus_comm
    aof_ex_plus_assoc
    aof_ex_plus_lid
    aof_ex_plus_linv
    aof_ex_mult
    aof_ex_one
    aof_ex_div
    aof_ex_mult_comm
    aof_ex_mult_assoc
    aof_ex_ldist
    aof_ex_mult_lid
    aof_ex_mult_linv
    aof_ex_le
    aof_ex_le_antisym
    aof_ex_le_trans
    aof_ex_le_connex
    aof_ex_le_lplus
    aof_ex_le_mult
    aof_ex_not_trivial
    aof_ex_arch.

End AOFEx.

Arguments aof_ex U {UP H H0 UZ H1 UN H2 UM H3 H4 H5 UE H6 UO H7 H8 H9 H10 H11 H12 UD H13 H14}.

Definition rat_aof := aof_ex rat.
