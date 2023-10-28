Require Import init.

Require Export order_mult.
Require Import int.

#[universes(template)]
Class OrderCone U `{Plus U, Neg U, Mult U, One U} := {
    cone : U → Prop;
    cone_plus : ∀ {a b}, cone a → cone b → cone (a + b);
    cone_mult : ∀ {a b}, cone a → cone b → cone (a * b);
    cone_square : ∀ a, cone (a * a);
    cone_neg : ¬cone (-1);
    cone_all : ∀ a, {cone a} + {cone (-a)};
}.

Section OrderCone.

Context {U} `{FieldClass U, @OrderCone U UP UN UM UE}.

Theorem cone_one : cone 1.
Proof.
    applys_eq (cone_square (-1)).
    rewrite mult_neg_one.
    rewrite neg_neg.
    reflexivity.
Qed.

Theorem cone_div : ∀ a, 0 ≠ a → cone a → cone (/a).
Proof.
    intros a a_nz a_pos.
    pose proof (cone_square (/a)) as a2_pos.
    pose proof (cone_mult a_pos a2_pos) as a'_pos.
    rewrite mult_lrinv in a'_pos by exact a_nz.
    exact a'_pos.
Qed.

Global Instance cone_order : Order U := {
    le a b := cone (b - a)
}.

Global Instance cone_le_antisym : Antisymmetric le.
Proof.
    split.
    unfold le; cbn.
    intros a b ab ba.
    rewrite <- plus_0_anb_b_a.
    rewrite <- (neg_neg a) in ba.
    rewrite <- neg_plus_group in ba.
    remember (b - a) as c; clear b a Heqc.
    classic_contradiction c_nz.
    pose proof (cone_div _ c_nz ab) as c_pos.
    pose proof (cone_mult ba c_pos) as contr.
    rewrite mult_lneg in contr.
    rewrite mult_rinv in contr by exact c_nz.
    exact (cone_neg contr).
Qed.

Global Instance cone_le_transitive : Transitive le.
Proof.
    split.
    unfold le; cbn.
    intros a b c ab bc.
    pose proof (cone_plus bc ab) as pos.
    rewrite plus_assoc in pos.
    rewrite plus_rlinv in pos.
    exact pos.
Qed.

Global Instance cone_le_connex : Connex le.
Proof.
    split.
    unfold le; cbn.
    intros a b.
    (* Doing this at 2 makes it really slow for some reason *)
    rewrite <- (neg_neg a).
    rewrite <- neg_plus_group.
    rewrite neg_neg.
    remember (b - a) as c; clear a b Heqc.
    apply cone_all.
Qed.

Global Instance cone_le_lplus : OrderLplus U.
Proof.
    split.
    unfold le; cbn.
    intros a b c pos.
    rewrite neg_plus.
    rewrite plus_4.
    rewrite plus_rinv, plus_lid.
    exact pos.
Qed.

Global Instance cone_le_mult : OrderMult U.
Proof.
    split.
    unfold le; cbn.
    intros a b.
    rewrite neg_zero.
    do 3 rewrite plus_rid.
    apply cone_mult.
Qed.

End OrderCone.
