Require Import init.

Require Import nat.
Require Import set.
Require Export plus_group.

Require Export int_base.

Notation "a ⊕ b" := (fst a + fst b, snd a + snd b) : int_scope.

Open Scope int_scope.

Lemma int_plus_wd : ∀ a b c d, a ~ b → c ~ d → a ⊕ c ~ b ⊕ d.
Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] ab cd.
    cbn in *.
    rewrite plus_4.
    rewrite ab, cd.
    apply plus_4.
Qed.

Global Instance int_plus : Plus int := {
    plus := binary_op (binary_self_wd int_plus_wd)
}.

Global Instance int_plus_comm_class : PlusComm int.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    destruct a as [a1 a2], b as [b1 b2].
    unfold plus; equiv_simpl.
    rewrite (plus_comm a1).
    rewrite (plus_comm b2).
    reflexivity.
Qed.

Global Instance int_plus_assoc_class : PlusAssoc int.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
    unfold plus; equiv_simpl.
    rewrite (plus_assoc a1), (plus_assoc a2).
    reflexivity.
Qed.

Global Instance int_zero : Zero int := {
    zero := to_equiv int_equiv (0, 0);
}.


Global Instance int_plus_lid_class : PlusLid int.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold zero, plus; equiv_simpl.
    do 2 rewrite plus_lid.
    reflexivity.
Qed.

Notation "⊖ a" := (snd a, fst a) : int_scope.

Lemma int_neg_wd : ∀ a b, a ~ b → ⊖a ~ ⊖b.
Proof.
    intros [a1 a2] [b1 b2] eq.
    cbn in *.
    symmetry.
    rewrite (plus_comm b2), (plus_comm a2).
    exact eq.
Qed.

Global Instance int_neg : Neg int := {
    neg := unary_op (unary_self_wd int_neg_wd);
}.

Global Instance int_plus_linv_class : PlusLinv int.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold zero, plus, neg; equiv_simpl.
    rewrite plus_rid, plus_lid.
    apply plus_comm.
Qed.

Close Scope int_scope.
