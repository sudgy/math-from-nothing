Require Import init.

Require Export group_category.
Require Export group_subgroup.

Require Import set.

Record NormalSubgroup (G : Group) := make_normal_subgroup {
    normal_subgroup_subgroup :> Subgroup G;
    normal_subgroup_aha : ∀ a h,
        normal_subgroup_subgroup h → normal_subgroup_subgroup (a + h - a);
}.

Arguments normal_subgroup_subgroup {G}.
Arguments normal_subgroup_aha {G}.

Section QuotientGroup.

Context {G : Group} (H : NormalSubgroup G).

Let quotient_eq a b := H (a - b).
Local Infix "~" := quotient_eq : algebra_scope.

Local Instance quotient_group_eq_reflexive : Reflexive quotient_eq.
Proof.
    split.
    intros x.
    unfold quotient_eq.
    rewrite plus_rinv.
    apply subgroup_zero.
Qed.

Local Instance quotient_group_eq_symmetric : Symmetric quotient_eq.
Proof.
    split.
    unfold quotient_eq.
    intros a b ab.
    apply subgroup_neg in ab.
    rewrite neg_plus_group in ab.
    rewrite neg_neg in ab.
    exact ab.
Qed.

Local Instance quotient_group_eq_transitive : Transitive quotient_eq.
Proof.
    split.
    unfold quotient_eq.
    intros a b c ab bc.
    pose proof (subgroup_plus H _ _ ab bc) as eq.
    rewrite plus_assoc in eq.
    rewrite plus_rlinv in eq.
    exact eq.
Qed.

Definition quotient_group_equiv := make_equiv _ quotient_group_eq_reflexive
    quotient_group_eq_symmetric quotient_group_eq_transitive.

Definition qgroup_type := equiv_type quotient_group_equiv.
Definition to_qgroup_type a := to_equiv quotient_group_equiv a.

Local Infix "~" := (eq_equal quotient_group_equiv).

Lemma qgroup_plus_wd : ∀ a b c d, a ~ b → c ~ d → a + c ~ b + d.
Proof.
    cbn; unfold quotient_eq.
    intros a b c d ab cd.
    rewrite neg_plus_group.
    pose proof (normal_subgroup_aha H a (c - d) cd) as eq.
    pose proof (subgroup_plus _ _ _ eq ab) as eq2.
    rewrite <- plus_assoc in eq2.
    rewrite plus_llinv in eq2.
    rewrite plus_assoc in eq2.
    rewrite plus_assoc.
    exact eq2.
Qed.

Local Instance quotient_group_plus : Plus qgroup_type := {
    plus := binary_op (binary_self_wd qgroup_plus_wd)
}.

Local Instance quotient_group_plus_assoc : PlusAssoc qgroup_type.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold plus; equiv_simpl.
    rewrite plus_assoc.
    reflexivity.
Qed.

Local Instance quotient_group_zero : Zero qgroup_type := {
    zero := to_qgroup_type 0
}.

Local Instance quotient_group_plus_lid : PlusLid qgroup_type.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold zero, plus; equiv_simpl.
    rewrite plus_lid.
    reflexivity.
Qed.

Local Instance quotient_group_plus_rid : PlusRid qgroup_type.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold zero, plus; equiv_simpl.
    rewrite plus_rid.
    reflexivity.
Qed.

Lemma qgroup_neg_wd : ∀ a b, a ~ b → -a ~ -b.
Proof.
    cbn; unfold quotient_eq.
    intros a b eq.
    pose proof (normal_subgroup_aha H (-b) _ eq) as eq2.
    rewrite <- plus_assoc in eq2.
    rewrite plus_rrinv in eq2.
    rewrite <- neg_plus_group.
    apply subgroup_neg.
    exact eq2.
Qed.
Local Instance quotient_group_neg : Neg qgroup_type := {
    neg := unary_op (unary_self_wd qgroup_neg_wd)
}.

Local Instance quotient_group_plus_linv : PlusLinv qgroup_type.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold plus, neg, zero; equiv_simpl.
    rewrite plus_linv.
    reflexivity.
Qed.

Local Instance quotient_group_plus_rinv : PlusRinv qgroup_type.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold plus, neg, zero; equiv_simpl.
    rewrite plus_rinv.
    reflexivity.
Qed.

Local Instance to_qgroup_plus : HomomorphismPlus to_qgroup_type.
Proof.
    split.
    intros a b.
    unfold plus at 2, to_qgroup_type; equiv_simpl.
    apply refl.
Qed.

Definition quotient_group : Group := make_group qgroup_type quotient_group_plus
    quotient_group_zero quotient_group_neg quotient_group_plus_assoc
    quotient_group_plus_lid quotient_group_plus_rid quotient_group_plus_linv
    quotient_group_plus_rinv.

Definition to_qgroup : morphism G quotient_group :=
    make_group_homomorphism G quotient_group to_qgroup_type to_qgroup_plus.

Theorem to_qgroup_eq : ∀ a b, H (a - b) ↔ to_qgroup a = to_qgroup b.
Proof.
    intros a b.
    cbn; unfold to_qgroup_type.
    rewrite (equiv_eq (E := quotient_group_equiv)).
    reflexivity.
Qed.

Theorem to_qgroup_zero : ∀ a, H a ↔ 0 = to_qgroup a.
    intros a.
    assert (0 = to_qgroup a ↔ to_qgroup a = 0) as eq
        by (split; intro; symmetry; assumption).
    rewrite eq.
    rewrite <- (homo_zero (f := to_qgroup)).
    rewrite <- to_qgroup_eq.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem qgroup_unary_op {U} : ∀ (f : G → U) (wd : ∀ a b, a ~ b → f a = f b),
    ∀ x, unary_op wd (to_qgroup x) = f x.
Proof.
    intros f wd x.
    apply unary_op_eq.
Qed.

Theorem qgroup_binary_op {U} : ∀ (f : G → G → U)
    (wd : ∀ a b c d , a ~ b → c ~ d → f a c = f b d),
    ∀ x y, binary_op wd (to_qgroup x) (to_qgroup y) = f x y.
Proof.
    intros f wd x.
    apply binary_op_eq.
Qed.

Theorem qgroup_ex : ∀ x : quotient_group, ∃ a, to_qgroup a = x.
Proof.
    intros x.
    equiv_get_value x.
    exists x.
    reflexivity.
Qed.

Theorem qgroup_f_ex : ∀ {U} (f : morphism G U), (∀ x, H x → 0 = f x) →
    ∃ g : morphism quotient_group U, ∀ x, f x = g (to_qgroup x).
Proof.
    intros U f f_kern.
    assert (∀ a b, a ~ b → f a = f b) as wd.
    {
        intros a b eq.
        rewrite <- plus_0_anb_b_a.
        rewrite <- homo_neg, <- homo_plus.
        apply sym in eq.
        apply f_kern.
        exact eq.
    }
    pose (g := unary_op wd : quotient_group → U).
    assert (g_plus : HomomorphismPlus g).
    {
        split.
        intros a b.
        equiv_get_value a b.
        unfold g, plus at 1; equiv_simpl.
        apply homo_plus.
    }
    exists (make_group_homomorphism _ _ g g_plus).
    intros x.
    cbn.
    unfold g; equiv_simpl.
    reflexivity.
Qed.

Definition qgroup_f {U} {f : morphism G U} (wd : ∀ x, H x → 0 = f x)
    := ex_val (qgroup_f_ex f wd).
Definition qgroup_f_eq {U} {f : morphism G U} {wd : ∀ x, H x → 0 = f x}
    := ex_proof (qgroup_f_ex f wd) : ∀ x, f x = qgroup_f wd (to_qgroup x).

End QuotientGroup.

Arguments qgroup_f {G} {H} {U} {f}.
Arguments qgroup_f_eq {G} {H} {U} {f} {wd}.

Arguments quotient_group : simpl never.
Arguments to_qgroup : simpl never.
