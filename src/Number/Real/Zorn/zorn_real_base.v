Require Import init.

Require Import nat.
Require Import int.
Require Import rat.
Require Import set.

Record ArchOrderedField := make_arch_ordered {
    aof_set : (nat → Prop) → Prop;
    aof_plus : Plus (set_type aof_set);
    aof_zero : Zero (set_type aof_set);
    aof_neg : Neg (set_type aof_set);
    aof_plus_comm : @PlusComm (set_type aof_set) aof_plus;
    aof_plus_assoc : @PlusAssoc (set_type aof_set) aof_plus;
    aof_plus_lid : @PlusLid (set_type aof_set) aof_plus aof_zero;
    aof_plus_linv : @PlusLinv (set_type aof_set) aof_plus aof_zero aof_neg;

    aof_mult : Mult (set_type aof_set);
    aof_one : One (set_type aof_set);
    aof_div : Div (set_type aof_set);
    aof_mult_comm : @MultComm (set_type aof_set) aof_mult;
    aof_mult_assoc : @MultAssoc (set_type aof_set) aof_mult;
    aof_ldist : @Ldist (set_type aof_set) aof_plus aof_mult;
    aof_mult_lid : @MultLid (set_type aof_set) aof_mult aof_one;
    aof_mult_linv : @MultLinv (set_type aof_set) aof_zero aof_mult aof_one aof_div;

    aof_le : Order (set_type aof_set);
    aof_le_antisym : @Antisymmetric (set_type aof_set) le;
    aof_le_trans : @Transitive (set_type aof_set) le;
    aof_le_connex : @Connex (set_type aof_set) le;
    aof_le_lplus : @OrderLplus (set_type aof_set) aof_plus aof_le;
    aof_le_mult : @OrderMult (set_type aof_set) aof_zero aof_mult aof_le;

    aof_not_trivial : @NotTrivial (set_type aof_set);
    aof_arch : @Archimedean (set_type aof_set) aof_plus aof_zero aof_le;
}.

Section ArchOrderedField.

Variables (A B : ArchOrderedField).

Let U1 := aof_set A.
Let A_plus := aof_plus A.
Let A_zero := aof_zero A.
Let A_neg := aof_neg A.
Let A_plus_comm := aof_plus_comm A.
Let A_plus_assoc := aof_plus_assoc A.
Let A_plus_lid := aof_plus_lid A.
Let A_plus_linv := aof_plus_linv A.
Let A_mult := aof_mult A.
Let A_one := aof_one A.
Let A_div := aof_div A.
Let A_mult_comm := aof_mult_comm A.
Let A_mult_assoc := aof_mult_assoc A.
Let A_ldist := aof_ldist A.
Let A_mult_lid := aof_mult_lid A.
Let A_mult_linv := aof_mult_linv A.
Let A_le := aof_le A.
Let A_le_antisym := aof_le_antisym A.
Let A_le_trans := aof_le_trans A.
Let A_le_connex := aof_le_connex A.
Let A_le_lplus := aof_le_lplus A.
Let A_le_mult := aof_le_mult A.
Let A_not_trivial := aof_not_trivial A.
Let A_arch := aof_arch A.
Let U2 := aof_set B.
Let B_plus := aof_plus B.
Let B_zero := aof_zero B.
Let B_neg := aof_neg B.
Let B_plus_comm := aof_plus_comm B.
Let B_plus_assoc := aof_plus_assoc B.
Let B_plus_lid := aof_plus_lid B.
Let B_plus_linv := aof_plus_linv B.
Let B_mult := aof_mult B.
Let B_one := aof_one B.
Let B_div := aof_div B.
Let B_mult_comm := aof_mult_comm B.
Let B_mult_assoc := aof_mult_assoc B.
Let B_ldist := aof_ldist B.
Let B_mult_lid := aof_mult_lid B.
Let B_mult_linv := aof_mult_linv B.
Let B_le := aof_le B.
Let B_le_antisym := aof_le_antisym B.
Let B_le_trans := aof_le_trans B.
Let B_le_connex := aof_le_connex B.
Let B_le_lplus := aof_le_lplus B.
Let B_le_mult := aof_le_mult B.
Let B_not_trivial := aof_not_trivial B.
Let B_arch := aof_arch B.
Local Existing Instances A_plus A_zero A_neg A_plus_comm A_plus_assoc A_plus_lid
    A_plus_linv A_mult A_one A_div A_mult_comm A_mult_assoc A_ldist A_mult_lid
    A_mult_linv A_le A_le_antisym A_le_trans A_le_connex A_le_lplus A_le_mult
    A_not_trivial A_arch B_plus B_zero B_neg B_plus_comm B_plus_assoc B_plus_lid
    B_plus_linv B_mult B_one B_div B_mult_comm B_mult_assoc B_ldist B_mult_lid
    B_mult_linv B_le B_le_antisym B_le_trans B_le_connex B_le_lplus B_le_mult
    B_not_trivial B_arch.

Definition arch_ordered_homo (f : set_type (aof_set A) → set_type (aof_set B))
    :=
        f 0 = 0 ∧
        f 1 = 1 ∧
        (∀ a b, f (a + b) = f a + f b) ∧
        (∀ a b, f (a * b) = f a * f b) ∧
        (∀ a b, a ≤ b → f a ≤ f b).

Theorem arch_ordered_homo_neg : ∀ f, arch_ordered_homo f → ∀ x, f (-x) = -f x.
Proof.
    intros f f_homo x.
    pose proof f_homo as [f_zero [f_one [f_plus [f_mult f_le]]]].
    apply plus_lcancel with (f x).
    rewrite <- f_plus.
    do 2 rewrite plus_rinv.
    exact f_zero.
Qed.

Theorem arch_ordered_homo_inj : ∀ f, arch_ordered_homo f → Injective f.
Proof.
    intros f f_homo.
    split.
    intros a b eq.
    rewrite <- plus_0_anb_b_a.
    rewrite <- plus_0_anb_b_a in eq.
    rewrite <- (arch_ordered_homo_neg _ f_homo) in eq.
    pose proof f_homo as [f_zero [f_one [f_plus [f_mult f_le]]]].
    rewrite <- f_plus in eq.
    remember (b - a) as c.
    clear a b Heqc.
    classic_contradiction contr.
    apply lmult with (f (/c)) in eq.
    rewrite mult_ranni in eq.
    rewrite <- f_mult in eq.
    rewrite mult_linv in eq by exact contr.
    rewrite f_one in eq.
    apply not_trivial_one in eq.
    exact eq.
Qed.


Theorem arch_ordered_homo_le : ∀ f, arch_ordered_homo f →
    ∀ x y, x ≤ y ↔ f x ≤ f y.
Proof.
    intros f f_homo x y.
    split; [>apply f_homo|].
    intros leq.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    destruct contr as [yx neq].
    apply f_homo in yx.
    pose proof (antisym leq yx) as eq.
    apply (arch_ordered_homo_inj _ f_homo) in eq.
    symmetry in eq.
    contradiction.
Qed.

Theorem arch_ordered_homo_lt : ∀ f, arch_ordered_homo f →
    ∀ x y, x < y ↔ f x < f y.
Proof.
    intros f f_homo x y.
    unfold strict.
    rewrite <- (arch_ordered_homo_le _ f_homo).
    split.
    -   intros [leq neq].
        split; [>exact leq|].
        intros eq.
        apply arch_ordered_homo_inj in eq; [>|exact f_homo].
        contradiction.
    -   intros [leq neq].
        split; [>exact leq|].
        intros eq.
        subst y.
        contradiction.
Qed.

Theorem arch_ordered_homo_div : ∀ f, arch_ordered_homo f →
    ∀ x, 0 ≠ x → f (/x) = /f x.
Proof.
    intros f f_homo x x_nz.
    pose proof f_homo as [f_zero [f_one [f_plus [f_mult f_le]]]].
    assert (0 ≠ f x) as fx_nz.
    {
        intros contr.
        rewrite <- f_zero in contr.
        apply arch_ordered_homo_inj in contr; [>|exact f_homo].
        contradiction.
    }
    apply mult_lcancel with (f x); [>exact fx_nz|].
    rewrite <- f_mult.
    rewrite mult_rinv by exact x_nz.
    rewrite mult_rinv by exact fx_nz.
    exact f_one.
Qed.

Theorem arch_ordered_homo_nat : ∀ f, arch_ordered_homo f →
    ∀ n, f (from_nat n) = from_nat n.
Proof.
    intros f f_homo n.
    pose proof f_homo as [f_zero [f_one [f_plus [f_mult f_le]]]].
    nat_induction n.
    -   setoid_rewrite homo_zero.
        exact f_zero.
    -   cbn.
        rewrite f_plus.
        rewrite f_one, IHn.
        reflexivity.
Qed.

Theorem arch_ordered_homo_int : ∀ f, arch_ordered_homo f →
    ∀ n, f (from_int n) = from_int n.
Proof.
    intros f f_homo n.
    pose proof f_homo as [f_zero [f_one [f_plus [f_mult f_le]]]].
    equiv_get_value n.
    destruct n as [m n].
    unfold from_int; equiv_simpl.
    unfold from_int_base; cbn.
    rewrite f_plus.
    rewrite arch_ordered_homo_neg by exact f_homo.
    do 2 rewrite arch_ordered_homo_nat by exact f_homo.
    reflexivity.
Qed.

Theorem arch_ordered_homo_rat : ∀ f, arch_ordered_homo f →
    ∀ q, f (from_rat q) = from_rat q.
Proof.
    intros f f_homo q.
    pose proof f_homo as [f_zero [f_one [f_plus [f_mult f_le]]]].
    pose proof (to_ofrac_ex q) as [q1 [q2 [q2_pos q_eq]]]; subst q.
    do 2 rewrite (homo_mult (f := from_rat)).
    rewrite homo_div.
    2: apply (inj_zero (to_ofrac int) (rand q2_pos)).
    rewrite (homo_div (f := from_rat)).
    2: apply (inj_zero (to_ofrac int) (rand q2_pos)).
    do 2 rewrite <- from_int_rat.
    do 4 rewrite from_rat_int.
    rewrite f_mult.
    rewrite arch_ordered_homo_div.
    2: exact f_homo.
    2: apply (inj_zero from_int); apply q2_pos.
    do 2 rewrite arch_ordered_homo_int by exact f_homo.
    reflexivity.
Qed.

Theorem arch_ordered_homo_uni_wlog : ∀ f g,
    arch_ordered_homo f → arch_ordered_homo g →
    ∀ x, f x ≤ g x.
Proof.
    intros f g f_homo g_homo x.
    classic_contradiction ltq.
    rewrite nle_lt in ltq.
    pose proof (rat_dense_in_arch (g x) (f x) ltq) as [r [r_gt r_lt]].
    rewrite <- (arch_ordered_homo_rat g g_homo) in r_gt.
    rewrite <- (arch_ordered_homo_rat f f_homo) in r_lt.
    rewrite <- arch_ordered_homo_lt in r_gt by exact g_homo.
    rewrite <- arch_ordered_homo_lt in r_lt by exact f_homo.
    destruct (trans r_gt r_lt); contradiction.
Qed.
Theorem arch_ordered_homo_uni : ∀ f g,
    arch_ordered_homo f → arch_ordered_homo g → f = g.
Proof.
    intros f g f_homo g_homo.
    apply functional_ext.
    intros x.
    apply antisym; apply arch_ordered_homo_uni_wlog; assumption.
Qed.

Theorem arch_ordered_homo_eq : ∀ f g x,
    arch_ordered_homo f → arch_ordered_homo g → f x = g x.
Proof.
    intros f g x f_homo g_homo.
    rewrite (arch_ordered_homo_uni f g f_homo g_homo).
    reflexivity.
Qed.

End ArchOrderedField.

Arguments arch_ordered_homo_eq {A B}.

Theorem identity_arch_ordered_homo : ∀ A, arch_ordered_homo A A identity.
Proof.
    intros A.
    repeat split; intro; try assumption.
    intros b ab; exact ab.
Qed.

Theorem arch_ordered_homo_identity :
    ∀ A f, arch_ordered_homo A A f → f = identity.
Proof.
    intros A f f_homo.
    apply arch_ordered_homo_uni.
    -   exact f_homo.
    -   apply identity_arch_ordered_homo.
Qed.

Theorem arch_ordered_homo_compose :
    ∀ A B C f g, arch_ordered_homo A B f → arch_ordered_homo B C g →
    arch_ordered_homo A C (λ x, g (f x)).
Proof.
    intros A B C f g f_homo g_homo.
    destruct f_homo as [f_zero [f_one [f_plus [f_mult f_le]]]].
    destruct g_homo as [g_zero [g_one [g_plus [g_mult g_le]]]].
    split; [>|split; [>|split; [>|split]]].
    -   rewrite f_zero.
        exact g_zero.
    -   rewrite f_one.
        exact g_one.
    -   intros a b.
        rewrite f_plus.
        apply g_plus.
    -   intros a b.
        rewrite f_mult.
        apply g_mult.
    -   intros a b ab.
        apply g_le.
        apply f_le.
        exact ab.
Qed.

Global Instance arch_ordered_le : Order ArchOrderedField := {
    le A B := ∃ f, arch_ordered_homo A B f
}.
Global Program Instance arch_ordered_le_refl : Reflexive le.
Next Obligation.
    unfold le; cbn.
    exists identity.
    apply identity_arch_ordered_homo.
Qed.
Global Program Instance arch_ordered_le_trans : Transitive le.
Next Obligation.
    rename x into A, y into B, z into C, H into AB, H0 into BC.
    unfold le in *; cbn in *.
    destruct AB as [f f_homo].
    destruct BC as [g g_homo].
    exists (λ x, g (f x)).
    apply arch_ordered_homo_compose; assumption.
Qed.
