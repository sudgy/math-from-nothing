Require Import init.

Require Import list.
Require Import unordered_list_base.
Require Import unordered_list_in.

Require Import equivalence.

Lemma ulist_filter_wd U : ∀ (S : U → Prop) l1 l2, list_permutation l1 l2 →
    to_equiv (ulist_equiv U) (list_filter S l1) =
    to_equiv (ulist_equiv U) (list_filter S l2).
Proof.
    intros S l1 l2 eq.
    equiv_simpl.
    intros x.
    revert l2 eq.
    induction l1; intros.
    -   apply list_perm_nil_eq in eq.
        subst l2.
        reflexivity.
    -   assert (in_list (a ꞉ l1) a) as a_in by (left; reflexivity).
        apply (list_perm_in eq) in a_in.
        apply in_list_split in a_in as [l3 [l4 l2_eq]]; subst l2.
        apply (list_perm_trans2 (list_perm_split l3 l4 a)) in eq.
        apply list_perm_add_eq in eq.
        specialize (IHl1 _ eq).
        rewrite list_filter_conc.
        rewrite list_count_conc.
        classic_case (S a) as [Sa|nSa].
        +   do 2 rewrite (list_filter_add_in Sa).
            do 2 rewrite list_count_add.
            rewrite IHl1.
            rewrite list_filter_conc.
            rewrite list_count_conc.
            do 2 rewrite plus_assoc.
            apply rplus.
            apply plus_comm.
        +   do 2 rewrite (list_filter_add_nin nSa).
            rewrite IHl1.
            rewrite list_filter_conc, list_count_conc.
            reflexivity.
Qed.
Definition ulist_filter {U} S :=
    unary_op (E := ulist_equiv U) (ulist_filter_wd U S).

Theorem list_prop_perm {U} : ∀ (S : U → Prop) (l1 l2 : list U),
    list_permutation l1 l2 → list_prop S l1 → list_prop S l2.
Proof.
    intros S l1 l2 eq Sl1.
    revert l2 eq.
    induction l1; intros.
    -   apply list_perm_nil_eq in eq.
        subst l2.
        exact true.
    -   destruct Sl1 as [a_in Sl1].
        assert (in_list (a ꞉ l1) a) as a_in' by (left; reflexivity).
        apply (list_perm_in eq) in a_in'.
        apply in_list_split in a_in' as [l3 [l4 eq']]; subst l2.
        pose proof (list_perm_split l3 l4 a) as eq2.
        pose proof (list_perm_trans eq eq2) as eq3.
        apply list_perm_add_eq in eq3.
        specialize (IHl1 Sl1 _ eq3).
        clear eq eq2 eq3.
        induction l3 as [|b l3].
        +   rewrite list_conc_lid in *.
            cbn.
            split; assumption.
        +   rewrite list_conc_add in *.
            cbn in *.
            split.
            *   apply IHl1.
            *   apply IHl3; apply IHl1.
Qed.

Lemma ulist_prop_wd U : ∀ (S : U → Prop) l1 l2, list_permutation l1 l2 →
    list_prop S l1 = list_prop S l2.
Proof.
    intros S l1 l2 eq.
    apply propositional_ext.
    split.
    -   exact (list_prop_perm S _ _ eq).
    -   apply list_perm_sym in eq.
        exact (list_prop_perm S _ _ eq).
Qed.
Definition ulist_prop {U} S :=
    unary_op (E := ulist_equiv U) (ulist_prop_wd U S).

Theorem ulist_filter_end {U} : ∀ S : U → Prop,
    ulist_filter S ulist_end = ulist_end.
Proof.
    intros S.
    unfold ulist_filter, ulist_end; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_filter_add_in {U} : ∀ (S : U → Prop) a l, S a →
    ulist_filter S (a ː l) = a ː ulist_filter S l.
Proof.
    intros S a l Sa.
    equiv_get_value l.
    unfold ulist_filter, ulist_add; equiv_simpl.
    rewrite (list_filter_add_in Sa).
    apply list_perm_refl.
Qed.

Theorem ulist_filter_add_nin {U} : ∀ (S : U → Prop) a l, ¬S a →
    ulist_filter S (a ː l) = ulist_filter S l.
Proof.
    intros S a l Sa.
    equiv_get_value l.
    unfold ulist_filter, ulist_add; equiv_simpl.
    rewrite (list_filter_add_nin Sa).
    apply list_perm_refl.
Qed.

Theorem ulist_prop_end {U} : ∀ S : U → Prop, ulist_prop S ulist_end.
Proof.
    intros S.
    unfold ulist_prop, ulist_end; equiv_simpl.
    exact true.
Qed.

Theorem ulist_prop_add {U} : ∀ S (a : U) l,
    ulist_prop S (a ː l) ↔ S a ∧ ulist_prop S l.
Proof.
    intros S a l.
    equiv_get_value l.
    unfold ulist_prop, ulist_add; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_prop_sub {U} : ∀ (l : ulist U) S T, S ⊆ T →
    ulist_prop S l → ulist_prop T l.
Proof.
    intros l S T sub.
    equiv_get_value l.
    unfold ulist_prop; equiv_simpl.
    apply list_prop_sub.
    exact sub.
Qed.

Theorem ulist_prop_other_filter {U} : ∀ (l : ulist U) S T,
    ulist_prop S l → ulist_prop S (ulist_filter T l).
Proof.
    intros l S T.
    equiv_get_value l.
    unfold ulist_prop, ulist_filter; equiv_simpl.
    apply list_prop_other_filter.
Qed.

Theorem ulist_prop_split {U} : ∀ l (S : U → Prop),
    (∀ a l', l = a ː l' → S a) → ulist_prop S l.
Proof.
    intros l S ind.
    induction l using ulist_induction.
    -   apply ulist_prop_end.
    -   rewrite ulist_prop_add.
        split.
        +   apply (ind a l).
            reflexivity.
        +   apply IHl.
            intros b l' eq.
            apply (ind b (a ː l')).
            rewrite eq.
            apply ulist_swap.
Qed.

Theorem ulist_filter_in_S {U} : ∀ S l (a : U),
    in_ulist (ulist_filter S l) a → S a.
Proof.
    intros S l a.
    equiv_get_value l.
    unfold in_ulist, ulist_filter; equiv_simpl.
    apply list_filter_in_set.
Qed.

Theorem ulist_filter_in {U} : ∀ S l (a : U),
    in_ulist (ulist_filter S l) a → in_ulist l a.
Proof.
    intros S l a.
    equiv_get_value l.
    unfold in_ulist, ulist_filter; equiv_simpl.
    apply list_filter_in.
Qed.

Theorem ulist_filter_unique {U} : ∀ S (l : ulist U),
    ulist_unique l → ulist_unique (ulist_filter S l).
Proof.
    intros S l.
    equiv_get_value l.
    unfold ulist_unique, ulist_filter; equiv_simpl.
    apply list_filter_unique.
Qed.

Theorem ulist_filter_image_in {U V} : ∀ S (f : U → V) (l : ulist U) x,
    in_ulist (ulist_image f (ulist_filter S l)) x →
    in_ulist (ulist_image f l) x.
Proof.
    intros S f l x.
    equiv_get_value l.
    unfold ulist_image, ulist_filter, in_ulist; equiv_simpl.
    apply list_filter_image_in.
Qed.

Theorem ulist_filter_image_unique {U V} : ∀ S (f : U → V) (l : ulist U),
    ulist_unique (ulist_image f l) →
    ulist_unique (ulist_image f (ulist_filter S l)).
Proof.
    intros S f l.
    equiv_get_value l.
    unfold ulist_image, ulist_filter, ulist_unique; equiv_simpl.
    apply list_filter_image_unique.
Qed.

Theorem ulist_filter_filter {U} : ∀ S (l : ulist U),
    ulist_filter S l = ulist_filter S (ulist_filter S l).
Proof.
    intros S l.
    equiv_get_value l.
    unfold ulist_filter; equiv_simpl.
    rewrite list_filter_filter.
    apply list_perm_refl.
Qed.
