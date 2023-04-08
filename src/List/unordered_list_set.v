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
        apply (trans2 (list_perm_split l3 l4 a)) in eq.
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
        pose proof (trans eq eq2) as eq3.
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

Theorem ulist_filter_single_in {U} : ∀ (S : U → Prop) a,
    S a → ulist_filter S ⟦a⟧ = ⟦a⟧.
Proof.
    intros S a Sa.
    rewrite (ulist_filter_add_in _ _ _ Sa), ulist_filter_end.
    reflexivity.
Qed.
Theorem ulist_filter_single_nin {U} : ∀ (S : U → Prop) a,
    ¬S a → ulist_filter S ⟦a⟧ = ⟦⟧.
Proof.
    intros S a Sa.
    rewrite (ulist_filter_add_nin _ _ _ Sa).
    apply ulist_filter_end.
Qed.

Theorem ulist_filter_conc {U} : ∀ (S : U → Prop) l1 l2,
    ulist_filter S (l1 + l2) = ulist_filter S l1 + ulist_filter S l2.
Proof.
    intros S l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_filter, plus; equiv_simpl.
    rewrite list_filter_conc.
    apply refl.
Qed.

Theorem ulist_filter_in_both {U} : ∀ S (l : ulist U) x,
    in_ulist (ulist_filter S l) x → in_ulist l x ∧ S x.
Proof.
    intros S l x.
    equiv_get_value l.
    unfold in_ulist, ulist_filter; equiv_simpl.
    apply list_filter_in_both.
Qed.

Theorem ulist_filter_in {U} : ∀ S l (a : U),
    in_ulist (ulist_filter S l) a → in_ulist l a.
Proof.
    intros S l a a_in.
    apply (ulist_filter_in_both _ _ _ a_in).
Qed.

Theorem ulist_filter_in_set {U} : ∀ S l (a : U),
    in_ulist (ulist_filter S l) a → S a.
Proof.
    intros S l a a_in.
    apply (ulist_filter_in_both _ _ _ a_in).
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

Theorem ulist_filter_inter {U} : ∀ S T (l : ulist U),
    ulist_filter S (ulist_filter T l) = ulist_filter (S ∩ T) l.
Proof.
    intros S T l.
    equiv_get_value l.
    unfold ulist_filter; equiv_simpl.
    rewrite list_filter_inter.
    apply refl.
Qed.

Theorem ulist_filter_filter {U} : ∀ S (l : ulist U),
    ulist_filter S l = ulist_filter S (ulist_filter S l).
Proof.
    intros S l.
    rewrite ulist_filter_inter.
    rewrite inter_idemp.
    reflexivity.
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

Theorem ulist_prop_single {U} : ∀ S (a : U), ulist_prop S ⟦a⟧ ↔ S a.
Proof.
    intros S a.
    rewrite ulist_prop_add.
    rewrite (prop_is_true (ulist_prop_end _)).
    rewrite and_rtrue.
    reflexivity.
Qed.

Tactic Notation "ulist_prop_induction" ident(l) ident(P) "as"
    simple_intropattern(a) simple_intropattern(nin) simple_intropattern(IHl) :=
    move P before l;
    induction l as [|a l IHl] using ulist_induction;
    [>|
        rewrite ulist_prop_add in P;
        specialize (IHl (rand P));
        destruct P as [nin P]
    ].

Theorem ulist_prop_conc {U} : ∀ S (l1 l2 : ulist U),
    ulist_prop S (l1 + l2) ↔ ulist_prop S l1 ∧ ulist_prop S l2.
Proof.
    intros S l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_prop, plus; equiv_simpl.
    apply list_prop_conc.
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

Theorem ulist_prop_filter {U} : ∀ (l : ulist U) S, ulist_prop S (ulist_filter S l).
Proof.
    intros l S.
    equiv_get_value l.
    unfold ulist_prop, ulist_filter; equiv_simpl.
    apply list_prop_filter.
Qed.

Theorem ulist_prop_in {U} : ∀ (a : ulist U) S, ulist_prop S a →
    ∀ x, in_ulist a x → S x.
Proof.
    intros a S.
    equiv_get_value a.
    unfold ulist_prop, in_ulist; equiv_simpl.
    intros Sa x.
    equiv_simpl.
    apply (list_prop_in _ _ Sa).
Qed.

Theorem ulist_prop_in_sub {U} : ∀ {a b : ulist U} {S},
    ulist_prop S b → (∀ x, in_ulist a x → in_ulist b x) → ulist_prop S a.
Proof.
    intros a b S.
    equiv_get_value a b.
    unfold ulist_prop, in_ulist; equiv_simpl.
    intros b_in x_in.
    apply (list_prop_in_sub b_in).
    intros x.
    specialize (x_in x).
    equiv_simpl in x_in.
    exact x_in.
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
