Require Import init.

Require Import list.
Require Import unordered_list_base.
Require Import unordered_list_func.

Require Import equivalence.

Unset Keyed Unification.

Lemma in_ulist_wd U : ∀ (a : U) l1 l2, list_permutation l1 l2 →
    in_list l1 a = in_list l2 a.
Proof.
    intros a l1 l2 eq.
    apply propositional_ext.
    revert a.
    exact (list_perm_in eq).
Qed.
Definition in_ulist {U} l a
    := unary_op (E := ulist_equiv U) (in_ulist_wd U a) l.

Lemma ulist_unique_wd U : ∀ l1 l2 : list U, list_permutation l1 l2 →
    list_unique l1 = list_unique l2.
Proof.
    intros l1 l2 eq.
    apply propositional_ext; split.
    -   exact (list_perm_unique eq).
    -   apply list_perm_sym in eq.
        exact (list_perm_unique eq).
Qed.
Definition ulist_unique {U} :=
    unary_op (E := ulist_equiv U) (ulist_unique_wd U).

Lemma list_filter_conc {U} : ∀ (S : U → Prop) l1 l2,
    list_filter S (l1 ++ l2) = list_filter S l1 ++ list_filter S l2.
Proof.
    intros S l1 l2.
    induction l1 as [|a l1].
    -   cbn.
        do 2 rewrite list_conc_lid.
        reflexivity.
    -   rewrite list_conc_add.
        cbn.
        rewrite IHl1.
        case_if [Sa|nSa].
        +   apply list_conc_add.
        +   reflexivity.
Qed.

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
    -   assert (in_list (a :: l1) a) as a_in by (left; reflexivity).
        apply (list_perm_in eq) in a_in.
        apply in_list_split in a_in as [l3 [l4 l2_eq]]; subst l2.
        apply (list_perm_trans2 (list_perm_split l3 l4 a)) in eq.
        apply list_perm_add_eq in eq.
        specialize (IHl1 _ eq).
        rewrite list_filter_conc.
        rewrite list_count_conc.
        cbn.
        case_if [Sa|nSa].
        +   cbn.
            rewrite IHl1.
            rewrite list_filter_conc.
            rewrite list_count_conc.
            do 2 rewrite plus_assoc.
            apply rplus.
            apply plus_comm.
        +   rewrite IHl1.
            rewrite list_filter_conc, list_count_conc.
            reflexivity.
Qed.
Definition ulist_filter {U} S :=
    unary_op (E := ulist_equiv U) (ulist_filter_wd U S).

Lemma ulist_prop_wd U : ∀ (S : U → Prop) l1 l2, list_permutation l1 l2 →
    list_prop S l1 = list_prop S l2.
Proof.
    intros S l1 l2 eq.
    apply propositional_ext.
    split.
    -   exact (list_prop_perm S eq).
    -   apply list_perm_sym in eq.
        exact (list_prop_perm S eq).
Qed.
Definition ulist_prop {U} S :=
    unary_op (E := ulist_equiv U) (ulist_prop_wd U S).

Theorem in_ulist_end {U} : ∀ a : U, ¬in_ulist ulist_end a.
Proof.
    intros a contr.
    unfold in_ulist, ulist_end in contr; equiv_simpl in contr.
    exact contr.
Qed.

Theorem in_ulist_add {U} : ∀ (a b : U) l,
    in_ulist (b ::: l) a ↔ b = a ∨ in_ulist l a.
Proof.
    intros a b l.
    equiv_get_value l.
    unfold in_ulist, ulist_add; equiv_simpl.
    reflexivity.
Qed.

Theorem in_ulist_single {U} : ∀ (a b : U), in_ulist (a ::: ulist_end) b → a = b.
Proof.
    intros a b b_in.
    rewrite in_ulist_add in b_in.
    destruct b_in as [b_in|b_in].
    -   exact b_in.
    -   contradiction (in_ulist_end _ b_in).
Qed.

Theorem ulist_unique_end {U} : ulist_unique (@ulist_end U).
Proof.
    unfold ulist_unique, ulist_end; equiv_simpl.
    exact true.
Qed.

Theorem ulist_unique_single {U} : ∀ a : U, ulist_unique (a ::: ulist_end).
Proof.
    intros a.
    unfold ulist_unique, ulist_add, ulist_end; equiv_simpl.
    rewrite not_false.
    split; exact true.
Qed.

Theorem ulist_unique_add {U} : ∀ (a : U) l,
    ulist_unique (a ::: l) ↔ ¬in_ulist l a ∧ ulist_unique l.
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_unique, in_ulist, ulist_add; equiv_simpl.
    reflexivity.
Qed.

Theorem ulist_filter_end {U} : ∀ S : U → Prop,
    ulist_filter S ulist_end = ulist_end.
Proof.
    intros S.
    unfold ulist_filter, ulist_end; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_filter_add_in {U} : ∀ (S : U → Prop) a l, S a →
    ulist_filter S (a ::: l) = a ::: ulist_filter S l.
Proof.
    intros S a l Sa.
    equiv_get_value l.
    unfold ulist_filter, ulist_add; equiv_simpl.
    case_if.
    -   apply list_perm_refl.
    -   contradiction.
Qed.

Theorem ulist_filter_add_nin {U} : ∀ (S : U → Prop) a l, ¬S a →
    ulist_filter S (a ::: l) = ulist_filter S l.
Proof.
    intros S a l Sa.
    equiv_get_value l.
    unfold ulist_filter, ulist_add; equiv_simpl.
    case_if.
    -   contradiction.
    -   apply list_perm_refl.
Qed.

Theorem ulist_prop_end {U} : ∀ S : U → Prop, ulist_prop S ulist_end.
Proof.
    intros S.
    unfold ulist_prop, ulist_end; equiv_simpl.
    exact true.
Qed.

Theorem ulist_prop_add {U} : ∀ S (a : U) l,
    ulist_prop S (a ::: l) ↔ S a ∧ ulist_prop S l.
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

Theorem ulist_prop_filter {U} : ∀ (l : ulist U) S T,
    ulist_prop S l → ulist_prop S (ulist_filter T l).
Proof.
    intros l S T.
    equiv_get_value l.
    unfold ulist_prop, ulist_filter; equiv_simpl.
    apply list_prop_filter.
Qed.

Theorem ulist_prop_split {U} : ∀ l (S : U → Prop),
    (∀ a l', l = a ::: l' → S a) → ulist_prop S l.
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
            apply (ind b (a ::: l')).
            rewrite eq.
            apply ulist_swap.
Qed.

Theorem in_ulist_conc {U} : ∀ l1 l2 (a : U),
    in_ulist (l1 +++ l2) a → in_ulist l1 a ∨ in_ulist l2 a.
Proof.
    intros l1 l2 a.
    equiv_get_value l1 l2.
    unfold in_ulist, ulist_conc; equiv_simpl.
    apply in_list_conc.
Qed.

Theorem in_ulist_lconc {U} : ∀ l1 l2 (a : U),
    in_ulist l1 a → in_ulist (l1 +++ l2) a.
Proof.
    intros l1 l2 a.
    equiv_get_value l1 l2.
    unfold in_ulist, ulist_conc; equiv_simpl.
    apply in_list_lconc.
Qed.
Theorem in_ulist_rconc {U} : ∀ l1 l2 (a : U),
    in_ulist l2 a → in_ulist (l1 +++ l2) a.
Proof.
    intros l1 l2 a.
    equiv_get_value l1 l2.
    unfold in_ulist, ulist_conc; equiv_simpl.
    apply in_list_rconc.
Qed.

Theorem in_ulist_split {U} : ∀ l (a : U), in_ulist l a → ∃ l', l = a ::: l'.
Proof.
    intros l a a_in.
    equiv_get_value l.
    unfold in_ulist in a_in; equiv_simpl in a_in.
    apply list_split_perm in a_in as [l' eq].
    exists (to_equiv _ l').
    unfold ulist_add; equiv_simpl.
    exact eq.
Qed.

Theorem in_ulist_image {U V} : ∀ l a (f : U → V),
    in_ulist l a → in_ulist (ulist_image l f) (f a).
Proof.
    intros l a f.
    equiv_get_value l.
    unfold in_ulist, ulist_image; equiv_simpl.
    apply in_list_image.
Qed.

Theorem image_in_ulist {U V} : ∀ l y (f : U → V),
    in_ulist (ulist_image l f) y → ∃ x, f x = y ∧ in_ulist l x.
Proof.
    intros l y f.
    equiv_get_value l.
    unfold in_ulist, ulist_image; equiv_simpl.
    intros y_in.
    apply image_in_list in y_in as [x H].
    exists x.
    equiv_simpl.
    exact H.
Qed.

Theorem ulist_filter_in_S {U} : ∀ S l (a : U),
    in_ulist (ulist_filter S l) a → S a.
Proof.
    intros S l a.
    equiv_get_value l.
    unfold in_ulist, ulist_filter; equiv_simpl.
    apply list_filter_in_S.
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
    in_ulist (ulist_image (ulist_filter S l) f) x →
    in_ulist (ulist_image l f) x.
Proof.
    intros S f l x.
    equiv_get_value l.
    unfold ulist_image, ulist_filter, in_ulist; equiv_simpl.
    apply list_filter_image_in.
Qed.

Theorem ulist_filter_image_unique {U V} : ∀ S (f : U → V) (l : ulist U),
    ulist_unique (ulist_image l f) →
    ulist_unique (ulist_image (ulist_filter S l) f).
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
    rewrite <- list_filter_filter.
    apply list_perm_refl.
Qed.

Theorem ulist_image_unique {U V} : ∀ (l : ulist U) (f : U → V),
    ulist_unique (ulist_image l f) → ulist_unique l.
Proof.
    intros l f.
    equiv_get_value l.
    unfold ulist_image, ulist_unique; equiv_simpl.
    apply list_image_unique.
Qed.

Theorem ulist_in_unique_eq {U} : ∀ al bl : ulist U,
    ulist_unique al → ulist_unique bl →
    (∀ x, in_ulist al x ↔ in_ulist bl x) → al = bl.
Proof.
    intros al bl.
    equiv_get_value al bl.
    unfold ulist_unique, in_ulist; equiv_simpl.
    intros al_uni bl_uni ins.
    apply (list_in_unique_perm _ _ al_uni bl_uni).
    intros x.
    specialize (ins x).
    equiv_simpl in ins.
    exact ins.
Qed.
