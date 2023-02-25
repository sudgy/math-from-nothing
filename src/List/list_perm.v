Require Import init.

Require Export list_base.
Require Export list_prop.
Require Export list_nat.
Require Export list_fold.
Require Import nat.

Require Import relation.

Set Implicit Arguments.

Definition list_permutation {U} (l1 l2 : list U) :=
    ∀ x, list_count l1 x = list_count l2 x.

Theorem list_perm_nil {U} : list_permutation (list_end (A := U)) [].
Proof.
    intros x.
    cbn.
    reflexivity.
Qed.

Theorem list_perm_skip {U} : ∀ (x : U) l l', list_permutation l l' →
    list_permutation (x :: l) (x :: l').
Proof.
    intros x l1 l2 eq.
    intros a.
    cbn.
    apply lplus.
    apply eq.
Qed.

Theorem list_perm_swap {U} : ∀ (x y : U) l, list_permutation (y::x::l) (x::y::l).
Proof.
    intros x y l n.
    cbn.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply plus_comm.
Qed.

Theorem list_perm_trans {U} {l l' l'' : list U} :
    list_permutation l l' → list_permutation l' l'' →
    list_permutation l l''.
Proof.
    intros eq1 eq2 n.
    rewrite eq1.
    apply eq2.
Qed.

Theorem list_perm_refl {U} : ∀ l : list U, list_permutation l l.
Proof.
    intros l x.
    reflexivity.
Qed.

Theorem list_perm_sym {U} : ∀ al bl : list U,
    list_permutation al bl → list_permutation bl al.
Proof.
    intros al bl eq.
    intros n.
    symmetry.
    apply eq.
Qed.

Theorem list_perm_trans2 {U} (l l' l'' : list U) :
    list_permutation l' l'' → list_permutation l l' →
    list_permutation l l''.
Proof.
    intros eq1 eq2.
    apply (list_perm_trans eq2 eq1).
Qed.

Theorem list_perm_nil_eq {U} : ∀ l : list U,
    list_permutation list_end l → list_end = l.
Proof.
    intros l l_eq.
    destruct l as [|a l]; [>reflexivity|].
    specialize (l_eq a).
    cbn in l_eq.
    case_if [eq|neq]; [>|contradiction].
    inversion l_eq.
Qed.

Theorem list_perm_lpart {U} : ∀ (al bl cl : list U),
    list_permutation al bl → list_permutation (al ++ cl) (bl ++ cl).
Proof.
    intros al bl cl eq n.
    do 2 rewrite list_count_conc.
    apply rplus.
    apply eq.
Qed.

Theorem list_perm_conc {U} : ∀ al bl : list U,
    list_permutation (al ++ bl) (bl ++ al).
Proof.
    intros al bl n.
    do 2 rewrite list_count_conc.
    apply plus_comm.
Qed.

Theorem list_perm_add {U} : ∀ (l : list U) a,
    list_permutation (a :: l) (l ++ a :: list_end).
Proof.
    intros l a.
    apply (list_perm_trans2 (list_perm_conc _ _)).
    apply list_perm_refl.
Qed.

Theorem list_perm_rpart {U} : ∀ (al bl cl : list U),
    list_permutation bl cl → list_permutation (al ++ bl) (al ++ cl).
Proof.
    intros al bl cl eq n.
    do 2 rewrite list_count_conc.
    apply lplus.
    apply eq.
Qed.

Theorem list_perm_split {U} : ∀ l1 l2 (x : U),
    list_permutation (l1 ++ x :: l2) (x :: l1 ++ l2).
Proof.
    intros l1 l2 a x.
    cbn.
    do 2 rewrite list_count_conc.
    cbn.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply plus_comm.
Qed.

Theorem list_perm_add_eq {U} : ∀ (a : U) l1 l2,
    list_permutation (a :: l1) (a :: l2) → list_permutation l1 l2.
Proof.
    intros a l1 l2 eq x.
    specialize (eq x).
    cbn in eq.
    apply plus_lcancel in eq.
    exact eq.
Qed.

Theorem list_perm_conc_lcancel {U} : ∀ (l1 l2 l3 : list U),
    list_permutation (l1 ++ l2) (l1 ++ l3) → list_permutation l2 l3.
Proof.
    intros a l1 l2 eq x.
    specialize (eq x).
    cbn in eq.
    do 2 rewrite list_count_conc in eq.
    apply plus_lcancel in eq.
    exact eq.
Qed.

Theorem list_perm_conc_rcancel {U} : ∀ (l1 l2 l3 : list U),
    list_permutation (l2 ++ l1) (l3 ++ l1) → list_permutation l2 l3.
Proof.
    intros a l1 l2 eq x.
    specialize (eq x).
    cbn in eq.
    do 2 rewrite list_count_conc in eq.
    apply plus_rcancel in eq.
    exact eq.
Qed.

Theorem list_in_unique_perm {U} : ∀ al bl : list U,
    list_unique al → list_unique bl → (∀ x, in_list al x ↔ in_list bl x) →
    list_permutation al bl.
Proof.
    intros al bl al_uni bl_uni x_in n.
    classic_case (in_list al n) as [n_in|n_nin].
    -   pose proof n_in as n_in'.
        apply x_in in n_in.
        rewrite (list_count_in_unique _ _ al_uni n_in').
        rewrite (list_count_in_unique _ _ bl_uni n_in).
        reflexivity.
    -   pose proof n_nin as n_nin'.
        rewrite x_in in n_nin'.
        apply list_count_nin in n_nin, n_nin'.
        rewrite <- n_nin, <- n_nin'.
        reflexivity.
Qed.

Theorem list_perm_in {U} : ∀ al bl : list U,
    list_permutation al bl → (∀ x, in_list al x ↔ in_list bl x).
Proof.
    intros al bl eq x.
    specialize (eq x).
    split; intros x_in.
    -   rewrite list_count_in in x_in.
        rewrite eq in x_in.
        rewrite <- list_count_in in x_in.
        exact x_in.
    -   rewrite list_count_in in x_in.
        rewrite <- eq in x_in.
        rewrite <- list_count_in in x_in.
        exact x_in.
Qed.

Theorem list_perm_unique {U} : ∀ al bl : list U,
    list_permutation al bl → list_unique al → list_unique bl.
Proof.
    intros al bl albl al_uni.
    revert bl albl al_uni.
    induction al as [|a al]; intros.
    -   apply list_perm_nil_eq in albl.
        rewrite <- albl.
        exact true.
    -   destruct al_uni as [a_nin al_uni].
        assert (in_list (a :: al) a) as a_in by (left; reflexivity).
        apply (list_perm_in albl) in a_in.
        apply in_list_split in a_in as [l1 [l2 eq]]; subst bl.
        pose proof (list_perm_split l1 l2 a) as eq.
        pose proof (list_perm_trans albl eq) as eq2.
        apply list_perm_add_eq in eq2.
        specialize (IHal _ eq2 al_uni).
        apply list_unique_conc.
        rewrite list_conc_add.
        cbn.
        split; [>|apply list_unique_conc; exact IHal].
        intros a_in.
        apply (list_perm_trans2 (list_perm_conc _ _)) in eq2.
        apply (list_perm_in eq2) in a_in.
        contradiction.
Qed.

Theorem list_split_perm {U} : ∀ l (a : U), in_list l a → ∃ l',
    list_permutation l (a :: l').
Proof.
    intros l a a_in.
    pose proof (in_list_split l a a_in) as [l1 [l2 l_eq]].
    rewrite l_eq.
    exists (l1 ++ l2).
    apply list_perm_split.
Qed.

Theorem list_image_perm {U V} : ∀ al bl (f : U → V),
    list_permutation al bl →
    list_permutation (list_image al f) (list_image bl f).
Proof.
    intros al bl f albli x.
    revert bl albli.
    induction al as [|a al]; intros.
    -   apply list_perm_nil_eq in albli.
        subst bl.
        rewrite list_image_end.
        cbn.
        reflexivity.
    -   assert (in_list (a :: al) a) as a_in by (left; reflexivity).
        apply (list_perm_in albli) in a_in.
        apply in_list_split in a_in as [l1 [l2 eq]]; subst bl.
        pose proof (list_perm_split l1 l2 a) as eq.
        pose proof (list_perm_trans albli eq) as eq2.
        apply list_perm_add_eq in eq2.
        specialize (IHal _ eq2).
        rewrite list_image_conc.
        do 2 rewrite list_image_add.
        rewrite list_count_conc.
        cbn.
        rewrite IHal.
        rewrite list_image_conc, list_count_conc.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.

Theorem list_perm_single {U} : ∀ (x : U) l, list_permutation [x] l → l = [x].
Proof.
    intros x l l_perm.
    assert (in_list [x] x) as x_in by (left; reflexivity).
    apply (list_perm_in l_perm) in x_in.
    apply in_list_split in x_in as [l1 [l2 eq]]; subst l.
    pose proof (list_perm_split l1 l2 x) as eq.
    pose proof (list_perm_trans l_perm eq) as eq2.
    apply list_perm_add_eq in eq2.
    apply list_perm_nil_eq in eq2.
    destruct l1.
    -   rewrite list_conc_lid.
        rewrite list_conc_lid in eq2.
        destruct l2.
        +   reflexivity.
        +   inversion eq2.
    -   inversion eq2.
Qed.

Theorem list_perm_eq {U} : ∀ l1 l2 : list U, l1 = l2 → list_permutation l1 l2.
Proof.
    intros l1 l2 eq.
    rewrite eq.
    apply list_perm_refl.
Qed.

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
        assert (in_list (a :: l1) a) as a_in' by (left; reflexivity).
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

Theorem list_perm_swap2 {U} : ∀ (a b : U) l1 l2, list_permutation l1 l2 →
    list_permutation (a :: b :: l1) (b :: a :: l2).
Proof.
    intros a b l1 l2 eq.
    pose proof (list_perm_swap b a l1) as eq1.
    apply (list_perm_trans eq1).
    apply list_perm_skip.
    apply list_perm_skip.
    exact eq.
Qed.

Theorem list_perm_reverse {U} : ∀ l : list U,
    list_permutation l (list_reverse l).
Proof.
    intros l x.
    apply list_count_reverse.
Qed.

Section Fold.

Context {U V} `{CRing U, CRing V}.

Theorem list_sum_perm : ∀ l1 l2, list_permutation l1 l2 →
    list_sum l1 = list_sum l2.
Proof.
    induction l1 as [|a l1]; intros l2 eq.
    -   apply list_perm_nil_eq in eq.
        subst l2.
        reflexivity.
    -   assert (in_list (a :: l1) a) as a_in by (left; reflexivity).
        apply (list_perm_in eq) in a_in.
        apply in_list_split in a_in as [l3 [l4 l2_eq]]; subst l2.
        rewrite list_sum_plus.
        cbn.
        pose proof (list_perm_split l3 l4 a) as eq2.
        pose proof (list_perm_trans eq eq2) as eq3.
        apply list_perm_add_eq in eq3.
        rewrite (IHl1 _ eq3).
        rewrite list_sum_plus.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.

Theorem list_prod_perm : ∀ l1 l2, list_permutation l1 l2 →
    list_prod l1 = list_prod l2.
Proof.
    induction l1 as [|a l1]; intros l2 eq.
    -   apply list_perm_nil_eq in eq.
        subst l2.
        reflexivity.
    -   assert (in_list (a :: l1) a) as a_in by (left; reflexivity).
        apply (list_perm_in eq) in a_in.
        apply in_list_split in a_in as [l3 [l4 l2_eq]]; subst l2.
        rewrite list_prod_mult.
        cbn.
        pose proof (list_perm_split l3 l4 a) as eq2.
        pose proof (list_perm_trans eq eq2) as eq3.
        apply list_perm_add_eq in eq3.
        rewrite (IHl1 _ eq3).
        rewrite list_prod_mult.
        do 2 rewrite mult_assoc.
        apply rmult.
        apply mult_comm.
Qed.

End Fold.
