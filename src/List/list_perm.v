Require Import init.

Require Export list_base.
Require Export list_in.
Require Export list_nat.
Require Export list_fold.
Require Import nat.

Require Import relation.

Definition list_permutation {U} (l1 l2 : list U) :=
    ∀ x, list_count l1 x = list_count l2 x.

Global Instance list_perm_refl U : Reflexive (list_permutation (U := U)).
Proof.
    split.
    intros a x.
    reflexivity.
Qed.

Global Instance list_perm_sym U : Symmetric (list_permutation (U := U)).
Proof.
    split.
    intros a b ab x.
    specialize (ab x).
    symmetry; exact ab.
Qed.

Global Instance list_perm_trans U : Transitive (list_permutation (U := U)).
Proof.
    split.
    intros a b c ab bc x.
    rewrite ab.
    apply bc.
Qed.

Theorem list_perm_skip {U} : ∀ (x : U) l l', list_permutation l l' →
    list_permutation (x ꞉ l) (x ꞉ l').
Proof.
    intros x l1 l2 eq.
    intros a.
    do 2 rewrite list_count_add.
    apply lplus.
    apply eq.
Qed.

Theorem list_perm_swap {U} : ∀ (x y : U) l,
    list_permutation (y ꞉ x ꞉ l) (x ꞉ y ꞉ l).
Proof.
    intros x y l n.
    do 4 rewrite list_count_add.
    apply plus_3.
Qed.

Theorem list_perm_nil_eq {U} : ∀ l : list U, list_permutation [] l → [] = l.
Proof.
    intros l l_eq.
    destruct l as [|a l]; [>reflexivity|].
    specialize (l_eq a).
    rewrite list_count_add_eq in l_eq.
    rewrite list_count_end in l_eq.
    contradiction (nat_zero_suc l_eq).
Qed.

Theorem list_perm_lpart {U} : ∀ {al bl} (cl : list U),
    list_permutation al bl → list_permutation (al + cl) (bl + cl).
Proof.
    intros al bl cl eq n.
    do 2 rewrite list_count_conc.
    apply rplus.
    apply eq.
Qed.

Theorem list_perm_rpart {U} : ∀ al {bl cl : list U},
    list_permutation bl cl → list_permutation (al + bl) (al + cl).
Proof.
    intros al bl cl eq n.
    do 2 rewrite list_count_conc.
    apply lplus.
    apply eq.
Qed.

Theorem list_perm_conc {U} : ∀ al bl : list U,
    list_permutation (al + bl) (bl + al).
Proof.
    intros al bl n.
    apply list_count_comm.
Qed.

Theorem list_perm_split {U} : ∀ l1 l2 (x : U),
    list_permutation (l1 + x ꞉ l2) (x ꞉ (l1 + l2)).
Proof.
    intros l1 l2 a x.
    rewrite list_count_add.
    do 2 rewrite list_count_conc.
    rewrite list_count_add.
    apply plus_3.
Qed.

Theorem list_perm_add_eq {U} : ∀ (a : U) l1 l2,
    list_permutation (a ꞉ l1) (a ꞉ l2) → list_permutation l1 l2.
Proof.
    intros a l1 l2 eq x.
    specialize (eq x).
    do 2 rewrite list_count_add in eq.
    apply plus_lcancel in eq.
    exact eq.
Qed.

Theorem list_perm_conc_lcancel {U} : ∀ (l1 l2 l3 : list U),
    list_permutation (l1 + l2) (l1 + l3) → list_permutation l2 l3.
Proof.
    intros a l1 l2 eq x.
    specialize (eq x).
    do 2 rewrite list_count_conc in eq.
    apply plus_lcancel in eq.
    exact eq.
Qed.

Theorem list_perm_conc_rcancel {U} : ∀ (l1 l2 l3 : list U),
    list_permutation (l2 + l1) (l3 + l1) → list_permutation l2 l3.
Proof.
    intros a l1 l2 eq x.
    specialize (eq x).
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

Theorem list_perm_in' {U} : ∀ {al bl : list U},
    list_permutation al bl → (∀ x, in_list al x → in_list bl x).
Proof.
    intros al bl eq x x_in.
    rewrite list_count_in in x_in.
    rewrite eq in x_in.
    rewrite <- list_count_in in x_in.
    exact x_in.
Qed.

Theorem list_perm_in {U} : ∀ {al bl : list U},
    list_permutation al bl → (∀ x, in_list al x ↔ in_list bl x).
Proof.
    intros al bl eq x.
    split; apply list_perm_in'.
    -   exact eq.
    -   apply sym; exact eq.
Qed.

Theorem list_split_perm {U} : ∀ {l} {a : U}, in_list l a → ∃ l',
    list_permutation l (a ꞉ l').
Proof.
    intros l a a_in.
    pose proof (in_list_split a_in) as [l1 [l2 l_eq]].
    rewrite l_eq.
    exists (l1 + l2).
    apply list_perm_split.
Qed.

Theorem list_perm_single {U} : ∀ {x : U} {l}, list_permutation [x] l → l = [x].
Proof.
    intros x l l_perm.
    pose proof (in_list_single x) as x_in.
    apply (list_perm_in l_perm) in x_in.
    apply in_list_split in x_in as [l1 [l2 eq]]; subst l.
    pose proof (list_perm_split l1 l2 x) as eq.
    pose proof (trans l_perm eq) as eq2.
    apply list_perm_add_eq in eq2.
    apply list_perm_nil_eq in eq2.
    destruct l1.
    -   rewrite list_conc_lid.
        rewrite list_conc_lid in eq2.
        rewrite <- eq2.
        reflexivity.
    -   symmetry in eq2.
        contradiction (list_end_neq eq2).
Qed.

Theorem list_perm_reverse {U} : ∀ l : list U,
    list_permutation l (list_reverse l).
Proof.
    intros l x.
    apply list_count_reverse.
Qed.
