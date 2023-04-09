Require Import init.

Require Import list.
Require Import unordered_list_base.

Require Import equivalence.

Lemma in_ulist_wd U : ∀ (a : U) l1 l2, list_permutation l1 l2 →
    in_list l1 a = in_list l2 a.
Proof.
    intros a l1 l2 eq.
    apply propositional_ext.
    apply (list_perm_in eq).
Qed.
Definition in_ulist {U} l a
    := unary_op (E := ulist_equiv U) (in_ulist_wd U a) l.

Lemma ulist_unique_wd' {U} : ∀ al bl : list U,
    list_permutation al bl → list_unique al → list_unique bl.
Proof.
    intros al bl albl al_uni.
    revert bl albl.
    list_unique_induction al al_uni as a a_nin IHal; intros bl albl.
    -   apply list_perm_nil_eq in albl.
        rewrite <- albl.
        apply list_unique_end.
    -   apply list_perm_split_eq in albl as [l1 [l2 [l_eq eq]]]; subst bl.
        specialize (IHal _ eq).
        apply list_unique_comm.
        rewrite list_conc_add.
        rewrite list_unique_add.
        split; [>|apply list_unique_comm; exact IHal].
        intros a_in.
        apply (trans2 (list_perm_comm _ _)) in eq.
        apply (list_perm_in eq) in a_in.
        contradiction.
Qed.

Lemma ulist_unique_wd U : ∀ l1 l2 : list U, list_permutation l1 l2 →
    list_unique l1 = list_unique l2.
Proof.
    intros l1 l2 eq.
    apply propositional_ext; split.
    -   exact (ulist_unique_wd' _ _ eq).
    -   apply list_perm_sym in eq.
        exact (ulist_unique_wd' _ _ eq).
Qed.
Definition ulist_unique {U} :=
    unary_op (E := ulist_equiv U) (ulist_unique_wd U).

Theorem in_ulist_end {U} : ∀ a : U, ¬in_ulist ulist_end a.
Proof.
    intros a contr.
    unfold in_ulist, ulist_end in contr; equiv_simpl in contr.
    contradiction (in_list_end contr).
Qed.

Theorem in_ulist_add_eq {U} : ∀ (a b : U) l,
    in_ulist (b ː l) a ↔ b = a ∨ in_ulist l a.
Proof.
    intros a b l.
    equiv_get_value l.
    unfold in_ulist, ulist_add; equiv_simpl.
    rewrite in_list_add_eq.
    reflexivity.
Qed.

Theorem in_ulist_add {U} : ∀ (a : U) l, in_ulist (a ː l) a.
Proof.
    intros a l.
    rewrite in_ulist_add_eq.
    left; reflexivity.
Qed.

Theorem in_ulist_single_eq {U} : ∀ (a b : U), in_ulist ⟦a⟧ b ↔ a = b.
Proof.
    intros a b.
    rewrite in_ulist_add_eq.
    rewrite (prop_is_false (in_ulist_end _)).
    rewrite or_rfalse.
    reflexivity.
Qed.

Theorem in_ulist_single {U} : ∀ a : U, in_ulist ⟦a⟧ a.
Proof.
    intros a.
    apply in_ulist_single_eq.
    reflexivity.
Qed.

Theorem in_ulist_conc {U} : ∀ {l1 l2} {a : U},
    in_ulist (l1 + l2) a → in_ulist l1 a ∨ in_ulist l2 a.
Proof.
    intros l1 l2 a.
    equiv_get_value l1 l2.
    unfold in_ulist, plus; equiv_simpl.
    apply in_list_conc.
Qed.

Theorem in_ulist_lconc {U} : ∀ l1 l2 {a : U},
    in_ulist l1 a → in_ulist (l1 + l2) a.
Proof.
    intros l1 l2 a.
    equiv_get_value l1 l2.
    unfold in_ulist, plus; equiv_simpl.
    apply in_list_lconc.
Qed.
Theorem in_ulist_rconc {U} : ∀ l1 l2 {a : U},
    in_ulist l2 a → in_ulist (l1 + l2) a.
Proof.
    intros l1 l2 a.
    equiv_get_value l1 l2.
    unfold in_ulist, plus; equiv_simpl.
    apply in_list_rconc.
Qed.

Theorem in_ulist_split {U} : ∀ {l} {a : U}, in_ulist l a → ∃ l', l = a ː l'.
Proof.
    intros l a a_in.
    equiv_get_value l.
    unfold in_ulist in a_in; equiv_simpl in a_in.
    apply list_split_perm in a_in as [l' eq].
    exists (to_equiv _ l').
    unfold ulist_add; equiv_simpl.
    exact eq.
Qed.

Theorem in_ulist_image {U V} : ∀ {l a} (f : U → V),
    in_ulist l a → in_ulist (ulist_image f l) (f a).
Proof.
    intros l a f.
    equiv_get_value l.
    unfold in_ulist, ulist_image; equiv_simpl.
    apply in_list_image.
Qed.

Theorem image_in_ulist {U V} : ∀ {l y} {f : U → V},
    in_ulist (ulist_image f l) y → ∃ x, f x = y ∧ in_ulist l x.
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

Theorem ulist_unique_end {U} : ulist_unique (@ulist_end U).
Proof.
    unfold ulist_unique, ulist_end; equiv_simpl.
    exact true.
Qed.

Theorem ulist_unique_add {U} : ∀ (a : U) l,
    ulist_unique (a ː l) ↔ ¬in_ulist l a ∧ ulist_unique l.
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_unique, in_ulist, ulist_add; equiv_simpl.
    rewrite list_unique_add.
    reflexivity.
Qed.

Theorem ulist_unique_single {U} : ∀ a : U, ulist_unique (a ː ulist_end).
Proof.
    intros a.
    unfold ulist_unique, ulist_add, ulist_end; equiv_simpl.
    apply list_unique_single.
Qed.

Tactic Notation "ulist_unique_induction" ident(l) ident(uni) "as"
    simple_intropattern(a) simple_intropattern(nin) simple_intropattern(IHl) :=
    move uni before l;
    induction l as [|a l IHl] using ulist_induction;
    [>|
        rewrite ulist_unique_add in uni;
        specialize (IHl (rand uni));
        destruct uni as [nin uni]
    ].

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

Theorem ulist_unique_lconc {U} : ∀ (l1 l2 : ulist U),
    ulist_unique (l1 + l2) → ulist_unique l1.
Proof.
    intros l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_unique, plus; equiv_simpl.
    apply list_unique_lconc.
Qed.

Theorem ulist_unique_rconc {U} : ∀ (l1 l2 : ulist U),
    ulist_unique (l1 + l2) → ulist_unique l2.
Proof.
    intros l1 l2.
    rewrite plus_comm.
    apply ulist_unique_lconc.
Qed.

Theorem ulist_unique_conc {U} : ∀ (l1 l2 : ulist U),
    ulist_unique (l1 + l2) → (∀ x, in_ulist l1 x → ¬in_ulist l2 x).
Proof.
    intros l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_unique, plus, in_ulist; equiv_simpl.
    intros uni x.
    equiv_simpl.
    apply (list_unique_conc _ _ uni).
Qed.

Theorem ulist_image_unique {U V} : ∀ (l : ulist U) (f : U → V),
    ulist_unique (ulist_image f l) → ulist_unique l.
Proof.
    intros l f.
    equiv_get_value l.
    unfold ulist_image, ulist_unique; equiv_simpl.
    apply list_image_unique.
Qed.
