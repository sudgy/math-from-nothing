Require Import init.

Require Import list_perm.

Require Import equivalence.

Local Instance list_perm_reflexive U : Reflexive _ := {
    refl := @list_perm_refl U
}.
Local Instance list_perm_symmetric U : Symmetric _ := {
    sym := @list_perm_sym U
}.
Local Instance list_perm_transitive U : Transitive _ := {
    trans := @list_perm_trans U
}.

Definition ulist_equiv U := make_equiv _
    (list_perm_reflexive U) (list_perm_symmetric U) (list_perm_transitive U).
Notation "'ulist' U" := (equiv_type (ulist_equiv U)) (at level 1).

Definition ulist_end {U} := to_equiv (ulist_equiv U) list_end.

Lemma uadd_wd U : ∀ (a : U) l1 l2,
    list_permutation l1 l2 → list_permutation (a ꞉ l1) (a ꞉ l2).
Proof.
    intros a l1 l2 l_perm.
    apply list_perm_skip.
    exact l_perm.
Qed.
Definition ulist_add {U} (a : U)
    := unary_op (unary_self_wd (E := ulist_equiv U) (uadd_wd U a)).
(** Like with list_add, this is NOT a colon!  It is actually U+02D0,
modifier letter triangular colon.  I have it mapped to \uadd in ibus. *)
Infix "ː" := ulist_add (at level 49, right associativity) : list_scope.
(** These are \llbracket and \rrbracket, U+27E6 and U+27E7. *)
Notation "⟦⟧" := ulist_end : list_scope.
Notation "⟦ a ⟧" := (a ː ⟦⟧) : list_scope.
Notation "⟦ x ; y ; .. ; z ⟧" :=
    (x ː (y ː .. (z ː ⟦⟧) ..))
    (format "⟦ '[' x ; '/' y ; '/' .. ; '/' z ']' ⟧") : list_scope.

Theorem ulist_induction {U} : ∀ S : ulist U → Prop,
    S ⟦⟧ → (∀ a l, S l → S (a ː l)) → ∀ l, S l.
Proof.
    intros S S_end S_add l.
    equiv_get_value l.
    induction l.
    -   exact S_end.
    -   assert (to_equiv (ulist_equiv U) (a ꞉ l) =
            a ː (to_equiv (ulist_equiv U) l)) as eq.
        {
            unfold ulist_add; equiv_simpl.
            apply list_perm_refl.
        }
        rewrite eq.
        apply S_add.
        exact IHl.
Qed.

Theorem ulist_destruct {U} : ∀ S : ulist U → Prop,
    S ⟦⟧ → (∀ a l, S (a ː l)) → ∀ l, S l.
Proof.
    intros S S_end S_ind l.
    induction l using ulist_induction.
    -   exact S_end.
    -   apply S_ind.
Qed.

Theorem ulist_end_neq {U} : ∀ (a : U) l, a ː l ≠ ⟦⟧.
Proof.
    intros a l contr.
    equiv_get_value l.
    unfold ulist_add, ulist_end in contr; equiv_simpl in contr.
    apply list_perm_sym in contr.
    apply list_perm_nil_eq in contr.
    inversion contr.
Qed.

Theorem ulist_single_eq {U} : ∀ (a b : U), ⟦a⟧ = ⟦b⟧ → a = b.
Proof.
    intros a b eq.
    unfold ulist_add, ulist_end in eq; equiv_simpl in eq.
    pose proof (list_perm_single eq) as eq2.
    inversion eq2.
    reflexivity.
Qed.

Lemma uconc_wd U : ∀ al1 al2 bl1 bl2 : list U,
    list_permutation al1 al2 → list_permutation bl1 bl2 →
    list_permutation (al1 + bl1) (al2 + bl2).
Proof.
    intros al1 al2 bl1 bl2 eq1 eq2.
    pose proof (list_perm_rpart al1 eq2).
    pose proof (list_perm_lpart bl2 eq1).
    exact (list_perm_trans H H0).
Qed.
Global Instance ulist_plus U : Plus (ulist U) := {
    plus := binary_op (binary_self_wd (E := ulist_equiv U) (uconc_wd U))
}.

Theorem ulist_add_conc_add {U} : ∀ (a : U) l1 l2,
    a ː (l1 + l2) = (a ː l1) + l2.
Proof.
    intros a l1 l2.
    equiv_get_value l1 l2.
    unfold plus, ulist_add; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_add_conc {U} : ∀ (a : U) l, a ː l = (⟦a⟧) + l.
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_end, ulist_add, plus; equiv_simpl.
    apply list_perm_refl.
Qed.

Global Instance ulist_zero U : Zero (ulist U) := {
    zero := ⟦⟧
}.

Global Instance ulist_plus_comm U : PlusComm (ulist U).
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold plus; equiv_simpl.
    apply list_perm_conc.
Qed.

Global Instance ulist_plus_lid U : PlusLid (ulist U).
Proof.
    split.
    intros l.
    equiv_get_value l.
    unfold ulist_end, plus, zero; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_conc_lid {U} : ∀ l : ulist U, ⟦⟧ + l = l.
Proof.
    exact plus_lid.
Qed.

Theorem ulist_conc_rid {U} : ∀ l : ulist U, l + ⟦⟧ = l.
Proof.
    exact plus_rid.
Qed.

Global Instance ulist_plus_assoc U : PlusAssoc (ulist U).
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold plus; equiv_simpl.
    rewrite plus_assoc.
    apply list_perm_refl.
Qed.

Theorem ulist_swap {U} : ∀ (a b : U) l, a ː b ː l = b ː a ː l.
Proof.
    intros a b l.
    equiv_get_value l.
    unfold ulist_add; equiv_simpl.
    apply list_perm_swap.
Qed.

Theorem ulist_skip {U} : ∀ (a : U) l1 l2, a ː l1 = a ː l2 → l1 = l2.
Proof.
    intros a l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_add; equiv_simpl.
    apply list_perm_add_eq.
Qed.

Global Instance ulist_plus_lcancel U : PlusLcancel (ulist U).
Proof.
    split.
    intros l1 l2 l3.
    equiv_get_value l1 l2 l3.
    unfold plus; equiv_simpl.
    apply list_perm_conc_lcancel.
Qed.

Unset Keyed Unification.

Theorem list_image_perm {U V} : ∀ al bl (f : U → V),
    list_permutation al bl →
    list_permutation (list_image f al) (list_image f bl).
Proof.
    intros al bl f albli x.
    revert bl albli.
    induction al as [|a al]; intros.
    -   apply list_perm_nil_eq in albli.
        subst bl.
        rewrite list_image_end.
        cbn.
        reflexivity.
    -   assert (in_list (a ꞉ al) a) as a_in by (left; reflexivity).
        apply (list_perm_in albli) in a_in.
        apply in_list_split in a_in as [l1 [l2 eq]]; subst bl.
        pose proof (list_perm_split l1 l2 a) as eq.
        pose proof (list_perm_trans albli eq) as eq2.
        apply list_perm_add_eq in eq2.
        specialize (IHal _ eq2).
        rewrite list_image_conc.
        do 2 rewrite list_image_add.
        rewrite list_count_conc.
        do 2 rewrite list_count_add.
        rewrite IHal.
        rewrite list_image_conc, list_count_conc.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.

Lemma ulist_image_wd A B : ∀ (f : A → B) a b, list_permutation a b →
    to_equiv (ulist_equiv B) (list_image f a) =
    to_equiv (ulist_equiv B) (list_image f b).
Proof.
    intros a b f ab.
    equiv_simpl.
    apply list_image_perm.
    exact ab.
Qed.
Definition ulist_image {A B} (f : A → B) :=
    unary_op (E := ulist_equiv A) (ulist_image_wd A B f).

Theorem ulist_image_end {A B : Type} : ∀ f : A → B,
    ulist_image f ⟦⟧ = ⟦⟧.
Proof.
    intros f.
    unfold ulist_end, ulist_image; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_image_add {A B : Type} : ∀ a l (f : A → B),
    ulist_image f (a ː l) = f a ː ulist_image f l.
Proof.
    intros a l f.
    equiv_get_value l.
    unfold ulist_image, ulist_add; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_image_conc {A B : Type} : ∀ a b (f : A → B),
    ulist_image f (a + b) = ulist_image f a + ulist_image f b.
Proof.
    intros a b f.
    equiv_get_value a b.
    unfold ulist_image, plus; equiv_simpl.
    rewrite list_image_conc.
    apply list_perm_refl.
Qed.

Theorem ulist_image_comp {A B C : Type} :
    ∀ (l : ulist A) (f : A → B) (g : B → C),
    ulist_image g (ulist_image f l) = ulist_image (λ x, g (f x)) l.
Proof.
    intros l f g.
    equiv_get_value l.
    unfold ulist_image; equiv_simpl.
    rewrite list_image_comp.
    apply list_perm_refl.
Qed.
