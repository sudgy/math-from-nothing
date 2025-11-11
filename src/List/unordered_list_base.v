Require Import init.

Require Import list_perm.

Require Import equivalence.

Definition ulist_equiv U := make_equiv _
    (list_perm_refl U) (list_perm_sym U) (list_perm_trans U).
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
    unfold ulist_end in S_end.
    equiv_get_value l.
    induction l.
    -   exact S_end.
    -   specialize (S_add a _ IHl).
        unfold ulist_add in S_add; equiv_simpl in S_add.
        exact S_add.
Qed.

Theorem ulist_destruct {U} : ∀ S : ulist U → Prop,
    S ⟦⟧ → (∀ a l, S (a ː l)) → ∀ l, S l.
Proof.
    intros S S_end S_ind l.
    induction l using ulist_induction.
    -   exact S_end.
    -   apply S_ind.
Qed.

Theorem ulist_end_neq {U} : ∀ {a : U} {l}, a ː l ≠ ⟦⟧.
Proof.
    intros a l contr.
    symmetry in contr.
    equiv_get_value l.
    unfold ulist_add, ulist_end in contr; equiv_simpl in contr.
    apply list_perm_nil_eq in contr.
    symmetry in contr.
    exact (list_end_neq contr).
Qed.

Theorem ulist_single_eq {U} : ∀ {a b : U}, ⟦a⟧ = ⟦b⟧ → a = b.
Proof.
    intros a b eq.
    unfold ulist_add, ulist_end in eq; equiv_simpl in eq.
    pose proof (list_perm_single eq) as eq2.
    apply list_single_eq in eq2.
    symmetry; exact eq2.
Qed.

Theorem ulist_swap {U} : ∀ (a b : U) l, a ː b ː l = b ː a ː l.
Proof.
    intros a b l.
    equiv_get_value l.
    unfold ulist_add; equiv_simpl.
    apply list_perm_swap.
Qed.

Theorem ulist_add_eq {U} : ∀ {a : U} {l1 l2}, a ː l1 = a ː l2 → l1 = l2.
Proof.
    intros a l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_add; equiv_simpl.
    apply list_perm_add_eq.
Qed.

Lemma uconc_wd U : ∀ al1 al2 bl1 bl2 : list U,
    list_permutation al1 al2 → list_permutation bl1 bl2 →
    list_permutation (al1 + bl1) (al2 + bl2).
Proof.
    intros al1 al2 bl1 bl2 eq1 eq2.
    pose proof (list_perm_rpart al1 eq2) as eq3.
    pose proof (list_perm_lpart bl2 eq1) as eq4.
    exact (trans eq3 eq4).
Qed.
Global Instance ulist_plus U : Plus (ulist U) := {
    plus := binary_op (binary_self_wd (E := ulist_equiv U) (uconc_wd U))
}.

Theorem ulist_conc_add {U} : ∀ (a : U) l1 l2,
    (a ː l1) + l2 = a ː (l1 + l2).
Proof.
    intros a l1 l2.
    equiv_get_value l1 l2.
    unfold plus, ulist_add; equiv_simpl.
    rewrite list_conc_add.
    apply refl.
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
    apply list_perm_comm.
Qed.

Global Instance ulist_plus_lid U : PlusLid (ulist U).
Proof.
    split.
    intros l.
    equiv_get_value l.
    unfold ulist_end, plus, zero; equiv_simpl.
    rewrite list_conc_lid.
    apply refl.
Qed.

Theorem ulist_conc_lid {U} : ∀ l : ulist U, ⟦⟧ + l = l.
Proof.
    exact plus_lid.
Qed.

Theorem ulist_conc_rid {U} : ∀ l : ulist U, l + ⟦⟧ = l.
Proof.
    exact plus_rid.
Qed.

Theorem ulist_conc_single {U} : ∀ (a : U) l, (⟦a⟧) + l = a ː l.
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_end, ulist_add, plus; equiv_simpl.
    rewrite list_conc_single.
    apply refl.
Qed.

Global Instance ulist_plus_assoc U : PlusAssoc (ulist U).
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold plus; equiv_simpl.
    rewrite plus_assoc.
    apply refl.
Qed.

Global Instance ulist_plus_lcancel U : PlusLcancel (ulist U).
Proof.
    split.
    intros l1 l2 l3.
    equiv_get_value l1 l2 l3.
    unfold plus; equiv_simpl.
    apply list_perm_conc_lcancel.
Qed.

Theorem ulist_image_wd {U V} : ∀ (f : U → V) al bl,
    list_permutation al bl →
    to_equiv (ulist_equiv V) (list_image f al) =
    to_equiv (ulist_equiv V) (list_image f bl).
Proof.
    intros f al bl albli.
    equiv_simpl.
    intros x.
    revert bl albli.
    induction al as [|a al]; intros.
    -   apply list_perm_nil_eq in albli.
        subst bl.
        reflexivity.
    -   apply list_perm_split_eq in albli as [l1 [l2 [l_eq l_perm]]]; subst bl.
        specialize (IHal _ l_perm).
        rewrite list_image_conc.
        do 2 rewrite list_image_add.
        rewrite list_count_conc.
        do 2 rewrite list_count_add.
        rewrite IHal.
        rewrite list_image_conc, list_count_conc.
        apply plus_3.
Qed.

Definition ulist_image {A B} (f : A → B) :=
    unary_op (E := ulist_equiv A) (@ulist_image_wd A B f).

Theorem ulist_image_end {A B : Type} : ∀ f : A → B,
    ulist_image f ⟦⟧ = ⟦⟧.
Proof.
    intros f.
    unfold ulist_end, ulist_image; equiv_simpl.
    rewrite list_image_end.
    apply refl.
Qed.

Theorem ulist_image_add {A B : Type} : ∀ a l (f : A → B),
    ulist_image f (a ː l) = f a ː ulist_image f l.
Proof.
    intros a l f.
    equiv_get_value l.
    unfold ulist_image, ulist_add; equiv_simpl.
    rewrite list_image_add.
    apply refl.
Qed.

Theorem ulist_image_single {A B : Type} : ∀ a (f : A → B),
    ulist_image f ⟦a⟧ = ⟦f a⟧.
Proof.
    intros a f.
    rewrite ulist_image_add, ulist_image_end.
    reflexivity.
Qed.

Theorem ulist_image_conc {A B : Type} : ∀ a b (f : A → B),
    ulist_image f (a + b) = ulist_image f a + ulist_image f b.
Proof.
    intros a b f.
    equiv_get_value a b.
    unfold ulist_image, plus; equiv_simpl.
    rewrite list_image_conc.
    apply refl.
Qed.

Theorem ulist_image_comp {A B C : Type} :
    ∀ (l : ulist A) (f : A → B) (g : B → C),
    ulist_image g (ulist_image f l) = ulist_image (λ x, g (f x)) l.
Proof.
    intros l f g.
    equiv_get_value l.
    unfold ulist_image; equiv_simpl.
    rewrite list_image_comp.
    apply refl.
Qed.

Theorem ulist_flatten1_wd U : ∀ l1 l2 : list (list U),
    list_permutation l1 l2 →
    to_equiv (ulist_equiv U) (list_flatten l1) =
    to_equiv (ulist_equiv U) (list_flatten l2).
Proof.
    intros l1 l2 eq.
    equiv_simpl.
    revert l2 eq.
    induction l1 as [|al l1 IHl]; intros.
    -   apply list_perm_nil_eq in eq.
        rewrite <- eq.
        apply refl.
    -   apply list_perm_split_eq in eq as [l21 [l22 [eq1 eq2]]].
        subst l2.
        rewrite list_flatten_conc.
        apply (trans2 (list_perm_comm _ _)).
        do 2 rewrite list_flatten_add.
        rewrite <- plus_assoc.
        apply list_perm_rpart.
        apply (trans2 (list_perm_comm _ _)).
        rewrite <- list_flatten_conc.
        apply IHl.
        exact eq2.
Qed.
Definition ulist_flatten1 {U} :=
    unary_op (E := ulist_equiv (list U)) (ulist_flatten1_wd U).

Definition ulist_flatten {U} (l : ulist (ulist U)) :=
    ulist_flatten1 (ulist_image from_equiv l).

Theorem ulist_flatten_end {U} : ulist_flatten (U := U) ⟦⟧ = ⟦⟧.
Proof.
    unfold ulist_flatten.
    rewrite ulist_image_end.
    unfold ulist_flatten1, ulist_end; equiv_simpl.
    rewrite list_flatten_end.
    apply refl.
Qed.

Theorem ulist_flatten_add {U} :
    ∀ (a : ulist U) l, ulist_flatten (a ː l) = a + ulist_flatten l.
Proof.
    intros a l.
    unfold ulist_flatten.
    rewrite ulist_image_add.
    equiv_get_value l a.
    unfold ulist_flatten1, plus, ulist_add, ulist_image; equiv_simpl.
    rewrite list_flatten_add.
    apply list_perm_lpart.
    assert (to_equiv (ulist_equiv U) (from_equiv (to_equiv (ulist_equiv U) a))
        = to_equiv (ulist_equiv U) a) as eq.
    {
        rewrite from_equiv_eq.
        reflexivity.
    }
    equiv_simpl in eq.
    exact eq.
Qed.

Theorem ulist_flatten_single {U} : ∀ a : ulist U, ulist_flatten ⟦a⟧ = a.
Proof.
    intros a.
    rewrite ulist_flatten_add.
    rewrite ulist_flatten_end.
    apply ulist_conc_rid.
Qed.

Theorem ulist_flatten_conc {U} : ∀ l1 l2 : ulist (ulist U),
    ulist_flatten (l1 + l2) = ulist_flatten l1 + ulist_flatten l2.
Proof.
    intros l1 l2.
    induction l1 as [|a l1] using ulist_induction.
    -   rewrite ulist_flatten_end.
        do 2 rewrite ulist_conc_lid.
        reflexivity.
    -   rewrite ulist_conc_add.
        do 2 rewrite ulist_flatten_add.
        rewrite IHl1.
        apply plus_assoc.
Qed.
