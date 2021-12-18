Require Import init.

Require Import list_perm.
Require Export unordered_list_base.

Require Import equivalence.

Lemma ulist_image_wd A B : ∀ a b (f : A → B), list_permutation a b →
        to_equiv_type (ulist_equiv B) (list_image a f) =
        to_equiv_type (ulist_equiv B) (list_image b f).
    intros a b f ab.
    equiv_simpl.
    apply list_image_perm.
    exact ab.
Qed.
Definition ulist_image {A B} :=
    binary_rop (E := ulist_equiv A) (ulist_image_wd A B).

Theorem ulist_image_end {A B : Type} : ∀ f : A → B,
        ulist_image ulist_end f = ulist_end.
    intros f.
    unfold ulist_end, ulist_image; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_image_add {A B : Type} : ∀ a l (f : A → B),
        ulist_image (a ::: l) f = f a ::: ulist_image l f.
    intros a l f.
    equiv_get_value l.
    unfold ulist_image, ulist_add; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_image_conc {A B : Type} : ∀ a b (f : A → B),
        ulist_image (a +++ b) f = ulist_image a f +++ ulist_image b f.
    intros a b f.
    equiv_get_value a b.
    unfold ulist_image, ulist_conc; equiv_simpl.
    rewrite list_image_conc.
    apply list_perm_refl.
Qed.

Theorem ulist_image_comp {A B C : Type} :
        ∀ (l : ulist A) (f : A → B) (g : B → C),
        ulist_image (ulist_image l f) g = ulist_image l (λ x, g (f x)).
    intros l f g.
    equiv_get_value l.
    unfold ulist_image; equiv_simpl.
    rewrite list_image_comp.
    apply list_perm_refl.
Qed.

Lemma ulist_prod2_base_wd {A B} (op : A → A → B) : ∀ (l1 l2 : list A) a,
        list_permutation l1 l2 →
        list_permutation (list_prod2_base op l1 a) (list_prod2_base op l2 a).
    intros l1 l2 a eq.
    induction eq.
    -   cbn.
        apply list_perm_refl.
    -   cbn.
        apply uadd_wd.
        exact IHeq.
    -   cbn.
        apply list_perm_swap.
    -   exact (list_perm_trans IHeq1 IHeq2).
Qed.
Theorem ulist_prod2_wd' {A B} (op : A → A → B) : ∀ l1 l2 l : list A,
        list_permutation l1 l2 →
        list_permutation (list_prod2 op l1 l) (list_prod2 op l2 l).
    intros l1 l2 l eq.
    induction l.
    -   cbn.
        apply list_perm_refl.
    -   cbn.
        apply uconc_wd.
        +   apply ulist_prod2_base_wd.
            exact eq.
        +   exact IHl.
Qed.
Lemma ulist_prod2_wd A B (op : A → A → B) : ∀ al1 al2 bl1 bl2 : list A,
        list_permutation al1 al2 → list_permutation bl1 bl2 →
        to_equiv_type (ulist_equiv B) (list_prod2 op al1 bl1) =
        to_equiv_type (ulist_equiv B) (list_prod2 op al2 bl2).
    intros al1 al2 bl1 bl2 a_eq b_eq.
    equiv_simpl.
    induction b_eq.
    -   cbn.
        apply list_perm_refl.
    -   cbn.
        apply uconc_wd.
        +   apply (ulist_prod2_base_wd _ _ _ _ a_eq).
        +   exact IHb_eq.
    -   cbn.
        do 2 rewrite list_conc_assoc.
        apply uconc_wd.
        +   apply (list_perm_trans (list_perm_conc _ _)).
            induction a_eq.
            *   cbn.
                apply list_perm_refl.
            *   cbn.
                apply list_perm_skip.
                apply (list_perm_trans (list_perm_split _ _ _)).
                apply (list_perm_trans2 (list_perm_sym(list_perm_split _ _ _))).
                apply list_perm_skip.
                exact IHa_eq.
            *   cbn.
                apply list_perm_swap2.
                apply (list_perm_trans (list_perm_split _ _ _)).
                apply (list_perm_trans2 (list_perm_sym(list_perm_split _ _ _))).
                apply (list_perm_trans
                    (list_perm_split (op y0 y :: list_prod2_base op l0 x) _ _)).
                apply (list_perm_trans2 (list_perm_sym
                    (list_perm_split(op x0 y :: list_prod2_base op l0 x) _ _))).
                cbn.
                apply list_perm_swap.
            *   exact (list_perm_trans IHa_eq1 IHa_eq2).
        +   apply ulist_prod2_wd'.
            exact a_eq.
    -   pose proof (ulist_prod2_wd' op _ _ l' a_eq) as eq.
        apply list_perm_sym in eq.
        apply (list_perm_trans IHb_eq1).
        apply (list_perm_trans eq).
        exact IHb_eq2.
Qed.
Definition ulist_prod2 {A B} (op : A → A → B) :=
    binary_op (E := ulist_equiv A) (ulist_prod2_wd A B op).

Theorem ulist_prod2_lend {A B} : ∀ (op : A → A → B) l,
        ulist_prod2 op ulist_end l = ulist_end.
    intros op l.
    equiv_get_value l.
    unfold ulist_end, ulist_prod2; equiv_simpl.
    rewrite list_prod2_lend.
    apply list_perm_refl.
Qed.

Theorem ulist_prod2_rend {A B} : ∀ (op : A → A → B) l,
        ulist_prod2 op l ulist_end = ulist_end.
    intros op l.
    equiv_get_value l.
    unfold ulist_end, ulist_prod2; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_prod2_ladd {A B} : ∀ (op : A → A → B) l1 l2 a,
        ulist_prod2 op (a ::: l1) l2 =
        ulist_image l2 (λ x, op a x) +++ ulist_prod2 op l1 l2.
    intros op l1 l2 a.
    equiv_get_value l1 l2.
    unfold ulist_conc, ulist_prod2, ulist_add, ulist_image; equiv_simpl.
    induction l2.
    1: apply list_perm_refl.
    cbn.
    apply list_perm_skip.
    rewrite list_prod2_base_image.
    pose proof (list_perm_conc (list_image l2 (λ x, op a x))
        (list_image l1 (λ x, op x a0))) as eq.
    apply (list_perm_lpart (list_prod2 op l1 l2)) in eq.
    apply list_perm_sym in eq.
    do 2 rewrite <- list_conc_assoc in eq.
    apply (list_perm_trans2 eq).
    apply list_perm_rpart.
    exact IHl2.
Qed.

Theorem ulist_prod2_radd {A B} : ∀ (op : A → A → B) l1 l2 a,
        ulist_prod2 op l1 (a ::: l2) =
        ulist_image l1 (λ x, op x a) +++ ulist_prod2 op l1 l2.
    intros op l1 l2 a.
    equiv_get_value l1 l2.
    unfold ulist_conc, ulist_prod2, ulist_add, ulist_image; equiv_simpl.
    rewrite list_prod2_base_image.
    apply list_perm_refl.
Qed.

Theorem ulist_prod2_lsingle {A B} : ∀ (op : A → A → B) l a,
        ulist_prod2 op (a ::: ulist_end) l =
        ulist_image l (λ x, op a x).
    intros op l a.
    rewrite ulist_prod2_ladd.
    rewrite ulist_prod2_lend.
    apply ulist_conc_rid.
Qed.

Theorem ulist_prod2_rsingle {A B} : ∀ (op : A → A → B) l a,
        ulist_prod2 op l (a ::: ulist_end) =
        ulist_image l (λ x, op x a).
    intros op l a.
    rewrite ulist_prod2_radd.
    rewrite ulist_prod2_rend.
    apply ulist_conc_rid.
Qed.
