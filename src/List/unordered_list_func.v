Require Import init.

Require Import list_perm.
Require Export unordered_list_base.

Require Import equivalence.

Unset Keyed Unification.

Lemma ulist_image_wd A B : ∀ (f : A → B) a b, list_permutation a b →
    to_equiv (ulist_equiv B) (list_image a f) =
    to_equiv (ulist_equiv B) (list_image b f).
Proof.
    intros a b f ab.
    equiv_simpl.
    apply list_image_perm.
    exact ab.
Qed.
Definition ulist_image {A B} (l : ulist A) (f : A → B) :=
    unary_op (E := ulist_equiv A) (ulist_image_wd A B f) l.

Theorem ulist_image_end {A B : Type} : ∀ f : A → B,
    ulist_image ulist_end f = ulist_end.
Proof.
    intros f.
    unfold ulist_end, ulist_image; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_image_add {A B : Type} : ∀ a l (f : A → B),
    ulist_image (a ::: l) f = f a ::: ulist_image l f.
Proof.
    intros a l f.
    equiv_get_value l.
    unfold ulist_image, ulist_add; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_image_conc {A B : Type} : ∀ a b (f : A → B),
    ulist_image (a +++ b) f = ulist_image a f +++ ulist_image b f.
Proof.
    intros a b f.
    equiv_get_value a b.
    unfold ulist_image, ulist_conc; equiv_simpl.
    rewrite list_image_conc.
    apply list_perm_refl.
Qed.

Theorem ulist_image_comp {A B C : Type} :
    ∀ (l : ulist A) (f : A → B) (g : B → C),
    ulist_image (ulist_image l f) g = ulist_image l (λ x, g (f x)).
Proof.
    intros l f g.
    equiv_get_value l.
    unfold ulist_image; equiv_simpl.
    rewrite list_image_comp.
    apply list_perm_refl.
Qed.

Theorem ulist_prod2_wd' {A B} (op : A → A → B) : ∀ l1 l2 l : list A,
    list_permutation l1 l2 →
    list_permutation (list_prod2 op l1 l) (list_prod2 op l2 l).
Proof.
    intros l1 l2 l eq.
    induction l.
    -   cbn.
        apply list_perm_refl.
    -   cbn.
        apply uconc_wd.
        +   apply list_image_perm.
            exact eq.
        +   exact IHl.
Qed.
Lemma list_prod2_eq {A B} : ∀ (op : A → A → B) l1 l2,
    list_prod2 op l1 l2 =
    list_image (list_prod2 pair l1 l2) (λ x, op (fst x) (snd x)).
Proof.
    intros op l1 l2.
    induction l2.
    -   do 2 rewrite list_prod2_rend.
        rewrite list_image_end.
        reflexivity.
    -   do 2 rewrite list_prod2_radd.
        rewrite list_image_conc.
        rewrite IHl2.
        rewrite list_image_comp.
        cbn.
        reflexivity.
Qed.
Lemma list_prod2_count {A} : ∀ l1 l2 (a b : A),
    list_count (list_prod2 pair l1 l2) (a, b) =
    list_count l1 a * list_count l2 b.
Proof.
    intros l1 l2 a b.
    induction l2 as [|c l2].
    -   rewrite list_prod2_rend.
        cbn.
        rewrite mult_ranni.
        reflexivity.
    -   rewrite list_prod2_radd.
        rewrite list_count_conc.
        rewrite IHl2; clear IHl2.
        cbn.
        rewrite ldist.
        apply rplus; clear l2.
        induction l1 as [|d l1].
        +   rewrite list_image_end.
            cbn.
            rewrite mult_lanni.
            reflexivity.
        +   rewrite list_image_add.
            cbn.
            rewrite IHl1; clear IHl1.
            rewrite rdist.
            apply rplus.
            case_if [eq|neq].
            *   inversion eq.
                case_if [eq1|neq1]; case_if [eq2|neq2]; try contradiction.
                rewrite mult_lid.
                reflexivity.
            *   case_if [eq1|neq1].
                --  subst d.
                    case_if [eq2|neq2].
                    ++  subst; contradiction.
                    ++  rewrite mult_ranni; reflexivity.
                --  rewrite mult_lanni; reflexivity.
Qed.
Lemma ulist_prod2_wd A B (op : A → A → B) : ∀ al1 al2 bl1 bl2 : list A,
    list_permutation al1 al2 → list_permutation bl1 bl2 →
    to_equiv (ulist_equiv B) (list_prod2 op al1 bl1) =
    to_equiv (ulist_equiv B) (list_prod2 op al2 bl2).
Proof.
    intros al1 al2 bl1 bl2 a_eq b_eq.
    equiv_simpl.
    rewrite (list_prod2_eq op al1 bl1).
    rewrite (list_prod2_eq op al2 bl2).
    apply list_image_perm.
    intros [a b].
    do 2 rewrite list_prod2_count.
    rewrite (a_eq a).
    rewrite (b_eq b).
    reflexivity.
Qed.
Definition ulist_prod2 {A B} (op : A → A → B) :=
    binary_op (E := ulist_equiv A) (ulist_prod2_wd A B op).

Theorem ulist_prod2_lend {A B} : ∀ (op : A → A → B) l,
    ulist_prod2 op ulist_end l = ulist_end.
Proof.
    intros op l.
    equiv_get_value l.
    unfold ulist_end, ulist_prod2; equiv_simpl.
    rewrite list_prod2_lend.
    apply list_perm_refl.
Qed.

Theorem ulist_prod2_rend {A B} : ∀ (op : A → A → B) l,
    ulist_prod2 op l ulist_end = ulist_end.
Proof.
    intros op l.
    equiv_get_value l.
    unfold ulist_end, ulist_prod2; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_prod2_ladd {A B} : ∀ (op : A → A → B) l1 l2 a,
    ulist_prod2 op (a ::: l1) l2 =
    ulist_image l2 (λ x, op a x) +++ ulist_prod2 op l1 l2.
Proof.
    intros op l1 l2 a.
    equiv_get_value l1 l2.
    unfold ulist_conc, ulist_prod2, ulist_add, ulist_image; equiv_simpl.
    induction l2.
    1: apply list_perm_refl.
    cbn.
    do 2 rewrite list_prod2_radd.
    rewrite list_image_add.
    rewrite list_image_add.
    do 2 rewrite list_conc_add.
    apply list_perm_skip.
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
Proof.
    intros op l1 l2 a.
    equiv_get_value l1 l2.
    unfold ulist_conc, ulist_prod2, ulist_add, ulist_image; equiv_simpl.
    rewrite list_prod2_radd.
    apply list_perm_refl.
Qed.

Theorem ulist_prod2_lsingle {A B} : ∀ (op : A → A → B) l a,
    ulist_prod2 op (a ::: ulist_end) l =
    ulist_image l (λ x, op a x).
Proof.
    intros op l a.
    rewrite ulist_prod2_ladd.
    rewrite ulist_prod2_lend.
    apply ulist_conc_rid.
Qed.

Theorem ulist_prod2_rsingle {A B} : ∀ (op : A → A → B) l a,
    ulist_prod2 op l (a ::: ulist_end) =
    ulist_image l (λ x, op x a).
Proof.
    intros op l a.
    rewrite ulist_prod2_radd.
    rewrite ulist_prod2_rend.
    apply ulist_conc_rid.
Qed.
