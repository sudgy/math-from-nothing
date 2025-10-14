Require Import init.

Require Import list.
Require Import unordered_list_base.
Require Import unordered_list_in.

Require Import nat.
Require Import equivalence.

Lemma ulist_size_wd U : ∀ l1 l2 : list U, list_permutation l1 l2 →
    list_size l1 = list_size l2.
Proof.
    induction l1 as [|a l1]; intros l2 eq.
    -   apply list_perm_nil_eq in eq.
        destruct eq.
        reflexivity.
    -   apply list_perm_split_eq in eq as [l3 [l4 [l_eq eq]]]; subst l2.
        specialize (IHl1 _ eq).
        rewrite list_size_comm.
        rewrite list_conc_add.
        do 2 rewrite list_size_add.
        rewrite IHl1.
        rewrite list_size_comm.
        reflexivity.
Qed.
Definition ulist_size {U} := unary_op (E := ulist_equiv U) (ulist_size_wd U).

Definition ulist_count {U} (l : ulist U) (a : U)
    := unary_op (E := ulist_equiv U) (λ l1 l2 eq, eq a) l.

Definition ulist_constant {U} (a : U) (n : nat)
    := to_equiv (ulist_equiv U) (list_constant a n).

Theorem ulist_size_end {U} : ulist_size (@ulist_end U) = 0.
Proof.
    unfold ulist_size, ulist_end; equiv_simpl.
    apply list_size_end.
Qed.

Theorem ulist_size_add {U} : ∀ (a : U) l,
    ulist_size (a ː l) = nat_suc (ulist_size l).
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_size, ulist_add; equiv_simpl.
    apply list_size_add.
Qed.

Theorem ulist_size_single {U} : ∀ x : U, ulist_size ⟦x⟧ = 1.
Proof.
    intros x.
    rewrite ulist_size_add, ulist_size_end.
    reflexivity.
Qed.

Theorem ulist_size_conc {U} : ∀ l1 l2 : ulist U,
    ulist_size (l1 + l2) = ulist_size l1 + ulist_size l2.
Proof.
    intros l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_size, plus at 1; equiv_simpl.
    apply list_size_conc.
Qed.

Theorem ulist_image_size {A B} : ∀ l (f : A → B),
    ulist_size (ulist_image f l) = ulist_size l.
Proof.
    intros l f.
    equiv_get_value l.
    unfold ulist_size, ulist_image; equiv_simpl.
    apply list_image_size.
Qed.

Theorem ulist_count_eq {A} : ∀ a b : ulist A,
    (∀ x, ulist_count a x = ulist_count b x) → a = b.
Proof.
    intros a b eq.
    equiv_get_value a b.
    equiv_simpl.
    intros x.
    specialize (eq x).
    unfold ulist_count in eq; equiv_simpl in eq.
    exact eq.
Qed.

Theorem ulist_count_end {U} : ∀ (x : U), ulist_count ⟦⟧ x = 0.
Proof.
    intros x.
    unfold ulist_count, ulist_end; equiv_simpl.
    apply list_count_end.
Qed.

Theorem ulist_count_add {U} : ∀ (x y : U) a,
    ulist_count (x ː a) y = (If x = y then 1 else 0) + ulist_count a y.
Proof.
    intros x y a.
    equiv_get_value a.
    unfold ulist_count, ulist_add; equiv_simpl.
    apply list_count_add.
Qed.

Theorem ulist_count_add_eq {U} : ∀ (x : U) a,
    ulist_count (x ː a) x = nat_suc (ulist_count a x).
Proof.
    intros x a.
    rewrite ulist_count_add.
    rewrite (if_true (Logic.eq_refl _)).
    reflexivity.
Qed.

Theorem ulist_count_add_neq {U} : ∀ {x y : U} {a}, x ≠ y →
    ulist_count (x ː a) y = ulist_count a y.
Proof.
    intros x y a neq.
    rewrite ulist_count_add.
    rewrite (if_false neq).
    rewrite plus_lid.
    reflexivity.
Qed.

Theorem ulist_count_single {U} : ∀ (x y : U),
    ulist_count ⟦x⟧ y = If x = y then 1 else 0.
Proof.
    intros x y.
    rewrite ulist_count_add, ulist_count_end.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem ulist_count_single_eq {U} : ∀ x : U, ulist_count ⟦x⟧ x = 1.
Proof.
    intros x.
    rewrite ulist_count_add_eq, ulist_count_end.
    reflexivity.
Qed.

Theorem ulist_count_single_neq {U} : ∀ x y : U, x ≠ y → ulist_count ⟦x⟧ y = 0.
Proof.
    intros x y neq.
    rewrite (ulist_count_add_neq neq).
    apply ulist_count_end.
Qed.

Theorem ulist_count_conc {U} : ∀ l1 l2 (a : U),
    ulist_count (l1 + l2) a = ulist_count l1 a + ulist_count l2 a.
Proof.
    intros l1 l2 a.
    equiv_get_value l1 l2.
    unfold ulist_count, plus at 1; equiv_simpl.
    apply list_count_conc.
Qed.

Theorem ulist_count_in {U} : ∀ l (a : U), in_ulist l a ↔ 0 ≠ ulist_count l a.
Proof.
    intros l a.
    equiv_get_value l.
    unfold in_ulist, ulist_count; equiv_simpl.
    apply list_count_in.
Qed.

Theorem ulist_count_nin {U} : ∀ l (a : U), ¬in_ulist l a ↔ 0 = ulist_count l a.
Proof.
    intros l a.
    rewrite ulist_count_in.
    apply not_not.
Qed.

Theorem ulist_count_unique {U} : ∀ l (a : U), ulist_unique l → ulist_count l a ≤ 1.
Proof.
    intros l x.
    equiv_get_value l.
    unfold ulist_unique, ulist_count; equiv_simpl.
    apply list_count_unique.
Qed.

Theorem ulist_count_in_unique {U} : ∀ l (a : U), ulist_unique l → in_ulist l a →
    ulist_count l a = 1.
Proof.
    intros l a.
    equiv_get_value l.
    unfold ulist_unique, in_ulist, ulist_count; equiv_simpl.
    apply list_count_in_unique.
Qed.

Theorem ulist_constant_zero {U} : ∀ a : U, ulist_constant a 0 = ⟦⟧.
Proof.
    reflexivity.
Qed.

Theorem ulist_constant_suc {U} : ∀ (a : U) n,
    ulist_constant a (nat_suc n) = a ː ulist_constant a n.
Proof.
    intros a n.
    unfold ulist_constant, ulist_add; equiv_simpl.
    rewrite list_constant_suc.
    apply refl.
Qed.

Theorem ulist_constant_one {U} : ∀ a : U, ulist_constant a 1 = ⟦a⟧.
Proof.
    intros a.
    rewrite ulist_constant_suc.
    rewrite ulist_constant_zero.
    reflexivity.
Qed.

Theorem in_ulist_constant {U} : ∀ (a b : U) n,
    in_ulist (ulist_constant a n) b → a = b.
Proof.
    intros a b n.
    unfold in_ulist, ulist_constant; equiv_simpl.
    apply in_list_constant.
Qed.

Theorem ulist_count_constant {U} : ∀ (a : U) n,
    ulist_count (ulist_constant a n) a = n.
Proof.
    intros a n.
    unfold ulist_count, ulist_constant; equiv_simpl.
    apply list_count_constant.
Qed.
