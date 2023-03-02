Require Import init.

Require Export list_base.
Require Export nat.

Set Implicit Arguments.

Fixpoint list_image (A B : Type) (l : list A) (f : A → B) :=
    match l with
    | [] => []
    | a :: l' => f a :: list_image l' f
    end.
Arguments list_image : simpl never.

Theorem list_image_end {A B : Type} : ∀ (f : A → B), list_image [] f = [].
Proof.
    reflexivity.
Qed.

Theorem list_image_add {A B : Type} : ∀ a l (f : A → B),
    list_image (a :: l) f = f a :: list_image l f.
Proof.
    reflexivity.
Qed.

Theorem list_image_single {A B : Type} : ∀ a (f : A → B),
    list_image [a] f = [f a].
Proof.
    reflexivity.
Qed.

Theorem list_image_conc {A B : Type} : ∀ (l1 l2 : list A) (f : A → B),
    list_image (l1 ++ l2) f = list_image l1 f ++ list_image l2 f.
Proof.
    intros l1 l2 f.
    induction l1.
    -   rewrite list_image_end.
        do 2 rewrite list_conc_lid.
        reflexivity.
    -   rewrite list_conc_add.
        do 2 rewrite list_image_add.
        rewrite IHl1.
        rewrite list_conc_add.
        reflexivity.
Qed.

Theorem list_image_comp {A B C : Type} : ∀ (l : list A) (f : A → B) (g : B → C),
    list_image (list_image l f) g = list_image l (λ x, g (f x)).
Proof.
    intros l f g.
    induction l.
    -   do 2 rewrite list_image_end.
        reflexivity.
    -   do 3 rewrite list_image_add.
        rewrite IHl.
        reflexivity.
Qed.

Fixpoint func_to_list_base {A : Type} (f : nat → A) n :=
    match n with
    | nat_zero => list_end
    | nat_suc n' => f n' :: func_to_list_base f n'
    end.

Definition func_to_list {A : Type} (f : nat → A) n :=
    list_reverse (func_to_list_base f n).

Theorem func_to_list_eq {A : Type} (f g : nat → A) n :
    (∀ m, m < n → f m = g m) → func_to_list f n = func_to_list g n.
Proof.
    intros all_eq.
    unfold func_to_list.
    rewrite <- list_reverse_eq.
    revert f g all_eq.
    nat_induction n.
    -   intros.
        unfold zero; cbn.
        reflexivity.
    -   intros.
        assert (∀ m, m < n → f m = g m) as all_eq2.
        {
            intros m m_lt.
            apply all_eq.
            exact (trans m_lt (nat_lt_suc n)).
        }
        specialize (IHn f g all_eq2).
        cbn.
        rewrite IHn.
        apply f_equal2.
        2: reflexivity.
        apply all_eq.
        apply nat_lt_suc.
Qed.

Fixpoint func_to_list2_base {A : Type} (f : nat → A) m n :=
    match n with
    | nat_zero => list_end
    | nat_suc n' => f m :: func_to_list2_base f (nat_suc m) n'
    end.

Definition func_to_list2 {A : Type} (f : nat → A) n := func_to_list2_base f 0 n.

Lemma func_to_list2_base_eq {A} : ∀ (f : nat → A) m n,
    func_to_list2_base f (nat_suc m) n =
    func_to_list2_base (λ x, f (nat_suc x)) m n.
Proof.
    intros f m n.
    revert m.
    nat_induction n.
    +   unfold zero; cbn.
        reflexivity.
    +   cbn.
        intros.
        rewrite IHn.
        reflexivity.
Qed.

Theorem func_to_list2_eq {A : Type} : ∀ (f : nat → A) n,
    func_to_list f n = func_to_list2 f n.
Proof.
    intros f n.
    unfold func_to_list, func_to_list2.
    nat_induction n.
    -   unfold zero; cbn.
        reflexivity.
    -   cbn.
        rewrite list_reverse_add.
        unfold func_to_list, func_to_list2 in IHn.
        rewrite IHn.
        clear IHn.
        revert f.
        nat_induction n.
        +   unfold zero, one; cbn.
            reflexivity.
        +   intros.
            cbn.
            rewrite list_conc_add.
            specialize (IHn (λ n, f (nat_suc n))).
            cbn in IHn.
            apply f_equal.
            rewrite <- func_to_list2_base_eq in IHn.
            rewrite <- func_to_list2_base_eq in IHn.
            exact IHn.
Qed.

Theorem func_to_list2_base_conc {A} : ∀ (f : nat → A) a b c,
    func_to_list2_base f a (b + c) =
    func_to_list2_base f a c ++ func_to_list2_base f (a + c) b.
Proof.
    intros f a b c.
    revert a b f.
    nat_induction c.
    -   intros.
        do 2 rewrite plus_rid.
        unfold zero; cbn.
        reflexivity.
    -   intros.
        rewrite nat_plus_rsuc.
        cbn.
        specialize (IHc (nat_suc a) b f).
        rewrite IHc.
        rewrite nat_plus_lrsuc.
        reflexivity.
Qed.
