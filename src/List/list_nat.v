Require Import init.

Require Export list_base.
Require Export list_in.

Require Export nat.

Fixpoint list_size {U : Type} (l : list U) :=
    match l with
    | [] => 0
    | a ꞉ l' => nat_suc (list_size l')
    end.
Arguments list_size : simpl never.

Fixpoint list_count {U} (l : list U) (a : U) : nat :=
    match l with
    | [] => 0
    | x ꞉ l' => (If x = a then 1 else 0) + list_count l' a
end.
Arguments list_count : simpl never.

Fixpoint list_constant {U} (a : U) (n : nat) :=
    match n with
    | nat_zero => []
    | nat_suc n' => a ꞉ list_constant a n'
    end.
Arguments list_constant : simpl never.

Theorem list_size_end U : list_size (U := U) [] = 0.
Proof.
    reflexivity.
Qed.

Theorem list_size_add {U} : ∀ (x : U) a,
    list_size (x ꞉ a) = nat_suc (list_size a).
Proof.
    reflexivity.
Qed.

Theorem list_size_single {U} : ∀ x : U, list_size [x] = 1.
Proof.
    intros x.
    rewrite list_size_add.
    rewrite list_size_end.
    reflexivity.
Qed.

Theorem list_size_conc {U} : ∀ l1 l2 : list U,
    list_size (l1 + l2) = list_size l1 + list_size l2.
Proof.
    intros l1 l2.
    induction l1.
    -   rewrite list_size_end.
        rewrite list_conc_lid.
        rewrite plus_lid.
        reflexivity.
    -   rewrite list_conc_add.
        do 2 rewrite list_size_add.
        rewrite IHl1.
        rewrite nat_plus_lsuc.
        reflexivity.
Qed.

Theorem list_size_comm {U} : ∀ l1 l2 : list U,
    list_size (l1 + l2) = list_size (l2 + l1).
Proof.
    intros l1 l2.
    do 2 rewrite list_size_conc.
    apply plus_comm.
Qed.

Theorem list_image_size {A B} : ∀ l (f : A → B),
    list_size (list_image f l) = list_size l.
Proof.
    intros l f.
    induction l.
    -   rewrite list_image_end.
        reflexivity.
    -   rewrite list_image_add.
        do 2 rewrite list_size_add.
        rewrite IHl.
        reflexivity.
Qed.

Theorem list_count_end {U} : ∀ (x : U), list_count [] x = 0.
Proof.
    reflexivity.
Qed.

Theorem list_count_add {U} : ∀ (x y : U) a,
    list_count (x ꞉ a) y = (If x = y then 1 else 0) + list_count a y.
Proof.
    reflexivity.
Qed.

Theorem list_count_add_eq {U} : ∀ (x : U) a,
    list_count (x ꞉ a) x = nat_suc (list_count a x).
Proof.
    intros x a.
    rewrite list_count_add.
    rewrite (if_true (Logic.eq_refl _)).
    reflexivity.
Qed.

Theorem list_count_add_neq {U} : ∀ {x y : U} {a}, x ≠ y →
    list_count (x ꞉ a) y = list_count a y.
Proof.
    intros x y a neq.
    rewrite list_count_add.
    rewrite (if_false neq).
    rewrite plus_lid.
    reflexivity.
Qed.

Theorem list_count_single {U} : ∀ (x y : U),
    list_count [x] y = If x = y then 1 else 0.
Proof.
    intros x y.
    rewrite list_count_add, list_count_end.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem list_count_single_eq {U} : ∀ x : U, list_count [x] x = 1.
Proof.
    intros x.
    rewrite list_count_add_eq, list_count_end.
    reflexivity.
Qed.

Theorem list_count_single_neq {U} : ∀ x y : U, x ≠ y → list_count [x] y = 0.
Proof.
    intros x y neq.
    rewrite (list_count_add_neq neq).
    apply list_count_end.
Qed.

Theorem list_count_conc {U} : ∀ l1 l2 (a : U),
    list_count (l1 + l2) a = list_count l1 a + list_count l2 a.
Proof.
    intros l1 l2 a.
    induction l1 as [|b l1].
    -   rewrite list_count_end.
        rewrite plus_lid, list_conc_lid.
        reflexivity.
    -   rewrite list_conc_add.
        do 2 rewrite list_count_add.
        rewrite IHl1.
        apply plus_assoc.
Qed.

Theorem list_count_comm {U} : ∀ a b (x : U),
    list_count (a + b) x = list_count (b + a) x.
Proof.
    intros a b x.
    do 2 rewrite list_count_conc.
    apply plus_comm.
Qed.

Theorem list_count_reverse {U} : ∀ l (a : U),
    list_count l a = list_count (list_reverse l) a.
Proof.
    intros l a.
    induction l as [|b l].
    -   rewrite list_reverse_end.
        reflexivity.
    -   rewrite list_reverse_add.
        rewrite list_count_conc.
        rewrite list_count_add, list_count_single.
        rewrite IHl.
        apply plus_comm.
Qed.

Theorem list_count_in {U} : ∀ l (a : U), in_list l a ↔ 0 ≠ list_count l a.
Proof.
    intros l a.
    split.
    -   intros a_in contr.
        apply in_list_split in a_in as [l1 [l2 l_eq]]; subst l.
        rewrite list_count_conc in contr.
        rewrite list_count_add_eq in contr.
        rewrite nat_plus_rsuc in contr.
        contradiction (nat_zero_suc contr).
    -   intros neq.
        induction l as [|x l].
        +   rewrite list_count_end in neq.
            contradiction.
        +   rewrite in_list_add_eq.
            apply or_right.
            intros neq'.
            rewrite (list_count_add_neq neq') in neq.
            exact (IHl neq).
Qed.

Theorem list_count_nin {U} : ∀ l (a : U), ¬in_list l a ↔ 0 = list_count l a.
Proof.
    intros l a.
    rewrite list_count_in.
    apply not_not.
Qed.

Theorem list_count_unique {U} : ∀ l (a : U), list_unique l → list_count l a ≤ 1.
Proof.
    intros l x l_uni.
    list_unique_induction l l_uni as a a_nin IHl.
    -   rewrite list_count_end.
        apply nat_pos.
    -   apply list_count_nin in a_nin.
        rewrite list_count_add.
        case_if [eq|neq].
        +   subst x.
            rewrite <- a_nin.
            rewrite plus_rid.
            apply refl.
        +   rewrite plus_lid.
            exact IHl.
Qed.

Theorem list_count_in_unique {U} : ∀ l (a : U), list_unique l → in_list l a →
    list_count l a = 1.
Proof.
    intros l a l_uni a_in.
    apply antisym.
    -   apply list_count_unique.
        exact l_uni.
    -   apply list_count_in in a_in.
        apply (nat_neq0_leq1 a_in).
Qed.

Theorem list_constant_zero {U} : ∀ a : U, list_constant a 0 = [].
Proof.
    reflexivity.
Qed.

Theorem list_constant_suc {U} : ∀ (a : U) n,
    list_constant a (nat_suc n) = a ꞉ list_constant a n.
Proof.
    reflexivity.
Qed.

Theorem list_constant_one {U} : ∀ a : U, list_constant a 1 = [a].
Proof.
    reflexivity.
Qed.

Theorem in_list_constant {U} : ∀ (a b : U) n,
    in_list (list_constant a n) b → a = b.
Proof.
    intros a b n b_in.
    nat_induction n.
    -   rewrite list_constant_zero in b_in.
        apply in_list_end in b_in.
        contradiction.
    -   rewrite list_constant_suc in b_in.
        apply in_list_add_eq in b_in.
        destruct b_in as [eq|b_in].
        +   exact eq.
        +   exact (IHn b_in).
Qed.

Theorem list_count_constant {U} : ∀ (a : U) n,
    list_count (list_constant a n) a = n.
Proof.
    intros a n.
    nat_induction n.
    -   rewrite list_constant_zero.
        apply list_count_end.
    -   rewrite list_constant_suc.
        rewrite list_count_add_eq.
        rewrite IHn.
        reflexivity.
Qed.
