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
    list_permutation l1 l2 → list_permutation (a :: l1) (a :: l2).
Proof.
    intros a l1 l2 l_perm.
    apply list_perm_skip.
    exact l_perm.
Qed.
Definition ulist_add {U} (a : U)
    := unary_op (unary_self_wd (E := ulist_equiv U) (uadd_wd U a)).
Infix ":::" := ulist_add (at level 60, right associativity) : list_scope.

Theorem ulist_induction {U} : ∀ S : ulist U → Prop,
    S ulist_end → (∀ a l, S l → S (a ::: l)) → ∀ l, S l.
Proof.
    intros S S_end S_add l.
    equiv_get_value l.
    induction l.
    -   exact S_end.
    -   assert (to_equiv (ulist_equiv U) (a :: l) =
            a ::: (to_equiv (ulist_equiv U) l)) as eq.
        {
            unfold ulist_add; equiv_simpl.
            apply list_perm_refl.
        }
        rewrite eq.
        apply S_add.
        exact IHl.
Qed.

Theorem ulist_destruct {U} : ∀ S : ulist U → Prop,
    S ulist_end → (∀ a l, S (a ::: l)) → ∀ l, S l.
Proof.
    intros S S_end S_ind l.
    induction l using ulist_induction.
    -   exact S_end.
    -   apply S_ind.
Qed.

Theorem ulist_end_neq {U} : ∀ (a : U) l, a ::: l ≠ ulist_end.
Proof.
    intros a l contr.
    equiv_get_value l.
    unfold ulist_add, ulist_end in contr; equiv_simpl in contr.
    apply list_perm_sym in contr.
    apply list_perm_nil_eq in contr.
    inversion contr.
Qed.

Theorem ulist_single_eq {U} : ∀ (a b : U), a ::: ulist_end = b ::: ulist_end →
    a = b.
Proof.
    intros a b eq.
    unfold ulist_add, ulist_end in eq; equiv_simpl in eq.
    pose proof (list_perm_single eq) as eq2.
    inversion eq2.
    reflexivity.
Qed.

Lemma uconc_wd U : ∀ al1 al2 bl1 bl2 : list U,
    list_permutation al1 al2 → list_permutation bl1 bl2 →
    list_permutation (al1 ++ bl1) (al2 ++ bl2).
Proof.
    intros al1 al2 bl1 bl2 eq1 eq2.
    pose proof (list_perm_rpart al1 eq2).
    pose proof (list_perm_lpart bl2 eq1).
    exact (list_perm_trans H H0).
Qed.
Definition ulist_conc {U}
    := binary_op (binary_self_wd (E := ulist_equiv U) (uconc_wd U)).
Infix "+++" := ulist_conc (right associativity, at level 60) : list_scope.

Theorem ulist_add_conc_add {U} : ∀ (a : U) l1 l2,
    a ::: (l1 +++ l2) = (a ::: l1) +++ l2.
Proof.
    intros a l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_conc, ulist_add; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_add_conc {U} : ∀ (a : U) l, a ::: l = (a ::: ulist_end) +++ l.
Proof.
    intros a l.
    equiv_get_value l.
    unfold ulist_end, ulist_add, ulist_conc; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_conc_lid {U} : ∀ l : ulist U, ulist_end +++ l = l.
Proof.
    intros l.
    equiv_get_value l.
    unfold ulist_end, ulist_conc; equiv_simpl.
    apply list_perm_refl.
Qed.

Theorem ulist_conc_rid {U} : ∀ l : ulist U, l +++ ulist_end = l.
Proof.
    intros l.
    equiv_get_value l.
    unfold ulist_end, ulist_conc; equiv_simpl.
    rewrite list_conc_rid.
    apply list_perm_refl.
Qed.

Theorem ulist_conc_comm {U} : ∀ a b : ulist U, a +++ b = b +++ a.
Proof.
    intros a b.
    equiv_get_value a b.
    unfold ulist_conc; equiv_simpl.
    apply list_perm_conc.
Qed.

Theorem ulist_conc_assoc {U} : ∀ a b c : ulist U,
    a +++ (b +++ c) = (a +++ b) +++ c.
Proof.
    intros a b c.
    equiv_get_value a b c.
    unfold ulist_conc; equiv_simpl.
    rewrite list_conc_assoc.
    apply list_perm_refl.
Qed.

Theorem ulist_swap {U} : ∀ (a b : U) l, a ::: b ::: l = b ::: a ::: l.
Proof.
    intros a b l.
    equiv_get_value l.
    unfold ulist_add; equiv_simpl.
    apply list_perm_swap.
Qed.

Theorem ulist_skip {U} : ∀ (a : U) l1 l2, a ::: l1 = a ::: l2 → l1 = l2.
Proof.
    intros a l1 l2.
    equiv_get_value l1 l2.
    unfold ulist_add; equiv_simpl.
    apply list_perm_add_eq.
Qed.

Theorem ulist_conc_lcancel {U} : ∀ l1 l2 l3 : ulist U,
    l1 +++ l2 = l1 +++ l3 → l2 = l3.
Proof.
    intros l1 l2 l3.
    equiv_get_value l1 l2 l3.
    unfold ulist_conc; equiv_simpl.
    apply list_perm_conc_lcancel.
Qed.

Theorem ulist_conc_rcancel {U} : ∀ l1 l2 l3 : ulist U,
    l2 +++ l1 = l3 +++ l1 → l2 = l3.
Proof.
    intros l1 l2 l3.
    do 2 rewrite (ulist_conc_comm _ l1).
    apply ulist_conc_lcancel.
Qed.
