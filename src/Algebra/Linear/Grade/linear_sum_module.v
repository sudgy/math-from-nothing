Require Import init.

Require Import Coq.Init.Tactics.

Require Export linear_base.
Require Import module_category.
Require Import linear_subspace.

Require Import set.
Require Import nat.
Require Import unordered_list.

Section LinearGradeSum.

Context {U : CRingObj}.
Variable (I : Type).
Variable (V : I → ModuleObj U).

Definition sum_module_base := (∀ k, V k).
Definition sum_module_finite (A : sum_module_base) :=
    simple_finite (set_type (λ k, 0 ≠ A k)).
Definition sum_module_type := set_type sum_module_finite.

Definition single_to_sum_module_base {k} (A : V k) : sum_module_base.
    intros n.
    classic_case (k = n).
    -   subst k.
        exact A.
    -   exact 0.
Defined.

Theorem single_to_sum_module_base_eq : ∀ i u, single_to_sum_module_base u i = u.
Proof.
    intros i u.
    unfold single_to_sum_module_base.
    destruct (sem _) as [eq|neq].
    -   rewrite (proof_irrelevance _ Logic.eq_refl).
        cbn.
        reflexivity.
    -   contradiction.
Qed.

Lemma single_to_sum_module_finite {k} : ∀ A : V k,
    sum_module_finite (single_to_sum_module_base A).
Proof.
    intros A.
    exists 1.
    exists (λ _, [0|nat_one_pos]).
    split.
    intros [a a_neq] [b b_neq] eq; clear eq.
    unfold single_to_sum_module_base in *.
    apply set_type_eq; cbn.
    classic_case (k = a) as [ak|ak];
    classic_case (k = b) as [bk|bk].
    1: subst; reflexivity.
    all: contradiction.
Qed.

Definition single_to_sum_module {k} (A : V k)
    := [_|single_to_sum_module_finite A].

Theorem single_to_sum_module_eq : ∀ k, ∀ (A B : V k),
    single_to_sum_module A = single_to_sum_module B → A = B.
Proof.
    intros k A B eq.
    apply set_type_eq in eq.
    assert (∀ x, [single_to_sum_module A|] x = [single_to_sum_module B|] x) as eq2.
    {
        rewrite eq.
        reflexivity.
    }
    clear eq.
    unfold single_to_sum_module, single_to_sum_module_base in eq2.
    cbn in eq2.
    specialize (eq2 k).
    destruct (sem (k = k)) as [eq|neq]; try contradiction.
    destruct eq; cbn in eq2.
    exact eq2.
Qed.

Lemma sum_module_plus_finite : ∀ A B : sum_module_type,
    sum_module_finite (λ k, [A|] k + [B|] k).
Proof.
    intros [A A_fin] [B B_fin]; cbn.
    apply (simple_finite_trans _ _ (simple_finite_sum _ _ A_fin B_fin)).
    assert (∀ (n : set_type (λ k, 0 ≠ A k + B k)), {0 ≠ A [n|]} + {0 ≠ B [n|]})
        as n_in.
    {
        intros [n n_neq]; cbn.
        classic_case (0 = A n) as [Anz|Anz].
        -   right.
            rewrite <- Anz in n_neq.
            rewrite plus_lid in n_neq.
            exact n_neq.
        -   left; exact Anz.
    }
    exists (λ n, match (n_in n) with
        | strong_or_left  H => inl [[n|]|H]
        | strong_or_right H => inr [[n|]|H]
    end).
    split.
    intros a b eq.
    destruct (n_in a) as [neq1|neq1]; destruct (n_in b) as [neq2|neq2].
    all: inversion eq as [eq2].
    all: apply set_type_eq; exact eq2.
Qed.

Instance sum_module_plus : Plus sum_module_type := {
    plus A B := [_|sum_module_plus_finite A B]
}.

Program Instance sum_module_plus_comm : PlusComm sum_module_type.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_comm.
Qed.

Program Instance sum_module_plus_assoc : PlusAssoc sum_module_type.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_assoc.
Qed.

Lemma sum_module_zero_finite : sum_module_finite (λ k, 0).
Proof.
    unfold sum_module_finite.
    exists 0.
    exists (λ x : set_type (λ k : I, (zero (U := module_V (V k))) ≠ 0),
        False_rect _ ([|x] Logic.eq_refl)).
    split.
    intros [a neq].
    contradiction.
Qed.

Instance sum_module_zero : Zero sum_module_type := {
    zero := [_|sum_module_zero_finite]
}.

Program Instance sum_module_plus_lid : PlusLid sum_module_type.
Next Obligation.
    unfold plus, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_lid.
Qed.

Lemma sum_module_neg_finite : ∀ A : sum_module_type, sum_module_finite (λ k, -[A|] k).
Proof.
    intros [A A_fin]; cbn.
    apply (simple_finite_trans _ _ A_fin).
    assert (∀ (n : set_type (λ k, 0 ≠ - A k)), 0 ≠ A [n|]) as n_in.
    {
        intros [n n_neq]; cbn.
        intros eq.
        rewrite <- eq in n_neq.
        rewrite neg_zero in n_neq.
        contradiction.
    }
    exists (λ n, [[n|]|n_in n]).
    split.
    intros a b eq.
    apply set_type_eq in eq; cbn in eq.
    apply set_type_eq in eq; cbn in eq.
    exact eq.
Qed.

Instance sum_module_neg : Neg sum_module_type := {
    neg A := [_|sum_module_neg_finite A]
}.

Program Instance sum_module_plus_linv : PlusLinv sum_module_type.
Next Obligation.
    unfold plus, neg, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_linv.
Qed.

Theorem single_to_sum_module_plus : ∀ k (A B : module_V (V k)),
    single_to_sum_module (A + B) =
    single_to_sum_module A + single_to_sum_module B.
Proof.
    intros k A B.
    apply set_type_eq; cbn.
    apply functional_ext; intros x.
    unfold plus at 2; cbn.
    unfold single_to_sum_module_base.
    destruct (sem (k = x)) as [eq|neq].
    2: symmetry; apply plus_rid.
    destruct eq; cbn.
    reflexivity.
Qed.

Lemma sum_module_scalar_finite : ∀ α (A : sum_module_type),
    sum_module_finite (λ k, α · [A|] k).
Proof.
    intros α [A A_fin]; cbn.
    apply (simple_finite_trans _ _ A_fin).
    assert (∀ (n : set_type (λ k, 0 ≠ α · A k)), 0 ≠ A [n|]) as n_in.
    {
        intros [n n_neq]; cbn.
        intros eq.
        rewrite <- eq in n_neq.
        rewrite scalar_ranni in n_neq.
        contradiction.
    }
    exists (λ n, [[n|]|n_in n]).
    split.
    intros a b eq.
    apply set_type_eq in eq; cbn in eq.
    apply set_type_eq in eq; cbn in eq.
    exact eq.
Qed.

Instance sum_module_scalar_mult : ScalarMult U sum_module_type := {
    scalar_mult α A := [_|sum_module_scalar_finite α A]
}.

Program Instance sum_module_scalar_comp : ScalarComp U sum_module_type.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_comp.
Qed.

Program Instance sum_module_scalar_id : ScalarId U sum_module_type.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_id.
Qed.

Program Instance sum_module_scalar_ldist : ScalarLdist U sum_module_type.
Next Obligation.
    unfold plus, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_ldist.
Qed.

Program Instance sum_module_scalar_rdist : ScalarRdist U sum_module_type.
Next Obligation.
    unfold plus at 2, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_rdist.
Qed.

Theorem single_to_sum_module_scalar : ∀ k α (A : module_V (V k)),
    single_to_sum_module (α · A) = α · single_to_sum_module A.
Proof.
    intros k A B.
    apply set_type_eq; cbn.
    apply functional_ext; intros x.
    unfold scalar_mult at 2; cbn.
    unfold single_to_sum_module_base.
    destruct (sem (k = x)) as [eq|neq].
    -   destruct eq; cbn.
        reflexivity.
    -   rewrite scalar_ranni.
        reflexivity.
Qed.

Lemma single_to_sum_module_zero : ∀ k, (single_to_sum_module (k := k) 0) = 0.
Proof.
    intros k.
    apply set_type_eq; cbn.
    unfold single_to_sum_module_base.
    apply functional_ext.
    intros x.
    destruct (sem (k = x)) as [eq|neq].
    -   destruct eq; cbn.
        reflexivity.
    -   reflexivity.
Qed.

Lemma sum_module_list_sum_k : ∀ (al : ulist (sum_module_type)) k,
    [ulist_sum al|] k = ulist_sum (ulist_image (λ a, [a|] k) al).
Proof.
    intros al k.
    induction al using ulist_induction.
    -   rewrite ulist_image_end.
        do 2 rewrite ulist_sum_end.
        reflexivity.
    -   rewrite ulist_image_add.
        do 2 rewrite ulist_sum_add.
        unfold plus at 1; cbn.
        rewrite IHal.
        reflexivity.
Qed.

Definition sum_project_base (A : sum_module_type) (i : I) (k : I)
    := If i = k then [A|] k else 0.

Lemma sum_project_finite : ∀ A i, sum_module_finite (sum_project_base A i).
Proof.
    intros A i.
    exists 1.
    exists (λ _, [0|nat_one_pos]).
    split.
    intros [a a_neq] [b b_neq] eq; clear eq.
    rewrite set_type_eq2.
    unfold sum_project_base in a_neq, b_neq.
    case_if [eq1|neq1]; case_if [eq2|neq2].
    2, 3, 4: contradiction.
    subst.
    reflexivity.
Qed.

Definition sum_project A i := [_|sum_project_finite A i].

Theorem sum_project_project : ∀ A i,
    sum_project (sum_project A i) i = sum_project A i.
Proof.
    intros A i.
    apply set_type_eq.
    apply functional_ext.
    intros x.
    unfold sum_project; cbn.
    unfold sum_project_base; cbn.
    case_if [eq|neq]; reflexivity.
Qed.

Theorem sum_project_zero : ∀ i, sum_project 0 i = 0.
Proof.
    intros i.
    apply set_type_eq.
    apply functional_ext.
    intros x.
    unfold sum_project; cbn.
    unfold sum_project_base; cbn.
    case_if [eq|neq]; reflexivity.
Qed.

Theorem sum_project_neq : ∀ i j v, i ≠ j → sum_project (sum_project v i) j = 0.
Proof.
    intros i j v neq.
    apply set_type_eq.
    apply functional_ext.
    intros x.
    unfold sum_project; cbn.
    unfold sum_project_base; cbn.
    case_if [eq1|neq1]; [>case_if [eq2|neq2]|].
    -   subst.
        contradiction.
    -   reflexivity.
    -   reflexivity.
Qed.

Theorem sum_project_plus : ∀ u v i,
    sum_project (u + v) i = sum_project u i + sum_project v i.
Proof.
    intros u v i.
    apply set_type_eq.
    apply functional_ext.
    intros x.
    unfold sum_project; cbn.
    unfold sum_project_base; cbn.
    unfold plus at 2; cbn.
    case_if [eq|neq].
    -   reflexivity.
    -   rewrite plus_lid.
        reflexivity.
Qed.

Theorem sum_project_scalar : ∀ a v i,
    sum_project (a · v) i = a · sum_project v i.
Proof.
    intros a v i.
    apply set_type_eq.
    apply functional_ext.
    intros x.
    unfold sum_project; cbn.
    unfold sum_project_base; cbn.
    unfold scalar_mult at 2; cbn.
    case_if [eq|neq].
    -   reflexivity.
    -   rewrite scalar_ranni.
        reflexivity.
Qed.

Theorem all_sum_project_eq : ∀ u v,
    (∀ i, sum_project u i = sum_project v i) → u = v.
Proof.
    intros u v eq.
    apply set_type_eq.
    apply functional_ext.
    intros x.
    specialize (eq x).
    unfold sum_project in eq.
    rewrite set_type_eq2 in eq.
    unfold sum_project_base in eq.
    pose proof (func_eq _ _ eq x) as eq2.
    cbn in eq2.
    do 2 rewrite if_true in eq2 by reflexivity.
    exact eq2.
Qed.

End LinearGradeSum.

Definition sum_module {U} I (V : I → ModuleObj U) := make_module U
    (sum_module_type I V)
    (sum_module_plus I V)
    (sum_module_zero I V)
    (sum_module_neg I V)
    (sum_module_plus_assoc I V)
    (sum_module_plus_comm I V)
    (sum_module_plus_lid I V)
    (sum_module_plus_linv I V)
    (sum_module_scalar_mult I V)
    (sum_module_scalar_id I V)
    (sum_module_scalar_ldist I V)
    (sum_module_scalar_rdist I V)
    (sum_module_scalar_comp I V)
: Module U.
