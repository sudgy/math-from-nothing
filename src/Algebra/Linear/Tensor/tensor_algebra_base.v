Require Import init.

Require Import tensor_power_base.
Require Import module_category.

Require Import nat.
Require Import unordered_list.
Require Import plus_sum.
Require Import set.
Require Import card.

(** This file contains the definition of the algebra and the proofs that it
forms a vector space over the original field.
*)

(* begin hide *)
Section TensorAlgebra.

(* end hide *)
Context {F : CRing} (V : Module F).

(* begin hide *)
Let U := cring_U F.
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Let TP k := module_plus (tensor_power V k).
Let TZ k := module_zero (tensor_power V k).
Let TN k := module_neg (tensor_power V k).
Let TPC k := module_plus_comm (tensor_power V k).
Let TPA k := module_plus_assoc (tensor_power V k).
Let TPZ k := module_plus_lid (tensor_power V k).
Let TPN k := module_plus_linv (tensor_power V k).
Let TSM k := module_scalar (tensor_power V k).
Let TSMC k := module_scalar_comp (tensor_power V k).
Let TSMO k := module_scalar_id (tensor_power V k).
Let TSML k := module_scalar_ldist (tensor_power V k).
Let TSMR k := module_scalar_rdist (tensor_power V k).
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD TP TZ TN TPC
    TPA TPZ TPN TSM TSMC TSMO TSML TSMR.

Local Open Scope card_scope.

(* end hide *)
Let k_tensor k := module_V (tensor_power V k).

Definition tensor_algebra_base_base := (∀ k, module_V (tensor_power V k)).
Definition tensor_finite (A : tensor_algebra_base_base) :=
    finite (|set_type (λ k, 0 ≠ A k)|).
Definition tensor_algebra_base := set_type tensor_finite.

Definition power_to_tensor_base {k} (A : k_tensor k) :
    tensor_algebra_base_base := λ n, match (strong_excluded_middle (k = n)) with
    | strong_or_left H => module_homo_f (tensor_power_nat_eq V H) A
    | _ => 0
    end.

Lemma power_to_tensor_finite {k} :
        ∀ A : k_tensor k, tensor_finite (power_to_tensor_base A).
    intros A.
    apply (le_lt_trans2 (nat_is_finite 1)).
    unfold nat_to_card, le; equiv_simpl.
    exists (λ _, [0|nat_0_lt_1]).
    intros [a a_neq] [b b_neq] eq; clear eq.
    unfold power_to_tensor_base in *.
    apply set_type_eq; cbn.
    classic_case (k = a) as [ak|ak];
    classic_case (k = b) as [bk|bk].
    1: subst; reflexivity.
    all: contradiction.
Qed.

Definition power_to_tensor {k} (A : k_tensor k) := [_|power_to_tensor_finite A].

Theorem power_to_tensor_k_eq : ∀ k n (eq : k = n) (A : k_tensor k),
        power_to_tensor A =
        power_to_tensor (module_homo_f (tensor_power_nat_eq V eq) A).
    intros k n eq A.
    destruct eq.
    cbn.
    reflexivity.
Qed.

Theorem power_to_tensor_eq : ∀ k, ∀ (A B : k_tensor k),
        power_to_tensor A = power_to_tensor B → A = B.
    intros k A B eq.
    apply eq_set_type in eq.
    assert (∀ x, [power_to_tensor A|] x = [power_to_tensor B|] x) as eq2.
    {
        rewrite eq.
        reflexivity.
    }
    clear eq.
    unfold power_to_tensor, power_to_tensor_base in eq2.
    cbn in eq2.
    specialize (eq2 k).
    destruct (strong_excluded_middle (k = k)) as [eq|neq]; try contradiction.
    destruct eq; cbn in eq2.
    exact eq2.
Qed.

Lemma tensor_plus_finite : ∀ A B : tensor_algebra_base,
        tensor_finite (λ k, [A|] k + [B|] k).
    intros [A A_fin] [B B_fin]; cbn.
    apply fin_nat_ex in A_fin as [m m_eq].
    apply fin_nat_ex in B_fin as [n n_eq].
    assert (finite (nat_to_card m + nat_to_card n)) as mn_fin.
    {
        rewrite nat_to_card_plus.
        apply nat_is_finite.
    }
    apply (le_lt_trans2 mn_fin).
    rewrite m_eq, n_eq.
    clear m m_eq n n_eq mn_fin.
    unfold plus at 2, le; equiv_simpl.
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
    intros a b eq.
    destruct (n_in a) as [neq1|neq1]; destruct (n_in b) as [neq2|neq2].
    all: inversion eq as [eq2].
    all: apply set_type_eq; exact eq2.
Qed.

Instance tensor_algebra_plus : Plus tensor_algebra_base := {
    plus A B := [_|tensor_plus_finite A B]
}.

Program Instance tensor_algebra_plus_comm : PlusComm tensor_algebra_base.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_comm.
Qed.

Program Instance tensor_algebra_plus_assoc : PlusAssoc tensor_algebra_base.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_assoc.
Qed.

Lemma tensor_zero_finite : tensor_finite (λ k, 0).
    unfold tensor_finite.
    assert (|set_type (λ k : nat, (zero (U := module_V (tensor_power V k))) ≠ 0)| = 0)
        as eq.
    {
        apply card_false_0.
        intros [a neq].
        contradiction.
    }
    rewrite eq.
    apply nat_is_finite.
Qed.

Instance tensor_algebra_zero : Zero tensor_algebra_base := {
    zero := [_|tensor_zero_finite]
}.

Program Instance tensor_algebra_plus_lid : PlusLid tensor_algebra_base.
Next Obligation.
    unfold plus, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_lid.
Qed.

Lemma tensor_neg_finite : ∀ A : tensor_algebra_base, tensor_finite (λ k, -[A|] k).
    intros [A A_fin]; cbn.
    apply fin_nat_ex in A_fin as [n n_eq].
    apply (le_lt_trans2 (nat_is_finite n)).
    rewrite n_eq; clear n n_eq.
    unfold le; equiv_simpl.
    assert (∀ (n : set_type (λ k, 0 ≠ - A k)), 0 ≠ A [n|]) as n_in.
    {
        intros [n n_neq]; cbn.
        intros eq.
        rewrite <- eq in n_neq.
        rewrite neg_zero in n_neq.
        contradiction.
    }
    exists (λ n, [[n|]|n_in n]).
    intros a b eq.
    apply eq_set_type in eq; cbn in eq.
    apply set_type_eq in eq; cbn in eq.
    exact eq.
Qed.

Instance tensor_algebra_neg : Neg tensor_algebra_base := {
    neg A := [_|tensor_neg_finite A]
}.

Program Instance tensor_algebra_plus_linv : PlusLinv tensor_algebra_base.
Next Obligation.
    unfold plus, neg, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_linv.
Qed.

Theorem power_to_tensor_plus : ∀ k (A B : k_tensor k),
        power_to_tensor (A + B) =
        power_to_tensor A + power_to_tensor B.
    intros k A B.
    apply set_type_eq; cbn.
    apply functional_ext; intros x.
    unfold plus at 2; cbn.
    unfold power_to_tensor_base.
    destruct (strong_excluded_middle (k = x)) as [eq|neq].
    2: symmetry; apply plus_rid.
    destruct eq; cbn.
    reflexivity.
Qed.

Lemma tensor_scalar_finite : ∀ α (A : tensor_algebra_base),
        tensor_finite (λ k, α · [A|] k).
    intros α [A A_fin]; cbn.
    apply fin_nat_ex in A_fin as [n n_eq].
    apply (le_lt_trans2 (nat_is_finite n)).
    rewrite n_eq; clear n n_eq.
    unfold le; equiv_simpl.
    assert (∀ (n : set_type (λ k, 0 ≠ α · A k)), 0 ≠ A [n|]) as n_in.
    {
        intros [n n_neq]; cbn.
        intros eq.
        rewrite <- eq in n_neq.
        rewrite scalar_ranni in n_neq.
        contradiction.
    }
    exists (λ n, [[n|]|n_in n]).
    intros a b eq.
    apply eq_set_type in eq; cbn in eq.
    apply set_type_eq in eq; cbn in eq.
    exact eq.
Qed.

Instance tensor_algebra_scalar_mult : ScalarMult U tensor_algebra_base := {
    scalar_mult α A := [_|tensor_scalar_finite α A]
}.

Program Instance tensor_algebra_scalar_comp : ScalarComp U tensor_algebra_base.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_comp.
Qed.

Program Instance tensor_algebra_scalar_id : ScalarId U tensor_algebra_base.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_id.
Qed.

Program Instance tensor_algebra_scalar_ldist : ScalarLdist U tensor_algebra_base.
Next Obligation.
    unfold plus, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_ldist.
Qed.

Program Instance tensor_algebra_scalar_rdist : ScalarRdist U tensor_algebra_base.
Next Obligation.
    unfold plus at 2, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_rdist.
Qed.

Theorem power_to_tensor_scalar : ∀ k α (A : k_tensor k),
        power_to_tensor (α · A) = α · power_to_tensor A.
    intros k A B.
    apply set_type_eq; cbn.
    apply functional_ext; intros x.
    unfold scalar_mult at 2; cbn.
    unfold power_to_tensor_base.
    destruct (strong_excluded_middle (k = x)) as [eq|neq].
    -   destruct eq; cbn.
        reflexivity.
    -   rewrite scalar_ranni.
        reflexivity.
Qed.

Lemma power_to_tensor_zero : ∀ k, (power_to_tensor (k := k) 0) = 0.
    intros k.
    apply set_type_eq; cbn.
    unfold power_to_tensor_base.
    apply functional_ext.
    intros x.
    destruct (strong_excluded_middle (k = x)) as [eq|neq].
    -   destruct eq; cbn.
        reflexivity.
    -   reflexivity.
Qed.

Lemma tensor_list_sum_k : ∀ (al : ulist (tensor_algebra_base)) k,
        [ulist_sum al|] k = ulist_sum (ulist_image al (λ a, [a|] k)).
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
(* begin hide *)

End TensorAlgebra.
(* end hide *)
