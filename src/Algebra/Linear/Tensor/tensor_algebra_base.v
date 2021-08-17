Require Import init.

Require Export linear_base.
Require Import linear_multilinear.
Require Import nat.
Require Import card.
Require Import set.

(** This is a very different definition of a tensor algebra than usual.  Really,
I'm trying to beeline to constructing geometric algebra, so I'm only doing what
is absolutely necessary to reach that goal.  This construction is much easier to
deal with than the traditional constructions.
*)

Section TensorAlgebra.

Variables U V : Type.

Context `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @Ldist U UP UM,
    @MultComm U UM,
    @MultAssoc U UM,
    @MultLid U UM UO,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM
}.

Let T1 := multilinear_plus U V 1.
Let T2 := multilinear_plus_comm U V 1.
Let T3 := multilinear_plus_assoc U V 1.
Let T4 := multilinear_zero U V 1.
Let T5 := multilinear_plus_lid U V 1.
Let T6 := multilinear_neg U V 1.
Let T7 := multilinear_plus_linv U V 1.
Let T8 := multilinear_scalar_mult U V 1.
Let T9 := multilinear_scalar_comp U V 1.
Let T10 := multilinear_scalar_id U V 1.
Let T11 := multilinear_scalar_ldist U V 1.
Let T12 := multilinear_scalar_rdist U V 1.
Existing Instances T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Let T13 := multilinear_plus U (multilinear_type U V 1).
Let T14 := multilinear_plus_comm U (multilinear_type U V 1).
Let T15 := multilinear_plus_assoc U (multilinear_type U V 1).
Let T16 := multilinear_zero U (multilinear_type U V 1).
Let T17 := multilinear_plus_lid U (multilinear_type U V 1).
Let T18 := multilinear_neg U (multilinear_type U V 1).
Let T19 := multilinear_plus_linv U (multilinear_type U V 1).
Let T20 := multilinear_scalar_mult U (multilinear_type U V 1).
Let T21 := multilinear_scalar_comp U (multilinear_type U V 1).
Let T22 := multilinear_scalar_id U (multilinear_type U V 1).
Let T23 := multilinear_scalar_ldist U (multilinear_type U V 1).
Let T24 := multilinear_scalar_rdist U (multilinear_type U V 1).
Existing Instances T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24.

Local Open Scope card_scope.

Let multi_type k := multilinear_type U (multilinear_type U V 1) k.

(* TODO: Generalize this inifinite direct product to more general situations *)
Definition tensor_algebra_base := (∀ k, multi_type k).
Definition tensor_finite (A : tensor_algebra_base) :=
    finite (|set_type (λ k, 0 ≠ A k)|).
Definition tensor_algebra := set_type tensor_finite.

Definition multilinear_to_tensor_base {k} (A : multi_type k) :
    tensor_algebra_base := λ n, match (strong_excluded_middle (n = k)) with
    | strong_or_left H => multilinear_type_k_eq _ _ k n A H
    | _ => 0
    end.

Lemma multilinear_to_tensor_finite {k} :
        ∀ A : multi_type k, tensor_finite (multilinear_to_tensor_base A).
    intros A.
    apply (le_lt_trans2 (nat_is_finite 1)).
    unfold nat_to_card, le; equiv_simpl.
    exists (λ _, [0|nat_0_lt_1]).
    intros [a a_neq] [b b_neq] eq; clear eq.
    unfold multilinear_to_tensor_base in *.
    apply set_type_eq; cbn.
    classic_case (a = k) as [ak|ak];
    classic_case (b = k) as [bk|bk].
    1: subst; reflexivity.
    all: contradiction.
Qed.

Definition multilinear_to_tensor {k} (A : multi_type k) :=
    [_|multilinear_to_tensor_finite A].

Theorem multilinear_to_tensor_k_eq : ∀ k n (eq : n = k) (A : multi_type k),
        multilinear_to_tensor A =
        multilinear_to_tensor (multilinear_type_k_eq _ _ k n A eq).
    intros k n eq A.
    unfold multilinear_type_k_eq, Logic.eq_rect_r, Logic.eq_rect.
    destruct (Logic.eq_sym eq).
    reflexivity.
Qed.

Theorem multilinear_to_tensor_eq : ∀ k, ∀ (A B : multi_type k),
        multilinear_to_tensor A = multilinear_to_tensor B → A = B.
    intros k A B eq.
    apply eq_set_type in eq.
    assert (∀ x, [multilinear_to_tensor A|] x = [multilinear_to_tensor B|] x)
        as eq2.
    {
        rewrite eq.
        reflexivity.
    }
    clear eq.
    unfold multilinear_to_tensor, multilinear_to_tensor_base in eq2.
    cbn in eq2.
    specialize (eq2 k).
    destruct (strong_excluded_middle (k = k)) as [eq|neq]; try contradiction.
    unfold multilinear_type_k_eq in eq2.
    (* I don't know what I'm doing, but it works *)
    unfold Logic.eq_rect_r in eq2.
    unfold Logic.eq_rect in eq2.
    destruct (Logic.eq_sym eq).
    exact eq2.
Qed.

Lemma tensor_plus_finite : ∀ A B : tensor_algebra,
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

Instance tensor_plus : Plus tensor_algebra := {
    plus A B := [_|tensor_plus_finite A B]
}.

Program Instance tensor_plus_comm : PlusComm tensor_algebra.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_comm.
Qed.

Program Instance tensor_plus_assoc : PlusAssoc tensor_algebra.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_assoc.
Qed.

Lemma tensor_zero_finite : tensor_finite (λ k, 0).
    unfold tensor_finite.
    assert (|set_type (λ k : nat, (zero (U := multi_type k)) ≠ 0)| = 0)
        as eq.
    {
        apply card_false_0.
        intros [a neq].
        contradiction.
    }
    rewrite eq.
    apply nat_is_finite.
Qed.

Instance tensor_zero : Zero tensor_algebra := {
    zero := [_|tensor_zero_finite]
}.

Program Instance tensor_plus_lid : PlusLid tensor_algebra.
Next Obligation.
    unfold plus, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_lid.
Qed.

Lemma tensor_neg_finite : ∀ A : tensor_algebra, tensor_finite (λ k, -[A|] k).
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

Instance tensor_neg : Neg tensor_algebra := {
    neg A := [_|tensor_neg_finite A]
}.

Program Instance tensor_plus_linv : PlusLinv tensor_algebra.
Next Obligation.
    unfold plus, neg, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_linv.
Qed.

Lemma tensor_scalar_finite : ∀ α (A : tensor_algebra),
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

Theorem multilinear_to_tensor_plus : ∀ k (A B : multi_type k),
        multilinear_to_tensor A + multilinear_to_tensor B =
        multilinear_to_tensor (A + B).
    intros k A B.
    apply set_type_eq; cbn.
    apply functional_ext; intros x.
    unfold plus at 1; cbn.
    unfold multilinear_to_tensor_base.
    destruct (strong_excluded_middle (x = k)) as [eq|neq].
    2: apply plus_rid.
    unfold multilinear_type_k_eq, Logic.eq_rect_r, Logic.eq_rect.
    destruct (Logic.eq_sym _).
    reflexivity.
Qed.

Instance tensor_scalar_mult : ScalarMult U tensor_algebra := {
    scalar_mult α A := [_|tensor_scalar_finite α A]
}.

Program Instance tensor_scalar_comp : ScalarComp U tensor_algebra.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_comp.
Qed.

Program Instance tensor_scalar_id : ScalarId U tensor_algebra.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_id.
Qed.

Program Instance tensor_scalar_ldist : ScalarLdist U tensor_algebra.
Next Obligation.
    unfold plus, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_ldist.
Qed.

Program Instance tensor_scalar_rdist : ScalarRdist U tensor_algebra.
Next Obligation.
    unfold plus at 2, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_rdist.
Qed.

End TensorAlgebra.
