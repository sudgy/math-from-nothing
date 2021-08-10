Require Import init.

Require Export linear_base.
Require Import linear_subspace.
Require Import set.
Require Import list.

Definition linear_span U {V} `{Plus V, Zero V, Neg V, ScalarMult U V}
    (S : V → Prop) :=
    λ v, ∀ sub : Subspace U V, S ⊆ subspace_set sub → subspace_set sub v.

Section Span.

Context U {V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarComp U V UM SM,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM
}.
Variable A : V → Prop.

Let S := linear_span U A.

Lemma linear_span_zero : S 0.
    intros [T T_zero T_plus T_scalar]; cbn.
    intros sub.
    exact T_zero.
Qed.
Lemma linear_span_plus : ∀ a b, S a → S b → S (a + b).
    intros a b Sa Sb T sub.
    specialize (Sa T sub).
    specialize (Sb T sub).
    apply subspace_plus; assumption.
Qed.
Lemma linear_span_scalar : ∀ a v, S v → S (a · v).
    intros a v Sv T sub.
    specialize (Sv T sub).
    apply subspace_scalar.
    exact Sv.
Qed.

Theorem linear_span_combination_ex : ∀ v, S v → ∃ l1 l2 eq,
        (∀ b, in_list l2 b → S b) ∧
        list_unique l2 ∧
        v = linear_combination l1 l2 eq.
    intros v Sv.
    unfold S in Sv.
    unfold linear_span in Sv.
    pose (T (u : V) := ∃ l1 l2 eq,
        (∀ b, in_list l2 b → S b) ∧
        list_unique l2 ∧
        u = linear_combination l1 l2 eq
    ).
    assert (T 0) as T_zero.
    {
        assert (list_size (@list_end U) = list_size (@list_end V)) as eq
            by reflexivity.
        exists list_end, list_end, eq.
        split.
        2: split.
        -   intros b b_in.
            contradiction b_in.
        -   exact true.
        -   reflexivity.
    }
    assert (∀ a b, T a → T b → T (a + b)) as T_plus.
    {
        intros a b.
        intros [a_l1 [a_l2 [a_ls_eq [Sa_l2 [a_l2_uni a_eq]]]]].
        intros [b_l1 [b_l2 [b_ls_eq [Sb_l2 [b_l2_uni b_eq]]]]].
        admit.
    }
    assert (∀ a v, T v → T (a · v)) as T_scalar.
    {
        admit.
    }
    pose (T_sub := make_subspace T T_zero T_plus T_scalar).
    assert (A ⊆ subspace_set T_sub) as A_sub.
    {
        admit.
    }
    specialize (Sv T_sub A_sub).
    cbn in Sv.
    exact Sv.
Abort.

Definition linear_span_subspace := make_subspace S
    linear_span_zero linear_span_plus linear_span_scalar.

Definition linear_span_quotient := quotient_space linear_span_subspace.
Definition to_quotient v :=
    to_equiv_type (subspace_equiv linear_span_subspace) v.
Definition linear_span_quotient_plus
    := quotient_space_plus linear_span_subspace.
Definition linear_span_quotient_plus_assoc
    := quotient_space_plus_assoc linear_span_subspace.
Definition linear_span_quotient_plus_comm
    := quotient_space_plus_comm linear_span_subspace.
Definition linear_span_quotient_zero
    := quotient_space_zero linear_span_subspace.
Definition linear_span_quotient_plus_lid
    := quotient_space_plus_lid linear_span_subspace.
Definition linear_span_quotient_neg
    := quotient_space_neg linear_span_subspace.
Definition linear_span_quotient_plus_linv
    := quotient_space_plus_linv linear_span_subspace.
Definition linear_span_quotient_scalar_mult
    := quotient_space_scalar_mult linear_span_subspace.
Definition linear_span_quotient_scalar_comp
    := quotient_space_scalar_comp linear_span_subspace.
Definition linear_span_quotient_scalar_id
    := quotient_space_scalar_id linear_span_subspace.
Definition linear_span_quotient_scalar_ldist
    := quotient_space_scalar_ldist linear_span_subspace.
Definition linear_span_quotient_scalar_rdist
    := quotient_space_scalar_rdist linear_span_subspace.

End Span.
