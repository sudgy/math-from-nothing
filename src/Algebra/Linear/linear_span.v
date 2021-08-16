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
