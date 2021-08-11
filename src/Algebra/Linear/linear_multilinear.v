Require Import init.

Require Export linear_base.
Require Import set.

(* This is a function from V^k to U *)
Definition k_function U V k := (nat_to_set_type k → V) → U.

Definition k_linear {U V k} `{Mult U, Plus U, Plus V, ScalarMult U V}
    (f : k_function U V k) := ∀ vs i, i < k →
    (∀ α, α * f vs = f (λ n, If [n|] = i then α · vs n else vs n)) ∧
    (∀ a b, f (λ n, If [n|] = i then a + b else vs n) =
        f (λ n, If [n|] = i then a else vs n) +
        f (λ n, If [n|] = i then b else vs n)).

Section KLinearSpace.

Context {U V} `{
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

Variable k : nat.

Let F := set_type (k_linear (k := k)).
Let F_plus_base (A B : F) := λ f, [A|] f + [B|] f.

Lemma k_linear_plus_linear : ∀ A B, k_linear (F_plus_base A B).
    intros [A A_linear] [B B_linear].
    intros vs i i_lt.
    unfold F_plus_base; cbn.
    specialize (A_linear vs i i_lt) as [A_scalar A_dist].
    specialize (B_linear vs i i_lt) as [B_scalar B_dist].
    split.
    -   clear A_dist B_dist.
        intros α.
        specialize (A_scalar α).
        specialize (B_scalar α).
        rewrite ldist.
        rewrite A_scalar, B_scalar.
        reflexivity.
    -   clear A_scalar B_scalar.
        intros a b.
        specialize (A_dist a b).
        specialize (B_dist a b).
        rewrite A_dist, B_dist.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.

Instance F_plus : Plus F := {
    plus A B := [F_plus_base A B | k_linear_plus_linear A B]
}.

Program Instance F_plus_comm : PlusComm F.
Next Obligation.
    unfold plus; cbn.
    unfold F_plus_base.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_comm.
Qed.

Program Instance F_plus_assoc : PlusAssoc F.
Next Obligation.
    unfold plus; cbn.
    unfold F_plus_base.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_assoc.
Qed.

Lemma zero_k_linear : k_linear (k := k) (λ f, 0).
    intros vs i i_lt.
    split.
    -   intros α.
        apply mult_ranni.
    -   intros a b.
        rewrite plus_rid.
        reflexivity.
Qed.

Instance F_zero : Zero F := {
    zero := [λ f, 0 | zero_k_linear]
}.

Program Instance F_plus_lid : PlusLid F.
Next Obligation.
    unfold zero, plus; cbn.
    unfold F_plus_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_lid.
Qed.

Let F_neg_base (A : F) := λ f, -[A|] f.

Lemma neg_k_linear : ∀ A, k_linear (F_neg_base A).
    intros [A A_linear].
    intros vs i i_lt.
    unfold F_neg_base; cbn.
    specialize (A_linear vs i i_lt) as [A_scalar A_dist].
    split.
    -   clear A_dist.
        intros α.
        specialize (A_scalar α).
        rewrite mult_rneg.
        rewrite A_scalar.
        reflexivity.
    -   clear A_scalar.
        intros a b.
        specialize (A_dist a b).
        rewrite A_dist.
        apply neg_plus.
Qed.

Instance F_neg : Neg F := {
    neg A := [F_neg_base A | neg_k_linear A]
}.

Program Instance F_plus_linv : PlusLinv F.
Next Obligation.
    unfold plus, neg, zero; cbn.
    unfold F_plus_base, F_neg_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_linv.
Qed.

Let F_scalar_base α (A : F) := λ f, α * [A|] f.

Lemma scalar_k_linear : ∀ α A, k_linear (F_scalar_base α A).
    intros α [A A_linear].
    intros vs i i_lt.
    unfold F_scalar_base; cbn.
    specialize (A_linear vs i i_lt) as [A_scalar A_dist].
    split.
    -   clear A_dist.
        intros β.
        specialize (A_scalar β).
        rewrite mult_assoc.
        rewrite (mult_comm β α).
        rewrite <- mult_assoc.
        rewrite A_scalar.
        reflexivity.
    -   clear A_scalar.
        intros a b.
        specialize (A_dist a b).
        rewrite A_dist.
        apply ldist.
Qed.

Instance F_scalar_mult : ScalarMult U F := {
    scalar_mult α A := [F_scalar_base α A | scalar_k_linear α A]
}.

Program Instance F_scalar_comp : ScalarComp U F.
Next Obligation.
    unfold scalar_mult; cbn.
    unfold F_scalar_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply mult_assoc.
Qed.

Program Instance F_scalar_id : ScalarId U F.
Next Obligation.
    unfold scalar_mult; cbn.
    unfold F_scalar_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply mult_lid.
Qed.

Program Instance F_scalar_ldist : ScalarLdist U F.
Next Obligation.
    unfold plus, scalar_mult; cbn.
    unfold F_scalar_base, F_plus_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply ldist.
Qed.

Program Instance F_scalar_rdist : ScalarRdist U F.
Next Obligation.
    unfold plus at 2, scalar_mult; cbn.
    unfold F_scalar_base, F_plus_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply rdist.
Qed.

End KLinearSpace.
