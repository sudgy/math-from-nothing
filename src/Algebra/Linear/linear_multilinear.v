Require Import init.

Require Export linear_base.
Require Import linear_basis.
Require Import set.
Require Import list.

(* This is a function from V^k to U *)
Definition k_function U V k := (nat_to_set_type k → V) → U.

Definition k_linear {U V k} `{Mult U, Plus U, Plus V, ScalarMult U V}
    (f : k_function U V k) := ∀ vs i, i < k →
    (∀ α, α * f vs = f (λ n, If [n|] = i then α · vs n else vs n)) ∧
    (∀ a b, f (λ n, If [n|] = i then a + b else vs n) =
        f (λ n, If [n|] = i then a else vs n) +
        f (λ n, If [n|] = i then b else vs n)).

Section KLinearSpace.

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

Section KLinear.

Variable k : nat.

Definition multilinear_type := set_type (k_linear (k := k)).
Let F := multilinear_type.
Let multilinear_plus_base (A B : F) := λ f, [A|] f + [B|] f.

Lemma k_linear_plus_linear : ∀ A B, k_linear (multilinear_plus_base A B).
    intros [A A_linear] [B B_linear].
    intros vs i i_lt.
    unfold multilinear_plus_base; cbn.
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

Instance multilinear_plus : Plus F := {
    plus A B := [multilinear_plus_base A B | k_linear_plus_linear A B]
}.

Program Instance multilinear_plus_comm : PlusComm F.
Next Obligation.
    unfold plus; cbn.
    unfold multilinear_plus_base.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_comm.
Qed.

Program Instance multilinear_plus_assoc : PlusAssoc F.
Next Obligation.
    unfold plus; cbn.
    unfold multilinear_plus_base.
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

Instance multilinear_zero : Zero F := {
    zero := [λ f, 0 | zero_k_linear]
}.

Program Instance multilinear_plus_lid : PlusLid F.
Next Obligation.
    unfold zero, plus; cbn.
    unfold multilinear_plus_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_lid.
Qed.

Let multilinear_neg_base (A : F) := λ f, -[A|] f.

Lemma neg_k_linear : ∀ A, k_linear (multilinear_neg_base A).
    intros [A A_linear].
    intros vs i i_lt.
    unfold multilinear_neg_base; cbn.
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

Instance multilinear_neg : Neg F := {
    neg A := [multilinear_neg_base A | neg_k_linear A]
}.

Program Instance multilinear_plus_linv : PlusLinv F.
Next Obligation.
    unfold plus, neg, zero; cbn.
    unfold multilinear_plus_base, multilinear_neg_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_linv.
Qed.

Let multilinear_scalar_base α (A : F) := λ f, α * [A|] f.

Lemma scalar_k_linear : ∀ α A, k_linear (multilinear_scalar_base α A).
    intros α [A A_linear].
    intros vs i i_lt.
    unfold multilinear_scalar_base; cbn.
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

Instance multilinear_scalar_mult : ScalarMult U F := {
    scalar_mult α A := [multilinear_scalar_base α A | scalar_k_linear α A]
}.

Program Instance multilinear_scalar_comp : ScalarComp U F.
Next Obligation.
    unfold scalar_mult; cbn.
    unfold multilinear_scalar_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply mult_assoc.
Qed.

Program Instance multilinear_scalar_id : ScalarId U F.
Next Obligation.
    unfold scalar_mult; cbn.
    unfold multilinear_scalar_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply mult_lid.
Qed.

Program Instance multilinear_scalar_ldist : ScalarLdist U F.
Next Obligation.
    unfold plus, scalar_mult; cbn.
    unfold multilinear_scalar_base, multilinear_plus_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply ldist.
Qed.

Program Instance multilinear_scalar_rdist : ScalarRdist U F.
Next Obligation.
    unfold plus at 2, scalar_mult; cbn.
    unfold multilinear_scalar_base, multilinear_plus_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply rdist.
Qed.

End KLinear.

Existing Instance multilinear_plus.
Existing Instance multilinear_plus_comm.
Existing Instance multilinear_plus_assoc.
Existing Instance multilinear_zero.
Existing Instance multilinear_plus_lid.
Existing Instance multilinear_neg.
Existing Instance multilinear_plus_linv.
Existing Instance multilinear_scalar_mult.

Definition multilinear_type_k_eq k n (A : multilinear_type k) (eq : n = k) :
        (multilinear_type n).
    rewrite eq.
    exact A.
Defined.

Definition f_k_eq k n (f : nat_to_set_type k → V)
        (eq : n = k) :
        nat_to_set_type n → V.
    rewrite eq.
    exact f.
Defined.

Theorem multilinear_f_kn_eq : ∀ k n (eq : n = k)
        (A : multilinear_type n) (B : multilinear_type k),
        (∀ f : nat_to_set_type k → V,
            [A|] (f_k_eq k n f eq) = [B|] f) →
        A = multilinear_type_k_eq k n B eq.
    intros k n eq A B f_eq.
    subst n.
    cbn in *.
    apply set_type_eq.
    apply functional_ext.
    exact f_eq.
Qed.

Lemma m_f_kn_eq : ∀ k n (eq : n = k)
        (f : nat_to_set_type k → V),
        ∀ m (H1 : m < k) (H2 : m < n),
        f [m|H1] = f_k_eq k n f eq [m|H2].
    intros k n eq f m lt1 lt2.
    unfold f_k_eq, Logic.eq_rect_r, Logic.eq_rect.
    destruct (Logic.eq_sym _).
    rewrite (proof_irrelevance lt1 lt2).
    reflexivity.
Qed.

Definition multilinear_mult_base {k1 k2}
    (A : multilinear_type k1) (B : multilinear_type k2)
    : k_function U V (k1 + k2)
    := λ f, [A|] (λ n, f [[n|] | lt_le_trans [|n] (nat_le_self_rplus k1 k2)])
          * [B|] (λ n, f [k1 + [n|] | lt_lplus k1 [|n]]).

Section MultilinearMultMultilinear.

Context {k1 k2 : nat}.
Variables (A : multilinear_type k1) (B : multilinear_type k2).

Lemma multilinear_mult_multilinear : k_linear (multilinear_mult_base A B).
    rename A into A', B into B'.
    destruct A' as [A A_linear].
    destruct B' as [B B_linear].
    intros vs i i_gt.
    unfold multilinear_mult_base; cbn.
    classic_case (i < k1) as [i_lt|i_ge].
    -   specialize (A_linear
           (λ n : nat_to_set_type k1, vs [[n | ] |
               lt_le_trans [ | n] (nat_le_self_rplus k1 k2)]) i i_lt)
            as [A_scalar A_dist].
        split.
        +   clear A_dist.
            intros α.
            specialize (A_scalar α); cbn in A_scalar.
            rewrite mult_assoc.
            rewrite A_scalar.
            apply lmult.
            apply f_equal.
            apply functional_ext.
            intros [n n_lt]; cbn.
            case_if.
            *   exfalso; clear - i_lt e.
                subst i.
                rewrite <- nle_lt in i_lt.
                apply i_lt.
                apply nat_le_self_rplus.
            *   reflexivity.
        +   clear A_scalar.
            intros a b.
            specialize (A_dist a b); cbn in A_dist.
            rewrite A_dist.
            rewrite rdist.
            apply f_equal2.
            all: apply f_equal2; try reflexivity.
            *   apply f_equal.
                apply functional_ext.
                intros [n n_lt]; cbn.
                case_if.
                2: reflexivity.
                exfalso; clear - i_lt e.
                subst i.
                rewrite <- nle_lt in i_lt.
                apply i_lt.
                apply nat_le_self_rplus.
            *   apply f_equal.
                apply functional_ext.
                intros [n n_lt]; cbn.
                case_if.
                2: reflexivity.
                exfalso; clear - i_lt e.
                subst i.
                rewrite <- nle_lt in i_lt.
                apply i_lt.
                apply nat_le_self_rplus.
    -   rewrite nlt_le in i_ge.
        apply nat_le_ex in i_ge as [c i_eq]; subst i.
        apply lt_plus_lcancel in i_gt.
        specialize (B_linear (λ n : nat_to_set_type k2, vs [k1 + [n | ] |
            lt_lplus k1 [ | n]]) c i_gt) as [B_scalar B_dist].
        split.
        +   clear B_dist.
            intros α.
            specialize (B_scalar α).
            rewrite mult_assoc.
            rewrite (mult_comm α).
            rewrite <- mult_assoc.
            rewrite B_scalar.
            apply f_equal2.
            *   apply f_equal.
                apply functional_ext.
                intros [n n_lt]; cbn.
                case_if.
                2: reflexivity.
                exfalso; clear - n_lt e.
                unfold nat_to_set in n_lt.
                subst n.
                rewrite <- nle_lt in n_lt.
                apply n_lt.
                apply nat_le_self_rplus.
            *   apply f_equal.
                apply functional_ext.
                intros [n n_lt]; cbn.
                assert ((n = c) = (k1 + n = k1 + c)) as eq.
                {
                    apply propositional_ext.
                    split.
                    -   apply lplus.
                    -   apply plus_lcancel.
                }
                rewrite eq.
                reflexivity.
        +   clear B_scalar.
            intros a b.
            specialize (B_dist a b).
            assert (∀ n, (n = c) = (k1 + n = k1 + c)) as n_eq.
            {
                intros n.
                apply propositional_ext.
                split.
                -   apply lplus.
                -   apply plus_lcancel.
            }
            assert (
  (λ n : nat_to_set_type k2,
     If k1 + [n | ] = k1 + c then a + b
     else vs [k1 + [n | ] | lt_lplus k1 [ | n]]) =
           (λ n : nat_to_set_type k2,
              If [n | ] = c then a + b
              else vs [k1 + [n | ] | lt_lplus k1 [ | n]])) as eq.
            {
                clear - n_eq.
                apply functional_ext.
                intros [n n_lt]; cbn.
                rewrite n_eq.
                reflexivity.
            }
            rewrite eq; clear eq.
            rewrite B_dist; clear B_dist.
            rewrite ldist.
            apply f_equal2.
            all: apply f_equal2.
            *   apply f_equal.
                apply functional_ext.
                intros [n n_lt]; cbn.
                case_if.
                2: reflexivity.
                exfalso; clear - n_lt e.
                unfold nat_to_set in n_lt.
                subst n.
                rewrite <- nle_lt in n_lt.
                apply n_lt.
                apply nat_le_self_rplus.
            *   apply f_equal.
                apply functional_ext.
                intros n.
                rewrite n_eq.
                reflexivity.
            *   apply f_equal.
                apply functional_ext.
                intros [n n_lt]; cbn.
                case_if.
                2: reflexivity.
                exfalso; clear - n_lt e.
                unfold nat_to_set in n_lt.
                subst n.
                rewrite <- nle_lt in n_lt.
                apply n_lt.
                apply nat_le_self_rplus.
            *   apply f_equal.
                apply functional_ext.
                intros n.
                rewrite n_eq.
                reflexivity.
Qed.

Definition multilinear_mult :=
    [multilinear_mult_base A B | multilinear_mult_multilinear].

End MultilinearMultMultilinear.

Section MultilinearMultDist.

Context {k1 k2 k3 : nat}.
Variables (A : multilinear_type k1)
          (B : multilinear_type k2)
          (C : multilinear_type k2)
          (D : multilinear_type k3).

Theorem multilinear_mult_ldist :
        multilinear_mult A (B + C) =
        multilinear_mult A B + multilinear_mult A C.
    unfold multilinear_mult, plus; cbn.
    unfold multilinear_mult_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros f.
    apply ldist.
Qed.

Theorem multilinear_mult_rdist :
        multilinear_mult (B + C) A =
        multilinear_mult B A + multilinear_mult C A.
    unfold multilinear_mult, plus; cbn.
    unfold multilinear_mult_base; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros f.
    apply rdist.
Qed.

End MultilinearMultDist.

Theorem multilinear_mult_lanni : ∀ k1 k2 (A : multilinear_type k2),
        multilinear_mult (zero (U := multilinear_type k1)) A = 0.
    intros k1 k2 A.
    assert (multilinear_mult (zero (U := multilinear_type k1)) A
        = multilinear_mult 0 A) as eq by reflexivity.
    rewrite <- (plus_rid 0) in eq at 1.
    rewrite multilinear_mult_rdist in eq.
    apply plus_0_a_ba_b in eq.
    symmetry; exact eq.
Qed.

Theorem multilinear_mult_ranni : ∀ k1 k2 (A : multilinear_type k2),
        multilinear_mult A (zero (U := multilinear_type k1)) = 0.
    intros k1 k2 A.
    assert (multilinear_mult A (zero (U := multilinear_type k1))
        = multilinear_mult A 0) as eq by reflexivity.
    rewrite <- (plus_rid 0) in eq at 1.
    rewrite multilinear_mult_ldist in eq.
    apply plus_0_a_ba_b in eq.
    symmetry; exact eq.
Qed.

Theorem multilinear_mult_assoc : ∀ {k1 k2 k3}
        (A : multilinear_type k1)
        (B : multilinear_type k2)
        (C : multilinear_type k3),
        multilinear_mult A (multilinear_mult B C) =
        multilinear_type_k_eq _ _
            (multilinear_mult (multilinear_mult A B) C)
        (plus_assoc k1 k2 k3).
    intros k1 k2 k3 A B C.
    apply multilinear_f_kn_eq.
    intros f.
    unfold multilinear_mult, multilinear_mult_base; cbn.
    rewrite mult_assoc.
    apply f_equal2.
    1: apply f_equal2.
    -   apply f_equal.
        apply functional_ext.
        intros n.
        symmetry.
        apply m_f_kn_eq.
    -   apply f_equal.
        apply functional_ext.
        intros n.
        symmetry.
        apply m_f_kn_eq.
    -   apply f_equal.
        apply functional_ext.
        intros n.
        symmetry.
        assert (nat_to_set (k1 + (k2 + k3)) (k1 + k2 + [n|])) as ltq.
        {
            unfold nat_to_set.
            rewrite plus_assoc.
            apply lt_lplus.
            exact [|n].
        }
        assert ([k1 + (k2 + [n|]) | lt_lplus k1 (lt_lplus k2 [|n])] =
            [k1 + k2 + [n|]|ltq]) as eq.
        {
            apply set_type_eq; cbn.
            apply plus_assoc.
        }
        rewrite eq.
        apply m_f_kn_eq.
Qed.

Definition scalar_to_multilinear_base (α : U) : k_function U V 0 := λ _, α.

Lemma scalar_to_multilinear_linear :
        ∀ α, k_linear (scalar_to_multilinear_base α).
    intros α f i i_lt.
    contradiction (nat_lt_zero i i_lt).
Qed.

Definition scalar_to_multilinear α := [_|scalar_to_multilinear_linear α].

Theorem scalar_to_multilinear_eq : ∀ α β,
        scalar_to_multilinear α = scalar_to_multilinear β → α = β.
    intros α β eq.
    apply eq_set_type in eq; cbn in eq.
    unfold scalar_to_multilinear_base in eq.
    pose proof (func_eq _ _ eq) as eq2.
    cbn in eq2.
    apply eq2.
    intros [a a_lt].
    contradiction (nat_lt_zero a a_lt).
Qed.

Theorem scalar_to_multilinear_plus : ∀ α β,
        scalar_to_multilinear α + scalar_to_multilinear β =
        scalar_to_multilinear (α + β).
    intros α β.
    unfold plus at 1; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros f.
    unfold scalar_to_multilinear_base; cbn.
    reflexivity.
Qed.

Theorem scalar_to_multilinear_mult : ∀ α β,
        multilinear_mult (scalar_to_multilinear α) (scalar_to_multilinear β) =
        scalar_to_multilinear (α * β).
    intros α β.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros f.
    unfold multilinear_mult_base; cbn.
    unfold scalar_to_multilinear_base; cbn.
    reflexivity.
Qed.

Theorem scalar_to_multilinear_scalar {k} : ∀ α (A : multilinear_type k),
        multilinear_mult (scalar_to_multilinear α) A =
        α · A.
    intros α A.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros f.
    unfold multilinear_mult_base; cbn.
    unfold scalar_to_multilinear_base; cbn.
    apply f_equal.
    apply f_equal.
    apply functional_ext.
    intros x.
    apply f_equal.
    apply set_type_eq; cbn.
    apply plus_lid.
Qed.

Theorem scalar_to_multilinear_comm {k} : ∀ α (A : multilinear_type k),
        multilinear_mult (scalar_to_multilinear α) A =
        multilinear_type_k_eq _ _
            (multilinear_mult A (scalar_to_multilinear α))
        (plus_comm _ _).
    intros α A.
    apply multilinear_f_kn_eq.
    intros f.
    unfold multilinear_mult, multilinear_mult_base; cbn.
    unfold scalar_to_multilinear_base; cbn.
    rewrite mult_comm.
    apply f_equal2.
    2: reflexivity.
    apply f_equal.
    apply functional_ext.
    intros n.
    symmetry.
    apply m_f_kn_eq.
Qed.

End KLinearSpace.

Section VectorToMultilinear.

Variables U V : Type.

Context `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    UD : Div U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    @Ldist U UP UM,
    @MultComm U UM,
    @MultAssoc U UM,
    @MultLid U UM UO,
    @MultLinv U UZ UM UO UD,
    @NotTrivial U UZ UO,

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

Definition vector_to_multilinear_base (v : V)
    : k_function U (multilinear_type U V 1) 1
    := λ f, [f [0|nat_0_lt_1]|] (λ n, v).

Lemma vector_to_multilinear_linear :
        ∀ v, k_linear (vector_to_multilinear_base v).
    intros v f i i_lt.
    apply nat_lt_1 in i_lt.
    subst i.
    unfold vector_to_multilinear_base; cbn.
    case_if.
    2: contradiction.
    split.
    -   intros α.
        unfold scalar_mult; cbn.
        reflexivity.
    -   intros a b.
        unfold plus at 1; cbn.
        reflexivity.
Qed.

Definition vector_to_multilinear v := [_|vector_to_multilinear_linear v].

Lemma linear_functional_eq : ∀ a b : V,
        (λ n : nat_to_set_type 1, If [n|] = 0 then a else b) = (λ n, a).
    intros a b.
    apply functional_ext.
    intros [n n_ltq].
    unfold nat_to_set in n_ltq.
    cbn.
    apply nat_lt_1 in n_ltq.
    subst n.
    case_if.
    -   reflexivity.
    -   contradiction.
Qed.

Lemma linear_functional_eq2 : ∀ a b : (nat_to_set_type 1 → V),
        (λ n, If [n|] = 0 then a n else b n) = (λ n, a [0|nat_0_lt_1]).
    intros a b.
    apply functional_ext.
    intros [x x_lt]; cbn.
    case_if.
    -   subst.
        apply f_equal.
        apply set_type_eq; reflexivity.
    -   exfalso.
        apply nat_lt_1 in x_lt.
        symmetry in x_lt; contradiction.
Qed.
(*
Definition single_v_multilinear_f (v : V) (v_nz : 0 ≠ v) : k_function U V 1 :=
    let B := basis_extend_ex _ (singleton_linearly_independent v v_nz) in
    λ f : (nat_to_set_type 1 → V),
    let l := basis_coefficients (ex_val B) (rand (ex_proof B)) (f [0|nat_0_lt_1]) in
    match (strong_excluded_middle (∃ a, in_list [l|] (a, v))) with
    | strong_or_left H => ex_val H
    | strong_or_right _ => 0
    end.

Local Arguments basis_coefficients: simpl never.

Lemma single_v_multilinear_H : ∀ v v_nz, k_linear (single_v_multilinear_f v v_nz).
    intros v v_nz vs i i_lt.
    apply nat_lt_1 in i_lt.
    subst i.
    pose (B_ex := basis_extend_ex _ (singleton_linearly_independent v v_nz)).
    pose (B := ex_val B_ex).
    pose (sub_B := land (ex_proof B_ex)).
    pose (B_basis := rand (ex_proof B_ex)).
    change (ex_type_val (ex_to_type B_ex)) with B in *.
    split.
    -   intros a.
        rewrite linear_functional_eq2.
        unfold single_v_multilinear_f.
        fold B_ex B.
        change (rand (ex_proof B_ex)) with B_basis.
        destruct (strong_excluded_middle _) as [v_in_l'|v_nin_l];
        destruct (strong_excluded_middle _) as [v_in_al'|v_nin_al].
        +   rewrite_ex_val b v_in_l; clear v_in_l'.
            rewrite_ex_val c v_in_al; clear v_in_al'.
        +   rewrite_ex_val b v_in_l; clear v_in_l'.
        +   
        +   apply mult_ranni.
    -   intros u1 u2.
        do 3 rewrite linear_functional_eq2.
        unfold single_v_multilinear_f.
        fold B_ex B.
        change (rand (ex_proof B_ex)) with B_basis.

Definition single_v_multilinear v v_nz : multilinear_type U V 1
    := [single_v_multilinear_f v v_nz | single_v_multilinear_H v v_nz].

Theorem vector_to_multilinear_eq :  ∀ u v,
        vector_to_multilinear u = vector_to_multilinear v → u = v.
    intros u v eq.
    apply eq_set_type in eq; cbn in eq.
    unfold vector_to_multilinear_base in eq.
    pose proof (func_eq _ _ eq) as eq2; cbn in eq2.
    clear eq.
    assert (∀ f : nat_to_set_type 1 → multilinear_type U V 1,
        0 = [f [0|nat_0_lt_1]|] (λ _, u - v)) as f0.
    {
        intros f.
        specialize (eq2 f).
        pose proof [|f [0 | nat_0_lt_1]] as f_linear.
        specialize (f_linear (λ n, v) 0 nat_0_lt_1) as [f_linear1 f_linear2].
        apply plus_0_anb_a_b in eq2.
        specialize (f_linear1 (-(1))).
        rewrite linear_functional_eq in f_linear1.
        rewrite mult_lneg in f_linear1.
        rewrite mult_lid in f_linear1.
        rewrite f_linear1 in eq2.
        rewrite scalar_neg_one in eq2.
        specialize (f_linear2 u (-v)).
        do 3 rewrite linear_functional_eq in f_linear2.
        rewrite <- f_linear2 in eq2.
        exact eq2.
    }
    clear eq2.

    classic_contradiction neq.
    assert (0 ≠ u - v) as v_neq.
    {
        intros contr.
        rewrite plus_0_anb_a_b in contr.
        contradiction.
    }
    clear neq.
    rename v into v'.
    remember (u - v') as v.
    clear u v' Heqv.
    specialize (f0 (λ _, single_v_multilinear _ v_neq)).
    cbn in f0.
    unfold single_v_multilinear_f in f0.
    unfold ex_val, ex_proof in f0.
    destruct (ex_to_type _) as [B [sub_B B_basis]]; cbn in *.
    rewrite_ex_val l [l_eq Bl].
    destruct (strong_excluded_middle _) as [v_in'|v_nin].
    -   destruct (ex_to_type _) as [a v_in]; cbn in *.
        clear v_in'.
        subst a.
        apply list_filter_in_S in v_in.
        contradiction.
    -   clear f0.
        pose (l' := (-(1), v) :: [linear_remove_zeros l|]).
        assert (linear_combination_set l') as l'_comb.
        {
            split.
            -   cbn.
                intros contr.
                apply v_nin.
                apply image_in_list in contr as [[a v'] [v'_eq v_in]].
                cbn in v'_eq.
                subst v'.
                exists a.
                exact v_in.
            -   exact [|linear_remove_zeros l].
        }
        assert (0 = linear_combination [l'|l'_comb]) as l'_eq.
        {
            unfold l'.
            rewrite (linear_combination_add _ _ _ [|linear_remove_zeros l]).
            change (fst (-(1), v) · snd (-(1), v)) with (-(1) · v).
            rewrite scalar_neg_one.
            rewrite plus_0_nab_a_b.
            rewrite l_eq.
            change [[linear_remove_zeros l|] | [|linear_remove_zeros l]]
                with (linear_remove_zeros l).
            apply linear_combination_remove_zeros.
        }
        assert (linear_list_in B [l'|l'_comb]) as Bl'.
        {
            intros u [b u_in].
            destruct u_in as [u_eq|u_in].
            -   inversion u_eq; subst u b.
                apply sub_B.
                reflexivity.
            -   apply Bl.
                exists b.
                apply list_filter_in in u_in.
                exact u_in.
        }
        apply not_trivial.
        rewrite <- neg_neg.
        rewrite <- (neg_neg 0).
        apply f_equal.
        rewrite neg_zero.
        apply (land B_basis [l'|l'_comb] Bl' l'_eq).
        exists v.
        left.
        reflexivity.
Qed.
*)
Theorem vector_to_multilinear_plus : ∀ u v,
        vector_to_multilinear u + vector_to_multilinear v =
        vector_to_multilinear (u + v).
    intros u v.
    apply set_type_eq; cbn.
    unfold plus at 1; cbn.
    unfold vector_to_multilinear_base.
    apply functional_ext.
    intros f.
    pose proof [|f [0 | nat_0_lt_1]] as f_linear.
    specialize (f_linear (λ n, u) 0 nat_0_lt_1) as [f_linear1 f_linear2].
    specialize (f_linear2 u v).
    do 3 rewrite linear_functional_eq in f_linear2.
    symmetry; exact f_linear2.
Qed.

Theorem vector_to_multilinear_scalar : ∀ α v,
        α · (vector_to_multilinear v) =
        vector_to_multilinear (α · v).
    intros α v.
    apply set_type_eq; cbn.
    unfold scalar_mult at 1; cbn.
    unfold vector_to_multilinear_base.
    apply functional_ext.
    intros f.
    pose proof [|f [0 | nat_0_lt_1]] as f_linear.
    specialize (f_linear (λ n, v) 0 nat_0_lt_1) as [f_linear1 f_linear2].
    specialize (f_linear1 α).
    rewrite linear_functional_eq in f_linear1.
    exact f_linear1.
Qed.

End VectorToMultilinear.
