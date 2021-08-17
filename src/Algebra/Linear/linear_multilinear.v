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

End KLinearSpace.
