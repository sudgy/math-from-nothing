Require Import init.

Require Export tensor_algebra_base.
Require Import tensor_algebra_grade.
Require Import tensor_algebra_mult1.
Require Import tensor_algebra_mult2.
Require Import linear_multilinear.
Require Import list.
Require Import set.
Require Import plus_sum.

(** This file contains facts about scalars in the tensor algebra, such as the
canonical injection and a few more facts about multiplication relating to
scalars.
*)

(* begin hide *)
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
Let T25 := tensor_plus U V.
Let T26 := tensor_plus_comm U V.
Let T27 := tensor_plus_assoc U V.
Let T28 := tensor_zero U V.
Let T29 := tensor_plus_lid U V.
Let T30 := tensor_neg U V.
Let T31 := tensor_plus_linv U V.
Let T32 := tensor_scalar_mult U V.
Let T33 := tensor_scalar_comp U V.
Let T34 := tensor_scalar_id U V.
Let T35 := tensor_scalar_ldist U V.
Let T36 := tensor_scalar_rdist U V.
Let T37 := tensor_mult U V.
Let T38 := tensor_mult_ldist U V.
Let T39 := tensor_mult_rdist U V.
Let T40 := tensor_mult_assoc U V.
Existing Instances T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27
    T28 T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40.
(* end hide *)
Let multi_type k := multilinear_type U (multilinear_type U V 1) k.

Definition scalar_to_tensor α :=
    multilinear_to_tensor U V (scalar_to_multilinear _ _ α).

Theorem scalar_to_tensor_plus : ∀ α β,
        scalar_to_tensor α + scalar_to_tensor β =
        scalar_to_tensor (α + β).
    intros α β.
    unfold scalar_to_tensor.
    rewrite multilinear_to_tensor_plus.
    apply f_equal.
    apply scalar_to_multilinear_plus.
Qed.

Theorem scalar_to_tensor_zero : scalar_to_tensor 0 = 0.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros x.
    unfold multilinear_to_tensor_base.
    destruct (strong_excluded_middle (x = 0)) as [x_z|x_nz].
    -   subst.
        cbn.
        apply set_type_eq; cbn.
        unfold scalar_to_multilinear_base; cbn.
        apply functional_ext.
        intros x.
        reflexivity.
    -   reflexivity.
Qed.

Theorem scalar_to_tensor_homogeneous : ∀ α,
        homogeneous_tensor U V (scalar_to_tensor α).
    intros α.
    exists 0, (scalar_to_multilinear _ _ α).
    reflexivity.
Qed.

Theorem scalar_to_tensor_decompose : ∀ α, 0 ≠ α →
        tensor_decompose_grade U V (scalar_to_tensor α) =
        [_|scalar_to_tensor_homogeneous α] :: list_end.
    intros α α_neq.
    unfold tensor_decompose_grade.
    assert (tensor_max_nz U V (scalar_to_tensor α) = 1) as nz_eq.
    {
        remember (tensor_max_nz U V (scalar_to_tensor α)) as n.
        assert (0 < n) as ltq.
        {
            rewrite Heqn.
            apply tensor_max_nz_leq.
            intros contr.
            apply eq_set_type in contr; cbn in contr.
            unfold multilinear_to_tensor_base in contr.
            destruct (strong_excluded_middle (0 = 0)) as [eq|neq];
                try contradiction.
            unfold multilinear_type_k_eq, Logic.eq_rect_r, Logic.eq_rect in contr.
            destruct (Logic.eq_sym eq).
            unfold scalar_to_multilinear in contr; cbn in contr.
            unfold zero in contr; cbn in contr.
            unfold scalar_to_multilinear_base in contr.
            pose proof (func_eq _ _ contr) as eq2; clear contr.
            cbn in eq2.
            apply α_neq.
            apply eq2.
            intros [a a_lt].
            contradiction (nat_lt_zero a a_lt).
        }
        nat_destruct n.
        -   destruct ltq; contradiction.
        -   pose proof (tensor_max_nz_least U V _ _ Heqn) as neq.
            symmetry; classic_contradiction contr.
            apply neq; clear neq.
            unfold zero; cbn.
            apply set_type_eq; cbn.
            apply functional_ext.
            intros f.
            unfold multilinear_to_tensor_base; cbn.
            destruct (strong_excluded_middle (n = 0)) as [eq|neq].
            +   exfalso; symmetry in eq.
                apply (f_equal nat_suc) in eq.
                contradiction.
            +   reflexivity.
    }
    rewrite nz_eq.
    unfold one; cbn.
    apply f_equal2.
    2: reflexivity.
    apply set_type_eq; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    unfold multilinear_to_tensor_base.
    change nat_zero with (zero (U := nat)).
    case_if; reflexivity.
Qed.

Theorem scalar_to_tensor_mult : ∀ α β,
        scalar_to_tensor α * scalar_to_tensor β =
        scalar_to_tensor (α * β).
    intros α β.
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst α.
        rewrite scalar_to_tensor_zero.
        do 2 rewrite mult_lanni.
        rewrite scalar_to_tensor_zero.
        reflexivity.
    }
    classic_case (0 = β) as [β_z|β_nz].
    {
        subst β.
        rewrite scalar_to_tensor_zero.
        do 2 rewrite mult_ranni.
        rewrite scalar_to_tensor_zero.
        reflexivity.
    }
    unfold mult at 1; cbn.
    rewrite scalar_to_tensor_decompose by exact α_nz.
    rewrite scalar_to_tensor_decompose by exact β_nz.
    cbn.
    unfold scalar_to_tensor.
    rewrite multilinear_to_tensor_tm.
    rewrite scalar_to_multilinear_mult.
    apply plus_rid.
Qed.

Theorem scalar_to_tensor_scalar : ∀ α (A : tensor_algebra U V),
        scalar_to_tensor α * A = α · A.
    intros α A.
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst α.
        rewrite scalar_to_tensor_zero.
        rewrite mult_lanni.
        rewrite scalar_lanni.
        reflexivity.
    }
    rewrite (tensor_decompose_grade_eq U V A).
    remember (tensor_decompose_grade U V A) as al.
    clear Heqal A.
    induction al.
    {
        cbn.
        rewrite mult_ranni.
        rewrite scalar_ranni.
        reflexivity.
    }
    cbn.
    rewrite ldist.
    rewrite scalar_ldist.
    rewrite IHal; clear IHal.
    apply rplus; clear al.
    unfold mult at 1; cbn.
    rewrite scalar_to_tensor_decompose by exact α_nz.
    rewrite list_prod2_lconc.
    rewrite list_prod2_lend.
    cbn.
    rewrite plus_lid.
    rewrite tensor_rmult_homogeneous.
    destruct a as [a a_homo]; cbn.
    destruct a_homo as [k [A A_eq]].
    subst a.
    unfold scalar_to_tensor.
    rewrite multilinear_to_tensor_tm.
    rewrite scalar_to_multilinear_scalar.
    unfold scalar_mult at 2; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros x.
    unfold multilinear_to_tensor_base.
    assert (strong_excluded_middle (x = 0 + k) =
            strong_excluded_middle (x = k)) as eq_eq.
    {
        destruct (strong_excluded_middle (x = 0 + k)) as [eq1|neq1];
        destruct (strong_excluded_middle (x = k)) as [eq2|neq2].
        -   apply f_equal.
            apply proof_irrelevance.
        -   exfalso; rewrite plus_lid in eq1.
            contradiction.
        -   exfalso; rewrite plus_lid in neq1.
            contradiction.
        -   apply f_equal.
            apply proof_irrelevance.
    }
    rewrite eq_eq; clear eq_eq.
    destruct (strong_excluded_middle (x = k)) as [eq|neq].
    -   subst; cbn.
        reflexivity.
    -   rewrite scalar_ranni.
        reflexivity.
Qed.

Theorem scalar_to_tensor_comm : ∀ α (A : tensor_algebra U V),
        scalar_to_tensor α * A = A * scalar_to_tensor α.
    intros α A.
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst α.
        rewrite scalar_to_tensor_zero.
        rewrite mult_lanni.
        rewrite mult_ranni.
        reflexivity.
    }
    rewrite (tensor_decompose_grade_eq U V A).
    remember (tensor_decompose_grade U V A) as al.
    clear Heqal A.
    induction al.
    {
        cbn.
        rewrite mult_lanni.
        rewrite mult_ranni.
        reflexivity.
    }
    cbn.
    rewrite ldist.
    rewrite rdist.
    rewrite IHal; clear IHal.
    apply rplus; clear al.
    unfold mult; cbn.
    rewrite scalar_to_tensor_decompose by exact α_nz.
    rewrite list_prod2_lconc.
    rewrite list_prod2_lend.
    rewrite list_prod2_rconc.
    rewrite list_prod2_rend.
    cbn.
    do 2 rewrite plus_lid.
    rewrite tensor_lmult_homogeneous.
    rewrite tensor_rmult_homogeneous.
    destruct a as [a a_homo]; cbn.
    destruct a_homo as [k [A A_eq]].
    subst a.
    unfold scalar_to_tensor.
    do 2 rewrite multilinear_to_tensor_tm.
    rewrite scalar_to_multilinear_comm.
    symmetry.
    apply multilinear_to_tensor_k_eq.
Qed.

Program Instance tensor_scalar_lmult : ScalarLMult U (tensor_algebra U V).
Next Obligation.
    do 2 rewrite <- scalar_to_tensor_scalar.
    rewrite mult_assoc.
    reflexivity.
Qed.

Program Instance tensor_scalar_rmult : ScalarRMult U (tensor_algebra U V).
Next Obligation.
    do 2 rewrite <- scalar_to_tensor_scalar.
    do 2 rewrite mult_assoc.
    rewrite (scalar_to_tensor_comm _ u).
    reflexivity.
Qed.

Instance tensor_one : One (tensor_algebra U V) := {
    one := scalar_to_tensor 1
}.

Program Instance tensor_mult_lid : MultLid (tensor_algebra U V).
Next Obligation.
    unfold one; cbn.
    rewrite scalar_to_tensor_scalar.
    apply scalar_id.
Qed.

Program Instance tensor_mult_rid : MultRid (tensor_algebra U V).
Next Obligation.
    unfold one; cbn.
    rewrite <- scalar_to_tensor_comm.
    rewrite scalar_to_tensor_scalar.
    apply scalar_id.
Qed.
(* begin hide *)
End TensorAlgebra.
(* end hide *)
