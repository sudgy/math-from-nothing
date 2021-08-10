(*
Require Import init.

Require Export geometric_construction3.

Require Import plus_sum.
Require Import mult_ring.
Require Import set.
Require Import list.
Require Import linear_span.
Require Import linear_subspace.

Section GA4.

Context {V : Type}.
Variable metric : ga_metric V.

Context U `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @MultComm U UM,
    @MultLid U UM UO,
    @Ldist U UP UM,
    @NotTrivial U UZ UO
}.

Definition ga13' := ga13 metric U.
Definition ga3_plus' := ga3_plus metric U.
Definition ga3_zero' := ga3_zero metric U.
Definition ga3_neg' := ga3_neg metric U.
Definition ga3_plus_comm' := ga3_plus_comm metric U.
Definition ga3_plus_assoc' := ga3_plus_assoc metric U.
Definition ga3_plus_lid' := ga3_plus_lid metric U.
Definition ga3_plus_linv' := ga3_plus_linv metric U.
Definition ga3_scalar' := ga3_scalar metric U.
Definition ga3_scalar_ldist' := ga3_scalar_ldist metric U.
Definition ga3_scalar_rdist' := ga3_scalar_rdist metric U.
Existing Instances ga3_plus' ga3_zero' ga3_neg' ga3_plus_comm' ga3_plus_assoc'
    ga3_plus_lid' ga3_plus_linv' ga3_scalar' ga3_scalar_ldist'
    ga3_scalar_rdist'.

Let sub1 v := ∃ l, v = ga13' (ga_pos, l) + ga13' (ga_neg, l).
Let sub2 v := ∃ l, v = ga13' (ga_null, l).
Let sub := sub1 ∪ sub2.

Definition ga := linear_span_quotient U sub.
Definition ga34 b := to_quotient U sub b.
Definition ga24 b := ga34 (ga23 metric U b).
Definition ga14 b := ga34 (ga13 metric U b).

Definition ga_plus_class
    := quotient_space_plus (linear_span_subspace U sub).
Definition ga_plus_assoc_class
    := quotient_space_plus_assoc (linear_span_subspace U sub).
Definition ga_plus_comm_class
    := quotient_space_plus_comm (linear_span_subspace U sub).
Definition ga_zero_class
    := quotient_space_zero (linear_span_subspace U sub).
Definition ga_plus_lid_class
    := quotient_space_plus_lid (linear_span_subspace U sub).
Definition ga_neg_class
    := quotient_space_neg (linear_span_subspace U sub).
Definition ga_plus_linv_class
    := quotient_space_plus_linv (linear_span_subspace U sub).
Definition ga_scalar_class
    := quotient_space_scalar_mult (linear_span_subspace U sub).
Definition ga_scalar_ldist_class
    := quotient_space_scalar_ldist (linear_span_subspace U sub).
Definition ga_scalar_rdist_class
    := quotient_space_scalar_rdist (linear_span_subspace U sub).
Existing Instances ga_plus_class ga_plus_assoc_class ga_plus_comm_class
    ga_zero_class ga_plus_lid_class ga_neg_class ga_plus_linv_class
    ga_scalar_class ga_scalar_ldist_class ga_scalar_rdist_class.

Definition ga_basis_scale x := ∃ α b, x = α · ga14 (ga_pos, b).

Lemma ga_free_basis_to_basis :
        ∀ x, ga3_basis_scale metric U x → ga_basis_scale (ga34 x).
    intros x [α [b x_eq]].
    equiv_get_value b.
    destruct b as [b_sign b].
    destruct b_sign.
    -   exists α, b.
        rewrite x_eq.
        unfold scalar_mult at 2; cbn.
        unfold ga14, ga34; cbn.
        unfold to_quotient.
        equiv_simpl.
        rewrite plus_rinv.
        intros S sub_S.
        apply subspace_zero.
    -   exists (-α), b.
        rewrite x_eq.
        unfold ga14, ga34, to_quotient.
        unfold scalar_mult at 2; cbn.
        equiv_simpl.
        intros S sub_S.
        rewrite scalar_lneg.
        rewrite neg_neg.
        rewrite <- scalar_ldist.
        apply subspace_scalar.
        apply sub_S.
        left.
        exists b.
        apply plus_comm.
    -   exists 0, b.
        rewrite scalar_lanni.
        rewrite x_eq.
        unfold ga34, to_quotient, zero.
        equiv_simpl.
        rewrite neg_zero, plus_rid.
        intros S sub_S.
        apply subspace_scalar.
        apply sub_S.
        right.
        exists b.
        reflexivity.
Qed.

Theorem ga_decompose_basis : ∀ a : ga, ∃ l : list (set_type ga_basis_scale),
        a = list_sum (list_image l (λ x, [x|])).
    intros a.
    equiv_get_value a.
    pose proof (ga3_decompose_basis metric U a) as [l a_eq].
    subst a.
    induction l.
    -   exists list_end.
        cbn.
        reflexivity.
    -   destruct IHl as [l' l'_eq].
        destruct a as [a a_basis]; cbn in *.
        apply ga_free_basis_to_basis in a_basis.
        exists ([_|a_basis] :: l').
        cbn.
        rewrite <- l'_eq.
        unfold plus at 2, ga34, to_quotient; equiv_simpl.
        reflexivity.
Qed.

Definition ga_mult_base (a b : set_type ga_basis_scale) :=
    (ex_val [|a] * ex_val [|b]) ·
    ga24 (ga2_mult metric (ga12 metric (ga_pos, ex_val (ex_proof [|a])))
                          (ga12 metric (ga_pos, ex_val (ex_proof [|b])))).
Instance ga_mult : Mult ga := {
    mult a b := list_sum (list_prod2 ga_mult_base
        (ex_val (ga_decompose_basis a))
        (ex_val (ga_decompose_basis b)))
}.
(*
    (*
Lemma ga_mult_base_basis : ∀ a b, ga_basis_scale (ga_mult_base a b).
Admitted.
*)
(*
Lemma ga_mult_list1 : ∀ al bl,
        list_sum (list_image al (λ x : set_type ga_basis_scale, [x | ])) *
        list_sum (list_image bl (λ x : set_type ga_basis_scale, [x | ]))
        = list_sum (list_prod2 ga_mult_base al bl).
    intros al bl.
    unfold mult; cbn.
    old_unpack_ex_val al' al_eq.
    old_unpack_ex_val bl' bl_eq.
Admitted.
*)
(*
        *)
Lemma ga_ldist : ∀ a b c, a * (b + c) = a * b + a * c.
    intros a b c.

    unfold mult; cbn.
    unfold ex_val at 1 3 4 5 6.
    destruct (ex_to_type _) as [al a_eq]; cbn.
    destruct (ex_to_type _) as [bl b_eq]; cbn.
    destruct (ex_to_type _) as [cl c_eq]; cbn.
    rewrite <- list_sum_plus.
    subst.
    rewrite <- list_sum_plus.
    rewrite <- list_image_conc.

    induction bl.
    -   cbn.


    pose proof (ga_decompose_basis a) as [al a_eq].
    pose proof (ga_decompose_basis b) as [bl b_eq].
    pose proof (ga_decompose_basis c) as [cl c_eq].
    subst.
    rewrite <- list_sum_plus.
    rewrite <- list_image_conc.
    (*
    repeat rewrite ga_mult_list1.
    rewrite <- list_sum_plus.
    induction bl.
    -   cbn.
        reflexivity.
    -   cbn.
        repeat rewrite list_sum_plus.
        rewrite IHbl.
        rewrite list_sum_plus.
        rewrite plus_assoc.
        reflexivity.
        *)
Qed.
(*
Theorem ga_mult_list : ∀ al bl,
        (list_sum al) * (list_sum bl) = list_sum (list_prod2 mult al bl).
    intros al bl.
Admitted.
*)

Lemma ga_mult_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
    intros a b c.
    pose proof (ga_decompose_basis a) as [al a_eq].
    pose proof (ga_decompose_basis b) as [bl b_eq].
    pose proof (ga_decompose_basis c) as [cl c_eq].
    subst.
    repeat rewrite ga_mult_list2.

    revert al bl.
    induction cl.
    -   intros.
        cbn.
        reflexivity.
    -   intros al bl.
        cbn in *.
    *)

End GA4.
    *)
