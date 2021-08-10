Require Import init.

Require Import list.
Require Import set.
Require Import card.
Require Import linear_free.
Require Import linear_span.
Require Import linear_subspace.
Require Import plus_sum.

Definition ga_mult_base3 (a b : set_type ga_free_basis_scale) :=
    (ex_val [|a] * ex_val [|b]) · to_free U ga_basis_base
        (ga_mult_base2 (ex_val (ex_proof [|a])) (ex_val (ex_proof [|b]))).
Definition ga_mult_base4 (a b : FR) :=
    list_sum (list_prod2 ga_mult_base3 (ex_val (ga_free_decompose_basis a))
                                       (ex_val (ga_free_decompose_basis b))).

Let equiv2 := eq_equal (subspace_equiv (linear_span_subspace U sub)).

(*
Lemma ga_mult_base2_wd : ∀ a b c d, equiv2 a b → equiv2 c d →
        equiv2 (ga_mult_base4 a c) (ga_mult_base4 b d).
    intros a b c d ab cd.
    cbn in ab, cd.
    unfold ga_mult_base4.
    cbn.
    old_unpack_ex_val al al_eq.
    old_unpack_ex_val bl bl_eq.
    old_unpack_ex_val cl cl_eq.
    old_unpack_ex_val dl dl_eq.
    subst a b c d.
    intros S sub_S.
    specialize (ab S sub_S).
    specialize (cd S sub_S).
Admitted.

Instance ga_mult : Mult ga := {
    mult := binary_self_op ga_mult_base2_wd
}.
 *)

End Construct.
