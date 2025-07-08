Require Import init.

Require Import algebra_category.
Require Import linear_free.
Require Import linear_extend.
Require Import ring_ideal.
Require Import linear_span.
Require Import linear_combination.

Require Export nat.
Require Export list.
Require Import unordered_list.
Require Import equivalence.

Section TensorAlgebra.

Context {U : CRingObj} (V : ModuleObj U).

Let FR := free_linear U (list (module_V V)).
Let to_FR a : FR := to_free U (list (module_V V)) a.

Let FR_grade := free_grade U (list (module_V V)).
Local Existing Instance FR_grade.

Local Instance FR_mult : Mult FR := {
    mult := free_bilinear U (list (module_V V)) (λ a b, to_FR (a + b))
}.
Local Instance FR_ldist : Ldist FR := {
    ldist := free_bilinear_ldist _ _ _
}.
Local Instance FR_rdist : Rdist FR := {
    rdist := free_bilinear_rdist _ _ _
}.
Local Instance FR_lscalar : ScalarLMult U FR := {
    scalar_lmult := free_bilinear_lscalar _ _ _
}.
Local Instance FR_rscalar : ScalarRMult U FR := {
    scalar_rmult := free_bilinear_rscalar _ _ _
}.
Local Instance FR_mult_assoc : MultAssoc FR.
Proof.
    split.
    intros a b c.
    induction a as [|a' v] using grade_induction.
    {
        do 3 rewrite mult_lanni.
        reflexivity.
    }
    do 3 rewrite rdist.
    rewrite IHv.
    apply rplus.
    destruct a' as [a' [a aa]]; cbn.
    apply to_free_ex in aa as [α a_eq]; subst a'.
    do 3 rewrite scalar_lmult.
    apply f_equal.
    clear v α IHv.
    induction b as [|b' v] using grade_induction.
    {
        rewrite (mult_lanni c).
        rewrite (mult_ranni (U := FR)).
        rewrite (mult_lanni c).
        reflexivity.
    }
    rewrite rdist.
    do 2 rewrite ldist.
    rewrite rdist.
    rewrite IHv.
    apply rplus.
    destruct b' as [b' [b bb]]; cbn.
    apply to_free_ex in bb as [β b_eq]; subst b'.
    rewrite scalar_lmult.
    do 2 rewrite scalar_rmult.
    rewrite scalar_lmult.
    apply f_equal.
    clear v β IHv.
    induction c as [|c' v] using grade_induction.
    {
        do 3 rewrite (mult_ranni (U := FR)).
        reflexivity.
    }
    do 3 rewrite ldist.
    rewrite IHv.
    apply rplus.
    destruct c' as [c' [c cc]]; cbn.
    apply to_free_ex in cc as [γ c_eq]; subst c'.
    do 3 rewrite scalar_rmult.
    apply f_equal.
    clear v γ IHv.
    unfold mult; cbn.
    do 4 rewrite (free_bilinear_free U (list (module_V V))).
    rewrite plus_assoc.
    reflexivity.
Qed.
Local Instance FR_one : One FR := {
    one := to_FR []
}.
Local Instance FR_mult_lid : MultLid FR.
Proof.
    split.
    intros a.
    induction a as [|a' v] using grade_induction.
    {
        apply mult_ranni.
    }
    rewrite ldist.
    rewrite IHv.
    apply rplus.
    destruct a' as [a' [a aa]]; cbn.
    apply to_free_ex in aa as [α a_eq]; subst a'.
    rewrite scalar_rmult.
    apply f_equal.
    clear v α IHv.
    unfold one, mult; cbn.
    rewrite (free_bilinear_free U (list (module_V V))).
    rewrite list_conc_lid.
    reflexivity.
Qed.
Local Instance FR_mult_rid : MultRid FR.
Proof.
    split.
    intros a.
    induction a as [|a' v] using grade_induction.
    {
        apply mult_lanni.
    }
    rewrite rdist.
    rewrite IHv.
    apply rplus.
    destruct a' as [a' [a aa]]; cbn.
    apply to_free_ex in aa as [α a_eq]; subst a'.
    rewrite scalar_lmult.
    apply f_equal.
    clear v α IHv.
    unfold one, mult; cbn.
    rewrite (free_bilinear_free U (list (module_V V))).
    rewrite list_conc_rid.
    reflexivity.
Qed.

Definition FR_ring : Ring := make_ring FR _ _ _ FR_mult _ _ _ _ FR_mult_assoc
    FR_ldist FR_rdist FR_one FR_mult_lid FR_mult_rid.
Arguments FR_ring : simpl never.

Definition tensor_ideal_base (x : FR_ring) :=
    (∃ a b, x = to_FR [a + b] - to_FR [a] - to_FR [b]) ∨
    (∃ α b, x = to_FR [α · b] - α · to_FR [b]).

Definition tensor_ideal := ideal_generated_by tensor_ideal_base.
Definition tensor_algebra_base := quotient_ring tensor_ideal.

Lemma tensor_scalar_wd : ∀ c u v, eq_equal (ideal_equiv tensor_ideal) u v →
    eq_equal (ideal_equiv tensor_ideal) (c · u) (c · v).
Proof.
    cbn.
    change (ideal_generated_by_set tensor_ideal_base) with (ideal_set tensor_ideal).
    intros c u v eq.
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    rewrite <- (mult_lid (u - v)).
    rewrite <- scalar_lmult.
    apply (ideal_lmult tensor_ideal).
    exact eq.
Qed.

Instance tensor_algebra_scalar_mult : ScalarMult U tensor_algebra_base := {
    scalar_mult c := unary_op (unary_self_wd (tensor_scalar_wd c))
}.
Local Instance tensor_algebra_scalar_comp : ScalarComp U tensor_algebra_base.
Proof.
    split.
    intros a b v.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_comp.
Qed.
Local Instance tensor_algebra_scalar_id : ScalarId U tensor_algebra_base.
Proof.
    split.
    intros v.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_id.
Qed.
Local Instance tensor_algebra_scalar_ldist : ScalarLdist U tensor_algebra_base.
Proof.
    split.
    intros a u v.
    equiv_get_value u v.
    unfold plus, scalar_mult, tensor_algebra_base, quotient_ring; equiv_simpl.
    apply f_equal.
    apply scalar_ldist.
Qed.
Local Instance tensor_algebra_scalar_rdist : ScalarRdist U tensor_algebra_base.
Proof.
    split.
    intros a b v.
    equiv_get_value v.
    unfold scalar_mult, plus at 2, tensor_algebra_base, quotient_ring; equiv_simpl.
    apply f_equal.
    apply scalar_rdist.
Qed.
Local Instance tensor_scalar_lmult : ScalarLMult U tensor_algebra_base.
Proof.
    split.
    intros a u v.
    equiv_get_value u v.
    unfold mult, scalar_mult, tensor_algebra_base, quotient_ring; equiv_simpl.
    apply f_equal.
    apply scalar_lmult.
Qed.
Local Instance tensor_scalar_rmult : ScalarRMult U tensor_algebra_base.
Proof.
    split.
    intros a u v.
    equiv_get_value u v.
    unfold mult, scalar_mult, tensor_algebra_base, quotient_ring; equiv_simpl.
    apply f_equal.
    apply scalar_rmult.
Qed.

Definition vector_to_tensor v := to_qring tensor_ideal (to_FR [v]).

Theorem vector_to_tensor_plus : ∀ u v,
    vector_to_tensor (u + v) = vector_to_tensor u + vector_to_tensor v.
Proof.
    intros a b.
    unfold vector_to_tensor.
    rewrite <- (homo_plus (f := to_qring tensor_ideal)).
    rewrite <- plus_0_anb_a_b.
    rewrite <- homo_neg, <- homo_plus.
    apply to_qring_zero.
    assert (tensor_ideal_base (to_FR [a + b] - to_FR [a] - to_FR [b])) as ab_in.
    {
        left.
        exists a, b.
        reflexivity.
    }
    exists (((1, 1), [_|ab_in]) ː ulist_end).
    rewrite ulist_image_add, ulist_image_end.
    cbn.
    rewrite ulist_sum_add, ulist_sum_end.
    rewrite mult_lid, mult_rid.
    rewrite plus_rid.
    rewrite neg_plus, plus_assoc.
    reflexivity.
Qed.

Theorem vector_to_tensor_scalar : ∀ α v,
    vector_to_tensor (α · v) = α · vector_to_tensor v.
Proof.
    intros α v.
    unfold vector_to_tensor.
    unfold scalar_mult at 2; cbn.
    unfold to_qring, to_qring_type; equiv_simpl.
    apply equiv_eq.
    unfold ideal_generated_by_set.
    assert (tensor_ideal_base (to_FR [α · v] - α · to_FR [v])) as v_in.
    {
        right.
        exists α, v.
        reflexivity.
    }
    exists (((1, 1), [_|v_in]) ː ulist_end).
    rewrite ulist_image_add, ulist_image_end.
    cbn.
    rewrite ulist_sum_add, ulist_sum_end.
    rewrite mult_lid, mult_rid.
    rewrite plus_rid.
    reflexivity.
Qed.

End TensorAlgebra.

Definition tensor_algebra_object {F : CRingObj} (V : ModuleObj F) := make_algebra F
    (make_module F
        (tensor_algebra_base V)
        _
        _
        _
        _
        _
        _
        _
        (tensor_algebra_scalar_mult V)
        (tensor_algebra_scalar_id V)
        (tensor_algebra_scalar_ldist V)
        (tensor_algebra_scalar_rdist V)
        (tensor_algebra_scalar_comp V)
    )
    _
    _
    _
    _
    _
    _
    _
    (tensor_scalar_lmult V)
    (tensor_scalar_rmult V)
.
