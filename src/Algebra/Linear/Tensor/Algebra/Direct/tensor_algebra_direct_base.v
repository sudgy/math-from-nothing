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

Context {F : CRingObj} (V : ModuleObj F).
Let U := cring_U F.
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Let VP := module_plus V.
Let VZ := module_zero V.
Let VN := module_neg V.
Let VPA := module_plus_assoc V.
Let VPC := module_plus_comm V.
Let VPZ := module_plus_lid V.
Let VPN := module_plus_linv V.
Let VSM := module_scalar V.
Let VSMO := module_scalar_id V.
Let VSML := module_scalar_ldist V.
Let VSMR := module_scalar_rdist V.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP VZ VN VPA
    VPC VPZ VPN VSM VSMO VSML VSMR.

Let FR_module := free_linear F (list (module_V V)).
Let FR := module_V FR_module.
Let to_FR a := to_free F (list (module_V V)) a.

Let FR_plus := module_plus FR_module.
Let FR_zero := module_zero FR_module.
Let FR_neg := module_neg FR_module.
Let FR_plus_comm := module_plus_comm FR_module.
Let FR_plus_assoc := module_plus_assoc FR_module.
Let FR_plus_lid := module_plus_lid FR_module.
Let FR_plus_linv := module_plus_linv FR_module.
Let FR_scalar := module_scalar FR_module.
Let FR_scalar_id := module_scalar_id FR_module.
Let FR_scalar_ldist := module_scalar_ldist FR_module.
Let FR_scalar_rdist := module_scalar_rdist FR_module.
Let FR_scalar_comp := module_scalar_comp FR_module.
Let FR_grade := free_grade F (list (module_V V)).
Existing Instances FR_plus FR_zero FR_neg FR_plus_comm FR_plus_assoc FR_plus_lid
    FR_plus_linv FR_scalar FR_scalar_id FR_scalar_ldist FR_scalar_rdist
    FR_scalar_comp FR_grade.

Local Instance FR_mult : Mult FR := {
    mult := free_bilinear F (list (module_V V)) (λ a b, to_FR (a ++ b))
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
    induction a as [|a' v a aa av IHa] using grade_induction.
    {
        do 3 rewrite mult_lanni.
        reflexivity.
    }
    do 3 rewrite rdist.
    rewrite IHa.
    apply rplus.
    apply to_free_ex in aa as [α a_eq]; subst a'.
    do 3 rewrite scalar_lmult.
    apply f_equal.
    clear v α av IHa.
    induction b as [|b' v b bb bv IHb] using grade_induction.
    {
        rewrite mult_lanni.
        rewrite mult_ranni.
        rewrite mult_lanni.
        reflexivity.
    }
    rewrite rdist.
    do 2 rewrite ldist.
    rewrite rdist.
    rewrite IHb.
    apply rplus.
    apply to_free_ex in bb as [β b_eq]; subst b'.
    rewrite scalar_lmult.
    do 2 rewrite scalar_rmult.
    rewrite scalar_lmult.
    apply f_equal.
    clear v β bv IHb.
    induction c as [|c' v c cc cv IHc] using grade_induction.
    {
        do 3 rewrite mult_ranni.
        reflexivity.
    }
    do 3 rewrite ldist.
    rewrite IHc.
    apply rplus.
    apply to_free_ex in cc as [γ c_eq]; subst c'.
    do 3 rewrite scalar_rmult.
    apply f_equal.
    clear v γ cv IHc.
    unfold mult; cbn.
    do 4 rewrite (free_bilinear_free F (list (module_V V))).
    rewrite list_conc_assoc.
    reflexivity.
Qed.
Local Instance FR_one : One FR := {
    one := to_FR []
}.
Local Instance FR_mult_lid : MultLid FR.
Proof.
    split.
    intros a.
    induction a as [|a' v a aa av IHa] using grade_induction.
    {
        apply mult_ranni.
    }
    rewrite ldist.
    rewrite IHa.
    apply rplus.
    apply to_free_ex in aa as [α a_eq]; subst a'.
    rewrite scalar_rmult.
    apply f_equal.
    clear v α av IHa.
    unfold one, mult; cbn.
    rewrite (free_bilinear_free F (list (module_V V))).
    rewrite list_conc_lid.
    reflexivity.
Qed.
Local Instance FR_mult_rid : MultRid FR.
Proof.
    split.
    intros a.
    induction a as [|a' v a aa av IHa] using grade_induction.
    {
        apply mult_lanni.
    }
    rewrite rdist.
    rewrite IHa.
    apply rplus.
    apply to_free_ex in aa as [α a_eq]; subst a'.
    rewrite scalar_lmult.
    apply f_equal.
    clear v α av IHa.
    unfold one, mult; cbn.
    rewrite (free_bilinear_free F (list (module_V V))).
    rewrite list_conc_rid.
    reflexivity.
Qed.

Definition tensor_ideal_base (x : FR) :=
    (∃ a b, x = to_FR [a + b] - to_FR [a] - to_FR [b]) ∨
    (∃ α b, x = to_FR [α · b] - α · to_FR [b]).

Definition tensor_ideal := ideal_generated_by tensor_ideal_base.

Definition tensor_algebra_base := quotient_ring tensor_ideal.
Definition tensor_algebra_plus := quotient_ring_plus tensor_ideal.
Definition tensor_algebra_plus_assoc := quotient_ring_plus_assoc tensor_ideal.
Definition tensor_algebra_plus_comm := quotient_ring_plus_comm tensor_ideal.
Definition tensor_algebra_zero := quotient_ring_zero tensor_ideal.
Definition tensor_algebra_plus_lid := quotient_ring_plus_lid tensor_ideal.
Definition tensor_algebra_neg := quotient_ring_neg tensor_ideal.
Definition tensor_algebra_plus_linv := quotient_ring_plus_linv tensor_ideal.
Definition tensor_mult_class := quotient_ring_mult tensor_ideal.
Definition tensor_mult_ldist := quotient_ring_ldist tensor_ideal.
Definition tensor_mult_rdist := quotient_ring_rdist tensor_ideal.
Definition tensor_mult_assoc := quotient_ring_mult_assoc tensor_ideal.
Definition tensor_one := quotient_ring_one tensor_ideal.
Definition tensor_mult_lid := quotient_ring_mult_lid tensor_ideal.
Definition tensor_mult_rid := quotient_ring_mult_rid tensor_ideal.
Existing Instances tensor_algebra_plus tensor_algebra_plus_assoc
    tensor_algebra_plus_comm tensor_algebra_zero tensor_algebra_plus_lid
    tensor_algebra_neg tensor_algebra_plus_linv tensor_mult_class
    tensor_mult_ldist tensor_mult_rdist tensor_mult_assoc tensor_one
    tensor_mult_lid tensor_mult_rid.

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
    unfold plus, scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_ldist.
Qed.
Local Instance tensor_algebra_scalar_rdist : ScalarRdist U tensor_algebra_base.
Proof.
    split.
    intros a b v.
    equiv_get_value v.
    unfold scalar_mult, plus at 2; equiv_simpl.
    apply f_equal.
    apply scalar_rdist.
Qed.
Local Instance tensor_scalar_lmult : ScalarLMult U tensor_algebra_base.
Proof.
    split.
    intros a u v.
    equiv_get_value u v.
    unfold mult, scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_lmult.
Qed.
Local Instance tensor_scalar_rmult : ScalarRMult U tensor_algebra_base.
Proof.
    split.
    intros a u v.
    equiv_get_value u v.
    unfold mult, scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_rmult.
Qed.

Definition vector_to_tensor v := to_qring tensor_ideal (to_FR [v]).

Theorem vector_to_tensor_plus : ∀ u v,
    vector_to_tensor (u + v) = vector_to_tensor u + vector_to_tensor v.
Proof.
    intros a b.
    unfold vector_to_tensor.
    unfold plus at 2; cbn.
    unfold to_qring; equiv_simpl.
    unfold ideal_generated_by_set.
    assert (tensor_ideal_base (to_FR [a + b] - to_FR [a] - to_FR [b])) as ab_in.
    {
        left.
        exists a, b.
        reflexivity.
    }
    exists (((1, 1), [_|ab_in]) ::: ulist_end).
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
    unfold to_qring; equiv_simpl.
    unfold ideal_generated_by_set.
    assert (tensor_ideal_base (to_FR [α · v] - α · to_FR [v])) as v_in.
    {
        right.
        exists α, v.
        reflexivity.
    }
    exists (((1, 1), [_|v_in]) ::: ulist_end).
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
        (tensor_algebra_plus V)
        (tensor_algebra_zero V)
        (tensor_algebra_neg V)
        (tensor_algebra_plus_assoc V)
        (tensor_algebra_plus_comm V)
        (tensor_algebra_plus_lid V)
        (tensor_algebra_plus_linv V)
        (tensor_algebra_scalar_mult V)
        (tensor_algebra_scalar_id V)
        (tensor_algebra_scalar_ldist V)
        (tensor_algebra_scalar_rdist V)
        (tensor_algebra_scalar_comp V)
    )
    (tensor_mult_class V)
    (tensor_mult_ldist V)
    (tensor_mult_rdist V)
    (tensor_mult_assoc V)
    (tensor_one V)
    (tensor_mult_lid V)
    (tensor_mult_rid V)
    (tensor_scalar_lmult V)
    (tensor_scalar_rmult V)
.
