Require Import init.

Require Import algebra_category.
Require Import linear_free.
Require Import linear_extend.
Require Import ring_ideal.
Require Import linear_bilinear_form.

Require Export list.
Require Import unordered_list.
Require Import equivalence.

Section GeometricAlgebra.

Context {U : CRingObj} {V : Module U}.
Context (B : set_type (bilinear_form (V := V))).

Let FR := free_linear U (list V).
Let to_FR a : FR:= to_free U (list V) a.

Let FR_grade := free_grade U (list V).
Existing Instances FR_grade.

Local Instance FR_mult : Mult FR := {
    mult := free_bilinear U (list V) (λ a b, to_FR (a + b))
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
    induction a as [|a v] using grade_induction.
    {
        do 3 rewrite mult_lanni.
        reflexivity.
    }
    do 3 rewrite rdist.
    rewrite IHv.
    apply rplus.
    destruct a as [a' [a aa]]; cbn.
    apply to_free_ex in aa as [α a_eq]; subst a'.
    do 3 rewrite scalar_lmult.
    apply f_equal.
    clear v α IHv.
    change (sum_module_type _ _) with (module_V FR).
    induction b as [|b v] using grade_induction.
    {
        rewrite mult_lanni.
        rewrite mult_ranni.
        rewrite mult_lanni.
        reflexivity.
    }
    rewrite rdist.
    do 2 rewrite ldist.
    rewrite rdist.
    rewrite IHv.
    apply rplus.
    destruct b as [b' [b bb]]; cbn.
    apply to_free_ex in bb as [β b_eq]; subst b'.
    rewrite scalar_lmult.
    do 2 rewrite scalar_rmult.
    rewrite scalar_lmult.
    apply f_equal.
    clear v β IHv.
    change (sum_module_type _ _) with (module_V FR).
    induction c as [|c v] using grade_induction.
    {
        do 3 rewrite mult_ranni.
        reflexivity.
    }
    do 3 rewrite ldist.
    rewrite IHv.
    apply rplus.
    destruct c as [c' [c cc]]; cbn.
    apply to_free_ex in cc as [γ c_eq]; subst c'.
    do 3 rewrite scalar_rmult.
    apply f_equal.
    clear v γ IHv.
    unfold mult; cbn.
    do 4 rewrite (free_bilinear_free U (list V)).
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
    induction a as [|a v] using grade_induction.
    {
        apply mult_ranni.
    }
    rewrite ldist.
    rewrite IHv.
    apply rplus.
    destruct a as [a' [a aa]]; cbn.
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
    induction a as [|a v] using grade_induction.
    {
        apply mult_lanni.
    }
    rewrite rdist.
    rewrite IHv.
    apply rplus.
    destruct a as [a' [a aa]]; cbn.
    apply to_free_ex in aa as [α a_eq]; subst a'.
    rewrite scalar_lmult.
    apply f_equal.
    clear v α IHv.
    unfold one, mult; cbn.
    rewrite (free_bilinear_free U (list (module_V V))).
    rewrite list_conc_rid.
    reflexivity.
Qed.

Definition ga_ideal_base (x : FR) :=
    (∃ a b, x = to_FR [a + b] - to_FR [a] - to_FR [b]) ∨
    (∃ α b, x = to_FR [α · b] - α · to_FR [b]) ∨
    (∃ v, x = to_FR [v; v] - [B|] v v · 1).

Definition ga_ideal := ideal_generated_by ga_ideal_base.

Definition geometric_algebra_base := quotient_ring ga_ideal.
Definition geometric_algebra_plus := quotient_ring_plus ga_ideal.
Definition geometric_algebra_plus_assoc := quotient_ring_plus_assoc ga_ideal.
Definition geometric_algebra_plus_comm := quotient_ring_plus_comm ga_ideal.
Definition geometric_algebra_zero := quotient_ring_zero ga_ideal.
Definition geometric_algebra_plus_lid := quotient_ring_plus_lid ga_ideal.
Definition geometric_algebra_neg := quotient_ring_neg ga_ideal.
Definition geometric_algebra_plus_linv := quotient_ring_plus_linv ga_ideal.
Definition geometric_mult_class := quotient_ring_mult ga_ideal.
Definition geometric_mult_ldist := quotient_ring_ldist ga_ideal.
Definition geometric_mult_rdist := quotient_ring_rdist ga_ideal.
Definition geometric_mult_assoc := quotient_ring_mult_assoc ga_ideal.
Definition geometric_one := quotient_ring_one ga_ideal.
Definition geometric_mult_lid := quotient_ring_mult_lid ga_ideal.
Definition geometric_mult_rid := quotient_ring_mult_rid ga_ideal.
Existing Instances geometric_algebra_plus geometric_algebra_plus_assoc
    geometric_algebra_plus_comm geometric_algebra_zero
    geometric_algebra_plus_lid geometric_algebra_neg geometric_algebra_plus_linv
    geometric_mult_class geometric_mult_ldist geometric_mult_rdist
    geometric_mult_assoc geometric_one geometric_mult_lid geometric_mult_rid.

Lemma ga_scalar_wd : ∀ c u v, eq_equal (ideal_equiv ga_ideal) u v →
    eq_equal (ideal_equiv ga_ideal) (c · u) (c · v).
Proof.
    intros c u v.
    cbn.
    change (ideal_generated_by_set ga_ideal_base) with (ideal_set ga_ideal).
    intros eq.
    change (sum_module_type _ _) with (module_V FR).
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    rewrite <- (mult_lid (u - v)).
    rewrite <- scalar_lmult.
    apply (ideal_lmult ga_ideal).
    exact eq.
Qed.

Instance geometric_algebra_scalar_mult : ScalarMult U geometric_algebra_base := {
    scalar_mult c := unary_op (unary_self_wd (ga_scalar_wd c))
}.
Local Instance geometric_algebra_scalar_comp : ScalarComp U geometric_algebra_base.
Proof.
    split.
    intros a b v.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    change (sum_module_type _ _) with (module_V FR).
    apply scalar_comp.
Qed.
Local Instance geometric_algebra_scalar_id : ScalarId U geometric_algebra_base.
Proof.
    split.
    intros v.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    apply f_equal.
    change (sum_module_type _ _) with (module_V FR).
    apply scalar_id.
Qed.
Local Instance geometric_algebra_scalar_ldist : ScalarLdist U geometric_algebra_base.
Proof.
    split.
    intros a u v.
    equiv_get_value u v.
    unfold plus, scalar_mult; equiv_simpl.
    apply f_equal.
    change (sum_module_type _ _) with (module_V FR).
    apply scalar_ldist.
Qed.
Local Instance geometric_algebra_scalar_rdist : ScalarRdist U geometric_algebra_base.
Proof.
    split.
    intros a b v.
    equiv_get_value v.
    unfold scalar_mult, plus at 2; equiv_simpl.
    apply f_equal.
    change (sum_module_type _ _) with (module_V FR).
    apply scalar_rdist.
Qed.
Local Instance geometric_scalar_lmult : ScalarLMult U geometric_algebra_base.
Proof.
    split.
    intros a u v.
    equiv_get_value u v.
    unfold mult, scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_lmult.
Qed.
Local Instance geometric_scalar_rmult : ScalarRMult U geometric_algebra_base.
Proof.
    split.
    intros a u v.
    equiv_get_value u v.
    unfold mult, scalar_mult; equiv_simpl.
    apply f_equal.
    apply scalar_rmult.
Qed.

Definition vector_to_geo v := to_qring ga_ideal (to_FR [v]).

Theorem vector_to_geo_plus : ∀ u v,
    vector_to_geo (u + v) = vector_to_geo u + vector_to_geo v.
Proof.
    intros a b.
    unfold vector_to_geo.
    unfold plus at 2; cbn.
    unfold to_qring; equiv_simpl.
    unfold ideal_generated_by_set.
    assert (ga_ideal_base (to_FR [a + b] - to_FR [a] - to_FR [b])) as ab_in.
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
    change (sum_module_type _ _) with (module_V FR).
    rewrite plus_rid.
    rewrite neg_plus, plus_assoc.
    reflexivity.
Qed.

Theorem vector_to_geo_scalar : ∀ α v,
    vector_to_geo (α · v) = α · vector_to_geo v.
Proof.
    intros α v.
    unfold vector_to_geo.
    unfold scalar_mult at 2; cbn.
    unfold to_qring; equiv_simpl.
    unfold ideal_generated_by_set.
    assert (ga_ideal_base (to_FR [α · v] - α · to_FR [v])) as v_in.
    {
        right; left.
        exists α, v.
        reflexivity.
    }
    exists (((1, 1), [_|v_in]) ː ulist_end).
    rewrite ulist_image_add, ulist_image_end.
    cbn.
    rewrite ulist_sum_add, ulist_sum_end.
    rewrite mult_lid, mult_rid.
    change (sum_module_type _ _) with (module_V FR).
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem geo_contract : ∀ v, vector_to_geo v * vector_to_geo v = [B|] v v · 1.
Proof.
    intros v.
    unfold vector_to_geo.
    unfold mult; cbn.
    unfold scalar_mult; cbn.
    unfold to_qring; equiv_simpl.
    unfold mult; cbn.
    change (sum_module_type _ _) with (module_V FR).
    rewrite (free_bilinear_free U (list V)).
    rewrite list_conc_add, list_conc_lid.
    unfold ideal_generated_by_set.
    assert (ga_ideal_base (to_FR [v; v] - [B|] v v · 1)) as v_in.
    {
        right; right.
        exists v.
        reflexivity.
    }
    exists (((1, 1), [_|v_in]) ː ulist_end).
    rewrite ulist_image_add, ulist_image_end.
    cbn.
    rewrite ulist_sum_add, ulist_sum_end.
    rewrite mult_lid, mult_rid.
    change (sum_module_type _ _) with (module_V FR).
    rewrite plus_rid.
    reflexivity.
Qed.

End GeometricAlgebra.

Definition geometric_algebra_object
    {F : CRingObj} {V : ModuleObj F} (B : set_type (bilinear_form (V := V)))
    := make_algebra F
        (make_module F
            (geometric_algebra_base B)
            (geometric_algebra_plus B)
            (geometric_algebra_zero B)
            (geometric_algebra_neg B)
            (geometric_algebra_plus_assoc B)
            (geometric_algebra_plus_comm B)
            (geometric_algebra_plus_lid B)
            (geometric_algebra_plus_linv B)
            (geometric_algebra_scalar_mult B)
            (geometric_algebra_scalar_id B)
            (geometric_algebra_scalar_ldist B)
            (geometric_algebra_scalar_rdist B)
            (geometric_algebra_scalar_comp B)
        )
        (geometric_mult_class B)
        (geometric_mult_ldist B)
        (geometric_mult_rdist B)
        (geometric_mult_assoc B)
        (geometric_one B)
        (geometric_mult_lid B)
        (geometric_mult_rid B)
        (geometric_scalar_lmult B)
        (geometric_scalar_rmult B)
    .
