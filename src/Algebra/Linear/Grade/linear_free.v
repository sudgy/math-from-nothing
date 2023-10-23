Require Import init.

Require Export linear_base.
Require Import linear_grade_sum.
Require Import linear_extend.
Require Import linear_transformation_space.
Require Import module_category.
Require Import category_comma.

Require Import set.
Require Import unordered_list.
Require Import category_initterm.

Section LinearFree.

Context (U : CRingObj) (V : Type).

Definition free_linear := sum_module V (λ _, cring_module U).
Definition free_grade := sum_module_grade V (λ _, cring_module U).
Existing Instances free_grade.

Definition to_free v := single_to_sum_module V (λ _, cring_module U) (k := v) 1
    : free_linear.

Theorem to_free_ex : ∀ (v : V) (x : free_linear),
    of_grade v x → ∃ α, x = α · to_free v.
Proof.
    intros v x vx.
    apply of_grade_ex in vx as [α x_eq].
    subst x.
    exists α.
    unfold to_free.
    apply set_type_eq.
    apply functional_ext; intros i.
    unfold scalar_mult; cbn.
    unfold grade_from; cbn.
    unfold single_to_sum_module_base.
    destruct (sem (v = i)) as [eq|neq]; cbn.
    -   destruct eq; cbn.
        unfold scalar_mult; cbn.
        rewrite mult_rid.
        reflexivity.
    -   unfold scalar_mult; cbn.
        rewrite mult_ranni.
        reflexivity.
Qed.

Section FreeExtend.

Context {V2 : Module U}.

Variable f_base : V → V2.
Let f1 (i : V) (v : grade_modules i) := v · f_base i.

Lemma free_extend_plus_base : ∀ i u v, f1 i (u + v) = f1 i u + f1 i v.
Proof.
    intros u v i.
    unfold f1.
    rewrite <- scalar_rdist.
    reflexivity.
Qed.
Lemma free_extend_scalar_base : ∀ i a v, f1 i (a · v) = a · f1 i v.
Proof.
    intros a v i.
    unfold f1.
    rewrite scalar_comp.
    reflexivity.
Qed.

Let f2 (i : V) := make_module_homomorphism _ _ _ _
    (free_extend_plus_base i) (free_extend_scalar_base i).

Definition free_extend := linear_extend f2 : ModuleObjHomomorphism free_linear V2.
Let f := free_extend.

Theorem free_extend_free : ∀ v : V, f (to_free v) = f_base v.
Proof.
    intros v.
    unfold f, free_extend.
    assert (of_grade v (to_free v)) as v_grade.
    {
        apply of_grade_ex.
        exists 1.
        unfold to_free.
        reflexivity.
    }
    rewrite (linear_extend_homo _ _ _ v_grade).
    unfold f2; cbn.
    unfold f1.
    unfold grade_to; cbn.
    unfold single_to_sum_module_base; cbn.
    destruct (sem (v = v)) as [eq|neq]; [>|contradiction].
    destruct eq; cbn.
    apply scalar_id.
Qed.

End FreeExtend.
Section FreeBilinear.

Context {V2 : Module U}.

Variable op : V → V → V2.

Let lf_module := make_module U _
    (linear_func_plus V V2)
    (linear_func_zero V V2)
    (linear_func_neg V V2)
    (linear_func_plus_assoc V V2)
    (linear_func_plus_comm V V2)
    (linear_func_plus_lid V V2)
    (linear_func_plus_linv V V2)
    (linear_func_scalar V V2)
    (linear_func_scalar_id V V2)
    (linear_func_scalar_ldist V V2)
    (linear_func_scalar_rdist V V2)
    (linear_func_scalar_comp V V2).

Definition free_bilinear_base := free_extend (op : V → lf_module).
Definition free_bilinear (v : free_linear) := free_extend (free_bilinear_base v).
Let f := free_bilinear.

Theorem free_bilinear_ldist : ∀ a b c, f a (b + c) = f a b + f a c.
Proof.
    intros a b c.
    unfold f.
    unfold free_bilinear.
    apply module_homo_plus.
Qed.

Theorem free_bilinear_rdist : ∀ a b c, f (a + b) c = f a c + f b c.
Proof.
    intros a b c.
    unfold f, free_bilinear, free_bilinear_base.
    rewrite module_homo_plus.
    induction c as [|v c IHc] using grade_induction.
    {
        do 3 rewrite module_homo_zero.
        rewrite plus_lid.
        reflexivity.
    }
    do 3 rewrite module_homo_plus.
    rewrite IHc.
    destruct v as [v [i iv]]; cbn.
    do 3 rewrite (linear_extend_homo _ _ _ iv); cbn.
    rewrite scalar_ldist.
    apply plus_4.
Qed.

Theorem free_bilinear_lscalar : ∀ a u v, f (a · u) v = a · f u v.
Proof.
    intros a u v.
    unfold f, free_bilinear, free_bilinear_base.
    rewrite module_homo_scalar.
    induction v as [|x v IHv] using grade_induction.
    {
        do 2 rewrite module_homo_zero.
        rewrite scalar_ranni.
        reflexivity.
    }
    do 2 rewrite module_homo_plus.
    rewrite IHv.
    rewrite scalar_ldist.
    destruct x as [x [i ix]]; cbn.
    do 2 rewrite (linear_extend_homo _ _ _ ix); cbn.
    do 2 rewrite scalar_comp.
    rewrite mult_comm.
    reflexivity.
Qed.

Theorem free_bilinear_rscalar : ∀ a u v, f u (a · v) = a · f u v.
Proof.
    intros a u v.
    unfold f, free_bilinear, free_bilinear_base.
    apply module_homo_scalar.
Qed.

Theorem free_bilinear_lanni : ∀ v, f 0 v = 0.
Proof.
    intros v.
    apply plus_lcancel with (f 0 v).
    rewrite <- free_bilinear_rdist.
    do 2 rewrite plus_rid.
    reflexivity.
Qed.

Theorem free_bilinear_ranni : ∀ v, f v 0 = 0.
Proof.
    intros v.
    apply plus_lcancel with (f v 0).
    rewrite <- free_bilinear_ldist.
    do 2 rewrite plus_rid.
    reflexivity.
Qed.

Theorem free_bilinear_lneg : ∀ u v, f (-u) v = -f u v.
Proof.
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite free_bilinear_lscalar.
    apply scalar_neg_one.
Qed.

Theorem free_bilinear_rneg : ∀ u v, f u (-v) = -f u v.
Proof.
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite free_bilinear_rscalar.
    apply scalar_neg_one.
Qed.

Theorem free_bilinear_free : ∀ u v : V, f (to_free u) (to_free v) = op u v.
Proof.
    intros u v.
    unfold f, free_bilinear, free_bilinear_base.
    do 2 rewrite free_extend_free.
    reflexivity.
Qed.

End FreeBilinear.

Definition to_free_from := make_comma_l1 (V : TYPE) (module_to_type U)
    free_linear to_free.

Theorem free_module_universal : initial to_free_from.
Proof.
    intros [s gM g].
    cbn in *.
    unfold comma_set; cbn.
    clear s.
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        exists (Single, free_extend g).
        cbn.
        functional_intros x.
        apply free_extend_free.
    -   intros [[s1 f1] f1_in'] [[s2 f2] f2_in'].
        cbn in *.
        apply set_type_eq; cbn.
        apply prod_combine; [>apply singleton_type_eq|]; cbn.
        clear s1 s2.
        pose proof (func_eq _ _ f1_in') as f1_in.
        pose proof (func_eq _ _ f2_in') as f2_in.
        clear f1_in' f2_in'.
        cbn in *.
        apply module_homomorphism_eq.
        intros v.
        induction v as [|a v IHv] using grade_induction.
        {
            do 2 rewrite module_homo_zero.
            reflexivity.
        }
        do 2 rewrite module_homo_plus.
        rewrite IHv.
        apply rplus.
        destruct a as [a [i ia]]; cbn.
        apply to_free_ex in ia as [α v_eq]; subst a.
        do 2 rewrite module_homo_scalar.
        rewrite f1_in, f2_in.
        reflexivity.
Qed.

End LinearFree.
