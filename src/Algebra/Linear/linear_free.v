Require Import init.

Require Export linear_base.
Require Import linear_basis.
Require Import linear_span.
Require Import linear_grade_sum.
Require Import linear_extend.
Require Import set.
Require Import card.
Require Import unordered_list.
Require Import plus_sum.

Require Import module_category.
Require Import category_initterm.

(* begin hide *)
Section LinearFree.

Context (F : CRing) (V : Type).
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
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD.

(* end hide *)
Definition free_linear := grade_sum V (λ _, cring_module F).
Definition free_plus_class := grade_sum_plus V (λ _, cring_module F).
Definition free_zero := grade_sum_zero V (λ _, cring_module F).
Definition free_neg := grade_sum_neg V (λ _, cring_module F).
Definition free_plus_assoc_class := grade_sum_plus_assoc V (λ _, cring_module F).
Definition free_plus_comm_class := grade_sum_plus_comm V (λ _, cring_module F).
Definition free_plus_lid_class := grade_sum_plus_lid V (λ _, cring_module F).
Definition free_plus_linv_class := grade_sum_plus_linv V (λ _, cring_module F).
Definition free_scalar := grade_sum_scalar_mult V (λ _, cring_module F).
Definition free_scalar_id_class := grade_sum_scalar_id V (λ _, cring_module F).
Definition free_scalar_ldist_class := grade_sum_scalar_ldist V (λ _, cring_module F).
Definition free_scalar_rdist_class := grade_sum_scalar_rdist V (λ _, cring_module F).
Definition free_scalar_comp_class := grade_sum_scalar_comp V (λ _, cring_module F).
Definition free_grade := grade_sum_grade V (λ _, cring_module F).

Existing Instances free_plus_class free_zero free_neg free_plus_assoc_class
    free_plus_comm_class free_plus_lid_class free_plus_linv_class free_scalar
    free_scalar_id_class free_scalar_ldist_class free_scalar_rdist_class
    free_scalar_comp_class free_grade.

Definition to_free v := single_to_grade_sum V (λ _, cring_module F) (k := v) 1.

Definition free_module := make_module
    F
    free_linear
    free_plus_class
    free_zero
    free_neg
    free_plus_assoc_class
    free_plus_comm_class
    free_plus_lid_class
    free_plus_linv_class
    free_scalar
    free_scalar_id_class
    free_scalar_ldist_class
    free_scalar_rdist_class
    free_scalar_comp_class
.

Record free_from := make_free_from {
    free_from_module : Module F;
    free_from_f : V → module_V free_from_module;
}.

Definition free_from_set (f g : free_from)
    (h : cat_morphism (MODULE F)
                      (free_from_module f)
                      (free_from_module g))
    := ∀ x, module_homo_f h (free_from_f f x) = free_from_f g x.

Definition free_from_compose {F G H : free_from}
    (f : set_type (free_from_set G H)) (g : set_type (free_from_set F G))
    := [f|] ∘ [g|].

Lemma free_from_set_compose_in
        {F' G H : free_from} : ∀ (f : set_type (free_from_set G H)) g,
        free_from_set F' H (free_from_compose f g).
    intros [f f_eq] [g g_eq].
    unfold free_from_set in *.
    unfold free_from_compose; cbn.
    intros x.
    rewrite g_eq.
    apply f_eq.
Qed.

Lemma free_from_set_id_in : ∀ f : free_from, free_from_set f f 𝟙.
    intros f.
    unfold free_from_set.
    intros x.
    cbn.
    reflexivity.
Qed.

Program Instance FREE_FROM : Category := {
    cat_U := free_from;
    cat_morphism f g := set_type (free_from_set f g);
    cat_compose {F G H} f g := [_|free_from_set_compose_in f g];
    cat_id f := [_|free_from_set_id_in f];
}.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_assoc (MODULE F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_lid (MODULE F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_rid (MODULE F)).
Qed.

Definition to_free_from := make_free_from free_module to_free.

Theorem free_module_universal : initial to_free_from.
    intros [gM g].
    pose (gP := module_plus gM).
    pose (gZ := module_zero gM).
    pose (gN := module_neg gM).
    pose (gPC := module_plus_comm gM).
    pose (gPA := module_plus_assoc gM).
    pose (gPZ := module_plus_lid gM).
    pose (gPN := module_plus_linv gM).
    pose (gSM := module_scalar gM).
    pose (gSMO := module_scalar_id gM).
    pose (gSML := module_scalar_ldist gM).
    pose (gSMR := module_scalar_rdist gM).
    pose (gSMC := module_scalar_comp gM).
    cbn.
    apply card_unique_one.
    -   apply ex_set_type.
        pose (f1 (i : V) (v : free_linear) (H : of_grade i v) := ex_val H · g i).
        assert (linear_extend_plus_base f1) as f1_plus.
        {
            intros u v i iu iv.
            unfold f1.
            rewrite_ex_val a a_eq.
            rewrite_ex_val b b_eq.
            rewrite_ex_val c c_eq.
            rewrite <- scalar_rdist.
            apply rscalar.
            rewrite <- b_eq, <- c_eq in a_eq.
            rewrite <- single_to_grade_sum_plus in a_eq.
            apply single_to_grade_sum_eq in a_eq.
            exact a_eq.
        }
        assert (linear_extend_scalar_base f1) as f1_scalar.
        {
            intros a v i iv.
            unfold f1.
            rewrite_ex_val b b_eq.
            rewrite_ex_val c c_eq.
            rewrite scalar_comp.
            apply rscalar.
            rewrite <- c_eq in b_eq.
            rewrite <- single_to_grade_sum_scalar in b_eq.
            apply single_to_grade_sum_eq in b_eq.
            exact b_eq.
        }
        pose (f := linear_extend f1 : free_linear → module_V gM).
        assert (∀ u v, f (u + v) = f u + f v) as f_plus.
        {
            apply linear_extend_plus; assumption.
        }
        assert (∀ a v, f (a · v) = a · f v) as f_scalar.
        {
            apply linear_extend_scalar; assumption.
        }
        exists (make_module_homomorphism _ free_module _ f f_plus f_scalar).
        unfold free_from_set; cbn.
        intros x.
        assert (of_grade x (to_free x)) as x_grade.
        {
            exists 1.
            unfold to_free.
            reflexivity.
        }
        unfold f.
        rewrite (linear_extend_homo (VG := free_grade)
            f1 f1_scalar x (to_free x) x_grade).
        unfold f1.
        rewrite_ex_val a aH.
        unfold to_free in aH.
        apply single_to_grade_sum_eq in aH.
        rewrite aH.
        apply scalar_id.
    -   intros [f1 f1_in] [f2 f2_in].
        pose (f1_plus := @module_homo_plus _ _ _ f1).
        pose (f1_scalar := @module_homo_scalar _ _ _ f1).
        pose (f2_plus := @module_homo_plus _ _ _ f2).
        pose (f2_scalar := @module_homo_scalar _ _ _ f2).
        apply set_type_eq; cbn.
        apply module_homomorphism_eq.
        cbn.
        intros v.
        unfold free_from_set in f1_in; cbn in f1_in.
        unfold free_from_set in f2_in; cbn in f2_in.
        pose proof (grade_decomposition_eq v) as v_eq.
        rewrite v_eq; clear v_eq.
        remember (grade_decomposition v) as l.
        clear Heql.
        induction l using ulist_induction.
        +   rewrite ulist_image_end, ulist_sum_end.
            do 2 rewrite module_homo_zero.
            reflexivity.
        +   rewrite ulist_image_add, ulist_sum_add.
            rewrite f1_plus, f2_plus.
            rewrite IHl.
            apply rplus.
            clear v l IHl.
            destruct a as [a [v [α eq]]]; cbn.
            subst a.
            rewrite <- (mult_rid α).
            pose (USM := module_scalar (cring_module F)).
            change (α * 1) with (α · 1).
            rewrite (single_to_grade_sum_scalar V (λ _, cring_module F) v α).
            rewrite f1_scalar, f2_scalar.
            apply f_equal.
            assert (single_to_grade_sum V (k := v) _ 1 = to_free v) as eq
                by reflexivity.
            rewrite eq.
            rewrite f1_in, f2_in.
            reflexivity.
Qed.
(* begin hide *)

End LinearFree.

Close Scope card_scope.
(* end hide *)
