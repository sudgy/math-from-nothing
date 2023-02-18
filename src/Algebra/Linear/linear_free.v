Require Import init.

Require Export linear_base.
Require Import linear_grade_sum.
Require Import linear_extend.
Require Import linear_transformation_space.
Require Import module_category.

Require Import set.
Require Import unordered_list.
Require Import plus_sum.
Require Import category_initterm.

(* begin hide *)
Section LinearFree.

Context (F : CRingObj) (V : Type).
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
Let FV := module_V free_linear.
Let free_plus_class := module_plus free_linear.
Let free_zero := module_zero free_linear.
Let free_neg := module_neg free_linear.
Let free_plus_assoc_class := module_plus_assoc free_linear.
Let free_plus_comm_class := module_plus_comm free_linear.
Let free_plus_lid_class := module_plus_lid free_linear.
Let free_plus_linv_class := module_plus_linv free_linear.
Let free_scalar := module_scalar free_linear.
Let free_scalar_id_class := module_scalar_id free_linear.
Let free_scalar_ldist_class := module_scalar_ldist free_linear.
Let free_scalar_rdist_class := module_scalar_rdist free_linear.
Let free_scalar_comp_class := module_scalar_comp free_linear.
Definition free_grade := grade_sum_grade V (λ _, cring_module F).

Existing Instances free_plus_class free_zero free_neg free_plus_assoc_class
    free_plus_comm_class free_plus_lid_class free_plus_linv_class free_scalar
    free_scalar_id_class free_scalar_ldist_class free_scalar_rdist_class
    free_scalar_comp_class free_grade.

Definition to_free v := single_to_grade_sum V (λ _, cring_module F) (k := v) 1.

Theorem to_free_ex : ∀ (v : V) (x : FV),
    of_grade v x → ∃ α, x = α · to_free v.
Proof.
    intros v x [α x_eq].
    exists α.
    rewrite <- x_eq.
    rewrite <- (mult_rid α) at 1.
    pose (USM := module_scalar (cring_module F)).
    change (α * 1) with (α · 1).
    rewrite (single_to_grade_sum_scalar V (λ _, cring_module F) v α).
    apply f_equal.
    reflexivity.
Qed.

Section FreeExtend.

Context {V2} `{
    VP : Plus V2,
    VZ : Zero V2,
    VN : Neg V2,
    @PlusComm V2 VP,
    @PlusAssoc V2 VP,
    @PlusLid V2 VP VZ,
    @PlusLinv V2 VP VZ VN,

    SM : ScalarMult U V2,
    @ScalarId U V2 UO SM,
    @ScalarLdist U V2 VP SM,
    @ScalarRdist U V2 UP VP SM,
    @ScalarComp U V2 UM SM
}.

Variable f_base : V → V2.
Let f1 (i : V) (v : FV) (H : of_grade i v) := ex_val H · f_base i.

Lemma free_extend_plus_base : linear_extend_plus_base f1.
Proof.
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
Qed.
Lemma free_extend_scalar_base : linear_extend_scalar_base f1.
Proof.
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
Qed.

Definition free_extend := linear_extend f1 : FV → V2.
Let f := free_extend.

Theorem free_extend_plus : ∀ a b, f (a + b) = f a + f b.
Proof.
    apply linear_extend_plus.
    -   exact free_extend_plus_base.
    -   exact free_extend_scalar_base.
Qed.

Theorem free_extend_scalar : ∀ a v, f (a · v) = a · f v.
Proof.
    apply linear_extend_scalar.
    -   exact free_extend_plus_base.
    -   exact free_extend_scalar_base.
Qed.

Theorem free_extend_zero : f 0 = 0.
Proof.
    rewrite <- (scalar_lanni 0).
    rewrite free_extend_scalar.
    apply scalar_lanni.
Qed.

Theorem free_extend_neg : ∀ x, f (-x) = -f x.
Proof.
    intros x.
    rewrite <- scalar_neg_one.
    rewrite free_extend_scalar.
    apply scalar_neg_one.
Qed.

Theorem free_extend_free : ∀ v : V, f (to_free v) = f_base v.
Proof.
    intros v.
    unfold f, free_extend.
    assert (of_grade v (to_free v)) as v_grade.
    {
        exists 1.
        unfold to_free.
        reflexivity.
    }
    rewrite (linear_extend_homo (VG := free_grade)
        f1 free_extend_scalar_base v (to_free v) v_grade).
    unfold f1.
    rewrite_ex_val a aH.
    unfold to_free in aH.
    apply single_to_grade_sum_eq in aH.
    rewrite aH.
    apply scalar_id.
Qed.

End FreeExtend.
Section FreeBilinear.

Context {V2} `{
    VP : Plus V2,
    VZ : Zero V2,
    VN : Neg V2,
    @PlusComm V2 VP,
    @PlusAssoc V2 VP,
    @PlusLid V2 VP VZ,
    @PlusLinv V2 VP VZ VN,

    SM : ScalarMult U V2,
    @ScalarId U V2 UO SM,
    @ScalarLdist U V2 VP SM,
    @ScalarRdist U V2 UP VP SM,
    @ScalarComp U V2 UM SM
}.

Variable op : V → V → V2.

Let TP := linear_func_plus V V2.
Let TZ := linear_func_zero V V2.
Let TN := linear_func_neg V V2.
Let TPC := linear_func_plus_comm V V2.
Let TPA := linear_func_plus_assoc V V2.
Let TPZ := linear_func_plus_lid V V2.
Let TPN := linear_func_plus_linv V V2.
Let TSM := linear_func_scalar V V2.
Let TSMO := linear_func_scalar_id V V2.
Let TSML := linear_func_scalar_ldist V V2.
Let TSMR := linear_func_scalar_rdist V V2.
Let TSMC := linear_func_scalar_comp V V2.
Local Existing Instances TP TZ TN TPC TPA TPZ TPN TSM TSMO TSML TSMR TSMC.

Definition free_bilinear_base := free_extend op.
Definition free_bilinear (v : FV) := free_extend (free_bilinear_base v).
Let f := free_bilinear.

Theorem free_bilinear_ldist : ∀ a b c, f a (b + c) = f a b + f a c.
Proof.
    intros a b c.
    unfold f.
    unfold free_bilinear.
    apply free_extend_plus.
Qed.

Theorem free_bilinear_rdist : ∀ a b c, f (a + b) c = f a c + f b c.
Proof.
    intros a b c.
    unfold f.
    unfold free_bilinear.
    unfold free_bilinear_base.
    rewrite free_extend_plus.
    rewrite (grade_decomposition_eq c).
    remember (grade_decomposition c) as l; clear Heql.
    induction l as [|v l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite free_extend_zero.
        rewrite plus_lid.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    do 3 rewrite free_extend_plus.
    rewrite IHl; clear IHl.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite <- plus_assoc.
    rewrite (plus_comm _ (free_extend (free_extend op b) _)).
    rewrite plus_assoc.
    apply rplus.
    destruct v as [v [x vx]]; cbn.
    apply to_free_ex in vx as [α v_eq]; subst v.
    do 3 rewrite free_extend_scalar.
    rewrite <- scalar_ldist.
    apply f_equal.
    do 3 rewrite free_extend_free.
    unfold plus at 1; cbn.
    reflexivity.
Qed.

Theorem free_bilinear_lscalar : ∀ a u v, f (a · u) v = a · f u v.
Proof.
    intros a u v.
    unfold f, free_bilinear, free_bilinear_base.
    rewrite free_extend_scalar.
    rewrite (grade_decomposition_eq v).
    remember (grade_decomposition v) as l; clear v Heql.
    induction l as [|v l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite free_extend_zero.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    do 2 rewrite free_extend_plus.
    rewrite IHl; clear IHl.
    rewrite scalar_ldist.
    apply rplus.
    destruct v as [v [x vx]]; cbn.
    apply to_free_ex in vx as [α v_eq]; subst v.
    do 2 rewrite free_extend_scalar.
    rewrite scalar_comp.
    rewrite mult_comm.
    rewrite <- scalar_comp.
    apply f_equal.
    do 2 rewrite free_extend_free.
    unfold scalar_mult at 1; cbn.
    reflexivity.
Qed.

Theorem free_bilinear_rscalar : ∀ a u v, f u (a · v) = a · f u v.
Proof.
    intros a u v.
    unfold f, free_bilinear, free_bilinear_base.
    apply free_extend_scalar.
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

Definition free_module := make_module
    F
    FV
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
    free_from_module : ModuleObj F;
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
Proof.
    intros [f f_eq] [g g_eq].
    unfold free_from_set in *.
    unfold free_from_compose; cbn.
    intros x.
    rewrite g_eq.
    apply f_eq.
Qed.

Lemma free_from_set_id_in : ∀ f : free_from, free_from_set f f 𝟙.
Proof.
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
Proof.
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
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        exists (make_module_homomorphism _ free_module _
            (free_extend g) (free_extend_plus g) (free_extend_scalar g)).
        unfold free_from_set; cbn.
        apply free_extend_free.
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
            destruct a as [a [v av]]; cbn.
            apply to_free_ex in av as [α a_eq]; subst a.
            rewrite f1_scalar, f2_scalar.
            apply f_equal.
            rewrite f1_in, f2_in.
            reflexivity.
Qed.
(* begin hide *)

End LinearFree.
(* end hide *)
