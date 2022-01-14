Require Import init.

Require Import unordered_list.

Require Export exterior_construct.
Require Import exterior_outermorphism.
Require Import module_category.
Require Import algebra_category.

Section ExteriorInvolutions.

Context {F : CRing} (V : Module F).

Let VP := module_plus V.
Let VZ := module_zero V.
Let VN := module_neg V.
Let VPA := module_plus_assoc V.
Let VPC := module_plus_comm V.
Let VPZ := module_plus_lid V.
Let VPN := module_plus_linv V.
Let VS := module_scalar V.
Let VSL := module_scalar_ldist V.

Existing Instances VP VZ VN VPA VPC VPZ VPN VS VSL.

Let EP := ext_plus V.
Let EZ := ext_zero V.
Let EN := ext_neg V.
Let EPA := ext_plus_assoc V.
Let EPC := ext_plus_comm V.
Let EPZ := ext_plus_lid V.
Let EPN := ext_plus_linv V.
Let EM := ext_mult V.
Let EO := ext_one V.
Let ES := ext_scalar V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO ES.

Definition ext_involute_base (v : module_V V) := -v.

Lemma ext_involute_base_plus : ∀ u v, ext_involute_base (u + v) =
        ext_involute_base u + ext_involute_base v.
    intros u v.
    unfold ext_involute_base.
    apply neg_plus.
Qed.

Lemma ext_involute_base_scalar : ∀ a v,
        ext_involute_base (a · v) = a · ext_involute_base v.
    intros a v.
    unfold ext_involute_base.
    symmetry; apply scalar_rneg.
Qed.

Definition ext_involute := outermorphism (make_module_homomorphism F V V
    ext_involute_base ext_involute_base_plus ext_involute_base_scalar).

Theorem ext_involute_eq : ∀ v,
        ext_involute (vector_to_ext V v) = -vector_to_ext V v.
    intros v.
    unfold ext_involute.
    rewrite (outermorphism_eq V); cbn.
    unfold ext_involute_base.
    apply vector_to_ext_neg.
Qed.

Theorem ext_involute_plus :
        ∀ u v, ext_involute (u + v) = ext_involute u + ext_involute v.
    apply outermorphism_plus.
Qed.

Theorem ext_involute_scalar :
        ∀ a v, ext_involute (a · v) = a · ext_involute v.
    apply outermorphism_scalar.
Qed.

Theorem ext_involute_mult :
        ∀ u v, ext_involute (u * v) = ext_involute u * ext_involute v.
    apply outermorphism_mult.
Qed.

Theorem ext_involute_one : ext_involute 1 = 1.
    apply outermorphism_one.
Qed.

Theorem ext_involute_neg : ∀ v, ext_involute (-v) = -ext_involute v.
    apply outermorphism_neg.
Qed.

Theorem ext_involute_zero : ext_involute 0 = 0.
    apply outermorphism_zero.
Qed.

Theorem ext_involute_inv : ∀ v, ext_involute (ext_involute v) = v.
    intros v.
    pose proof (ext_sum V v) as [l l_eq]; subst v.
    induction l using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        replace (ext_involute 0) with 0.
        -   apply ext_involute_zero.
        -   symmetry; apply ext_involute_zero.
    }
    rewrite ulist_image_add, ulist_sum_add.
    do 2 rewrite ext_involute_plus.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    destruct a as [a l]; cbn.
    do 2 rewrite ext_involute_scalar.
    apply f_equal; clear a.
    induction l.
    {
        cbn.
        replace (ext_involute 1) with 1.
        -   apply ext_involute_one.
        -   symmetry; apply ext_involute_one.
    }
    cbn.
    do 2 rewrite ext_involute_mult.
    rewrite IHl; clear IHl.
    apply rmult; clear l.
    rewrite ext_involute_eq.
    rewrite ext_involute_neg.
    rewrite ext_involute_eq.
    apply neg_neg.
Qed.

End ExteriorInvolutions.
