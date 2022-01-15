Require Import init.

Require Import set.
Require Import card.

Require Import module_category.
Require Import algebra_category.
Require Import linear_bilinear_form.
Require Import linear_sum.
Require Import linear_transformation_space.

Require Export geometric_construct.
Require Export exterior_construct.
Require Import exterior_universal.

Section GeometricToExterior.

Context {F : CRing} {V : Module F}.

Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UMC := cring_mult_comm F.

Existing Instances UP UZ UN UPC UPZ UPN UM UMC.

Let VP := module_plus V.
Let VS := module_scalar V.

Existing Instances VP VS.

Context (B : set_type bilinear_form).

Let EP := ext_plus V.
Let EZ := ext_zero V.
Let EN := ext_neg V.
Let EPA := ext_plus_assoc V.
Let EPC := ext_plus_comm V.
Let EPZ := ext_plus_lid V.
Let EPN := ext_plus_linv V.
Let EM := ext_mult V.
Let EO := ext_one V.
Let EMA := ext_mult_assoc V.
Let EML := ext_mult_lid V.
Let EMR := ext_mult_rid V.
Let ES := ext_scalar V.
Let ESL := ext_scalar_ldist V.
Let ESR := ext_scalar_rdist V.
Let ESC := ext_scalar_comp V.
Let EL := ext_ldist V.
Let ER := ext_rdist V.
Let ESML := ext_scalar_lmult V.
Let ESMR := ext_scalar_rmult V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO EMA EML EMR ES ESL ESR ESC EL ER ESML ESMR.

Let E12 := direct_sum (algebra_module (exterior_algebra V))
                       (algebra_module (exterior_algebra V)).
Let E12P := module_plus E12.
Let E12S := module_scalar E12.

Existing Instances E12P E12S.

Definition ext_inner_base1 (a : module_V V) (v : module_V V) (p : module_V E12)
    := (
        vector_to_ext V v * fst p,
        -vector_to_ext V v * snd p + [B|] a v · (fst p)
    ) : module_V E12.

Lemma ext_inner_base_plus : ∀ a v p1 p2, ext_inner_base1 a v (p1 + p2) =
        ext_inner_base1 a v p1 + ext_inner_base1 a v p2.
    intros a v [p11 p12] [p21 p22]; cbn.
    unfold ext_inner_base1; cbn.
    unfold plus at 1 3 4 5; cbn.
    apply f_equal2.
    -   apply ldist.
    -   rewrite ldist.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        rewrite scalar_ldist.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.

Lemma ext_inner_base_scalar : ∀ a v b p, ext_inner_base1 a v (b · p) =
        b · ext_inner_base1 a v p.
    intros a v b [p1 p2].
    unfold ext_inner_base1; cbn.
    unfold scalar_mult at 1 2 4 5; cbn.
    apply f_equal2.
    -   apply scalar_rmult.
    -   rewrite scalar_rmult.
        rewrite scalar_comp.
        rewrite (mult_comm _ b).
        rewrite <- scalar_comp.
        rewrite scalar_ldist.
        reflexivity.
Qed.

Definition ext_inner_base2 (a : module_V V) (v : module_V V) :=
    make_module_homomorphism F E12 E12
    (ext_inner_base1 a v)
    (ext_inner_base_plus a v)
    (ext_inner_base_scalar a v).

Let E3 := linear_trans_algebra E12.
Let E3P := algebra_plus E3.
Let E3Z := algebra_zero E3.
Let E3S := algebra_scalar E3.
Let E3M := algebra_mult E3.

Existing Instances E3P E3Z E3S E3M.

Lemma ext_inner_base2_plus : ∀ a v1 v2, ext_inner_base2 a (v1 + v2) =
        ext_inner_base2 a v1 + ext_inner_base2 a v2.
    intros a v1 v2.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold plus at 2; cbn.
    unfold ext_inner_base2, linear_trans_plus_base; cbn.
    unfold ext_inner_base1; cbn.
    unfold plus at 5; cbn.
    apply f_equal2.
    -   rewrite (vector_to_ext_plus V).
        apply rdist.
    -   rewrite (vector_to_ext_plus V).
        rewrite neg_plus.
        rewrite rdist.
        do 2 rewrite <- plus_assoc.
        apply lplus.
        rewrite bilinear_form_rplus.
        rewrite scalar_rdist.
        do 2 rewrite plus_assoc.
        apply rplus.
        apply plus_comm.
Qed.

Lemma ext_inner_base2_scalar : ∀ a b v,
        ext_inner_base2 a (b · v) = b · ext_inner_base2 a v.
    intros a b v.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold scalar_mult at 2; cbn.
    unfold linear_trans_scalar_base; cbn.
    unfold ext_inner_base1; cbn.
    unfold scalar_mult at 5; cbn.
    apply f_equal2.
    -   rewrite (vector_to_ext_scalar V).
        apply scalar_lmult.
    -   rewrite (vector_to_ext_scalar V).
        rewrite bilinear_form_rscalar.
        rewrite <- scalar_comp.
        rewrite scalar_ldist.
        do 2 rewrite mult_lneg.
        rewrite scalar_rneg.
        rewrite scalar_lmult.
        reflexivity.
Qed.

Lemma ext_inner_base_alternating : ∀ a v,
        0 = ext_inner_base2 a v * ext_inner_base2 a v.
    intros a v.
    apply module_homomorphism_eq.
    intros [x1 x2].
    unfold mult, zero; cbn.
    unfold linear_trans_zero_base, ext_inner_base1; cbn.
    unfold zero; cbn.
    apply f_equal2.
    -   rewrite mult_assoc.
        rewrite <- (ext_alternating V).
        rewrite mult_lanni.
        reflexivity.
    -   rewrite ldist.
        rewrite mult_assoc.
        rewrite mult_lneg, mult_rneg.
        rewrite <- (ext_alternating V).
        rewrite neg_neg, mult_lanni, plus_lid.
        rewrite <- scalar_rmult.
        rewrite <- rdist.
        rewrite plus_linv.
        rewrite mult_lanni.
        reflexivity.
Qed.

Definition ext_inner_base3 a := make_module_homomorphism
    F
    V
    (algebra_module E3)
    (ext_inner_base2 a)
    (ext_inner_base2_plus a)
    (ext_inner_base2_scalar a).

Definition ext_inner_base4 a := make_to_ext
    V
    E3
    (ext_inner_base3 a)
    (ext_inner_base_alternating a).

Definition ext_inner_base a
    := card_one_ex (exterior_universal V (ext_inner_base4 a)).

Definition ext_inner_homo a := [ext_inner_base a|].
Definition ext_inner_f a := algebra_homo_f (ext_inner_homo a).

Theorem ext_inner_f_eq : ∀ a v,
        ext_inner_f a (vector_to_ext V v) = ext_inner_base2 a v.
    intros a.
    apply [|ext_inner_base a].
Qed.

Theorem ext_inner_f_mult : ∀ a u v,
        ext_inner_f a (u * v) = ext_inner_f a u * ext_inner_f a v.
    intros a u v.
    apply algebra_homo_mult.
Qed.

Definition ext_inner a v := snd (module_homo_f (ext_inner_f a v) (1, 0)).

Theorem ext_inner_scalar : ∀ a α, 0 = ext_inner a (scalar_to_ext V α).
    intros a α.
    unfold ext_inner.
    unfold ext_inner_f.
    rewrite scalar_to_ext_one_scalar.
    rewrite algebra_homo_scalar.
    rewrite algebra_homo_one.
    unfold scalar_mult; cbn.
    unfold linear_trans_scalar_base.
    unfold one at 1; cbn.
    unfold scalar_mult; cbn.
    rewrite scalar_ranni.
    reflexivity.
Qed.

Theorem ext_inner_vector : ∀ a v,
        ext_inner a (vector_to_ext V v) = [B|] a v · 1.
    intros a v.
    unfold ext_inner.
    rewrite ext_inner_f_eq.
    cbn.
    rewrite mult_ranni, plus_lid.
    reflexivity.
Qed.

Theorem ext_inner_bivector : ∀ a u v,
        ext_inner a (vector_to_ext V u * vector_to_ext V v) =
        [B|] a u · vector_to_ext V v -
        [B|] a v · vector_to_ext V u.
    intros a u v.
    unfold ext_inner.
    rewrite ext_inner_f_mult.
    do 2 rewrite ext_inner_f_eq.
    unfold mult; cbn.
    rewrite mult_ranni, plus_lid.
    rewrite plus_comm.
    rewrite scalar_rmult.
    do 2 rewrite mult_rid.
    rewrite scalar_rneg.
    reflexivity.
Qed.

End GeometricToExterior.
