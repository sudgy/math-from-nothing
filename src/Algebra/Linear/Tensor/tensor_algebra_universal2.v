Require Import init.

Require Import linear_extend.
Require Import linear_grade_isomorphism.
Require Import tensor_power_base.
Require Import tensor_algebra_base.
Require Import tensor_algebra_scalar.
Require Import tensor_algebra_vector.
Require Import tensor_algebra_grade.
Require Import tensor_algebra_mult.
Require Import tensor_algebra_universal.

Require Import algebra_category.
Require Import category_initterm.

Require Import set.
Require Import card.
Require Import list.
Require Import unordered_list.
Require Import mult_product.

Unset Keyed Unification.

Section TensorAlgebra.

Context {F : CRing} (V : Module F).

Let vector_to_tensor_base := tensor_algebra_vector.vector_to_tensor V.
Let scalar_to_tensor_base := tensor_algebra_scalar.scalar_to_tensor V.

Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let VP := module_plus V.
Let VZ := module_zero V.
Let VSM := module_scalar V.
Let TAP := algebra_plus (tensor_algebra V).
Let TAZ := algebra_zero (tensor_algebra V).
Let TAN := algebra_neg (tensor_algebra V).
Let TAPC := algebra_plus_comm (tensor_algebra V).
Let TAPA := algebra_plus_assoc (tensor_algebra V).
Let TAPZ := algebra_plus_lid (tensor_algebra V).
Let TAPN := algebra_plus_linv (tensor_algebra V).
Let TASM := algebra_scalar (tensor_algebra V).
Let TASO := algebra_scalar_id (tensor_algebra V).
Let TAM := algebra_mult (tensor_algebra V).
Let TAMR := algebra_mult_rid (tensor_algebra V).
Let TAO := algebra_one (tensor_algebra V).

Existing Instances UP UZ UN UPC UPZ UPN UM UO VP VZ VSM TAP TAZ TAN TAPC TAPA TAPZ TAPN TASM TASO TAM TAMR TAO.

Theorem vector_to_tensor_plus : ∀ u v, vector_to_tensor (u + v) =
        vector_to_tensor u + vector_to_tensor v.
    apply module_homo_plus.
Qed.
Theorem vector_to_tensor_scalar : ∀ a v, vector_to_tensor (a · v) =
        a · vector_to_tensor v.
    apply module_homo_scalar.
Qed.
Theorem vector_to_tensor_zero : vector_to_tensor 0 = 0.
    apply module_homo_zero.
Qed.

Lemma tensor_algebra_iso_ex :
    ∃ f : cat_morphism (ALGEBRA F) (tensor_algebra_object V) (tensor_algebra V),
        isomorphism f ∧
        ∀ x, algebra_homo_f f (vector_to_tensor_base x) =
            module_homo_f (vector_to_tensor_homo V) x.
    pose proof (initial_unique _ _
        (tensor_algebra_ex_base V) (ex_proof (tensor_algebra_ex V)))
        as [[f f_eq] [[g g_eq] [fg gf]]].
    cbn in *.
    unfold to_algebra_set in *; cbn in *.
    change (ex_type_val (ex_to_type (tensor_algebra_ex V)))
        with (to_tensor_algebra V) in *.
    inversion fg as [eq1]; clear fg.
    inversion gf as [eq2]; clear gf.
    exists f.
    split.
    -   exists g.
        split.
        +   apply algebra_homomorphism_eq.
            apply (func_eq _ _ eq1).
        +   apply algebra_homomorphism_eq.
            apply (func_eq _ _ eq2).
    -   exact f_eq.
Qed.

Let f := ex_val tensor_algebra_iso_ex.
Let f_iso := land (ex_proof tensor_algebra_iso_ex).
Let g := ex_val f_iso.
Lemma tensor_algebra_iso_eq : ∀ x, algebra_homo_f f (vector_to_tensor_base x)
        = vector_to_tensor x.
    apply (ex_proof tensor_algebra_iso_ex).
Qed.
Lemma tensor_algebra_iso_fg : ∀ x, algebra_homo_f f (algebra_homo_f g x) = x.
    intros x.
    pose proof (ex_proof f_iso) as [eq1 eq2]; clear eq2.
    inversion eq1 as [eq1'].
    apply (func_eq _ _ eq1').
Qed.
Lemma tensor_algebra_iso_gf : ∀ x, algebra_homo_f g (algebra_homo_f f x) = x.
    intros x.
    pose proof (ex_proof f_iso) as [eq1 eq2]; clear eq1.
    inversion eq2 as [eq2'].
    apply (func_eq _ _ eq2').
Qed.

Theorem vector_to_tensor_eq : ∀ u v : module_V V,
        vector_to_tensor u = vector_to_tensor v → u = v.
    intros u v eq.
    do 2 rewrite <- tensor_algebra_iso_eq in eq.
    apply (f_equal (algebra_homo_f g)) in eq.
    do 2 rewrite tensor_algebra_iso_gf in eq.
    apply vector_to_tensor_eq in eq.
    exact eq.
Qed.

Definition scalar_to_tensor (a : cring_U F)
    := algebra_homo_f f (scalar_to_tensor_base a).

Theorem scalar_to_tensor_eq : ∀ a b,
        scalar_to_tensor a = scalar_to_tensor b → a = b.
    intros a b eq.
    unfold scalar_to_tensor in eq.
    apply (f_equal (algebra_homo_f g)) in eq.
    do 2 rewrite tensor_algebra_iso_gf in eq.
    apply scalar_to_tensor_eq in eq.
    exact eq.
Qed.

Theorem scalar_to_tensor_plus : ∀ a b,
        scalar_to_tensor (a + b) = scalar_to_tensor a + scalar_to_tensor b.
    intros a b.
    unfold scalar_to_tensor.
    rewrite (scalar_to_tensor_plus V).
    apply algebra_homo_plus.
Qed.

Theorem scalar_to_tensor_zero : scalar_to_tensor 0 = 0.
    unfold scalar_to_tensor.
    unfold scalar_to_tensor_base.
    pose proof (scalar_to_tensor_zero V) as eq.
    unfold zero in eq at 2 3; cbn in eq.
    unfold UZ.
    rewrite eq.
    apply (algebra_homo_zero f).
Qed.

Theorem scalar_to_tensor_mult : ∀ a b,
        scalar_to_tensor (a * b) = scalar_to_tensor a * scalar_to_tensor b.
    intros a b.
    unfold scalar_to_tensor.
    rewrite (scalar_to_tensor_mult V).
    apply algebra_homo_mult.
Qed.

Theorem scalar_to_tensor_scalar : ∀ a A,
        scalar_to_tensor a * A = a · A.
    intros a A.
    unfold scalar_to_tensor.
    rewrite <- (tensor_algebra_iso_fg A) at 1.
    rewrite <- (algebra_homo_mult _ _ f).
    rewrite (scalar_to_tensor_scalar V).
    rewrite (algebra_homo_scalar _ _ f).
    rewrite tensor_algebra_iso_fg.
    reflexivity.
Qed.

Theorem scalar_to_tensor_one : scalar_to_tensor 1 = 1.
    rewrite <- scalar_id.
    rewrite <- scalar_to_tensor_scalar.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem scalar_to_tensor_comm : ∀ a A,
        scalar_to_tensor a * A = A * scalar_to_tensor a.
    intros a A.
    unfold scalar_to_tensor.
    rewrite <- (tensor_algebra_iso_fg A) at 1.
    rewrite <- (algebra_homo_mult _ _ f).
    rewrite (scalar_to_tensor_comm V).
    rewrite (algebra_homo_mult _ _ f).
    rewrite tensor_algebra_iso_fg.
    reflexivity.
Qed.

Let TAG := tensor_grade V.
Let TAGM := tensor_grade_mult V.
Existing Instances TAG TAGM.

Definition tensor_grade := grade_isomorphism
    (algebra_to_module_homomorphism f)
    (algebra_to_module_iso f f_iso).
Definition tensor_grade_mult := graded_algebra_isomorphism f f_iso.

Existing Instances tensor_grade tensor_grade_mult.

Theorem scalar_to_tensor_grade : ∀ a,
        of_grade (H10 := tensor_grade) 0 (scalar_to_tensor a).
    intros a.
    unfold of_grade; cbn.
    exists (scalar_to_tensor_base a).
    cbn.
    split.
    -   exists a.
        reflexivity.
    -   reflexivity.
Qed.

Theorem vector_to_tensor_grade : ∀ v,
        of_grade (H10 := tensor_grade) 1 (vector_to_tensor v).
    intros v.
    unfold of_grade; cbn.
    exists (vector_to_tensor_base v).
    cbn.
    split.
    -   exists (vectors_to_power V (v :: list_end)).
        reflexivity.
    -   apply tensor_algebra_iso_eq.
Qed.

Definition vectors_to_tensor (l : list (module_V V))
    := rfold mult 1 (list_image l vector_to_tensor).

Theorem vectors_to_tensor_end : vectors_to_tensor list_end = 1.
    cbn.
    reflexivity.
Qed.

Theorem vectors_to_tensor_grade : ∀ l,
        of_grade (H10 := tensor_grade) (list_size l) (vectors_to_tensor l).
    intros l.
    induction l.
    -   rewrite vectors_to_tensor_end.
        pose proof scalar_to_tensor_one as eq.
        unfold tensor_algebra, algebra_V in eq.
        rewrite <- eq.
        apply scalar_to_tensor_grade.
    -   change (vectors_to_tensor (a :: l)) with
            (vector_to_tensor a * vectors_to_tensor l).
        change (list_size (a :: l)) with (1 + list_size l).
        apply (grade_mult (H := tensor_grade)).
        +   apply vector_to_tensor_grade.
        +   exact IHl.
Qed.

Definition simple_tensor x := ∃ α l, x = α · vectors_to_tensor l.

Theorem tensor_grade_sum : ∀ x (i : nat), of_grade (H10 := tensor_grade) i x →
        ∃ l : ulist (cring_U F *
            set_type (λ l : list (module_V V), list_size l = i)),
        ulist_sum (ulist_image l (λ x, fst x · vectors_to_tensor [snd x|]))
        = x.
    intros x' i [x [xi x'_eq]]; subst x'.
    destruct xi as [x' x_eq]; subst x.
    rename x' into x.
    cbn.
    pose proof (tensor_power_sum V x) as [l x_eq]; subst x.
    exists (ulist_image l (λ x, (ex_val [|x], ex_val (ex_proof [|x])))).
    rewrite ulist_image_comp; cbn.
    induction l using ulist_induction.
    -   do 2 rewrite ulist_image_end, ulist_sum_end.
        rewrite power_to_tensor_zero.
        symmetry; apply (algebra_homo_zero f).
    -   do 2 rewrite ulist_image_add, ulist_sum_add.
        rewrite IHl; clear IHl.
        rewrite power_to_tensor_plus.
        rewrite algebra_homo_plus.
        apply rplus; clear l.
        unfold ex_val, ex_proof.
        destruct (ex_to_type [|a]) as [α l_ex]; cbn.
        destruct (ex_to_type l_ex) as [l a_eq]; cbn.
        clear l_ex.
        rewrite a_eq; clear a_eq a.
        rewrite power_to_tensor_scalar.
        rewrite algebra_homo_scalar.
        apply f_equal.
        rewrite <- power_to_tensor_k_eq.
        destruct l as [l l_eq]; cbn; clear l_eq.
        induction l.
        +   cbn.
            unfold TAO.
            pose proof (algebra_homo_one _ _ f).
            cbn in *.
            unfold tensor_algebra in *.
            rewrite <- H.
            apply f_equal.
            reflexivity.
        +   cbn.
            rewrite IHl.
            rewrite <- (tensor_algebra_iso_fg (vector_to_tensor a)).
            rewrite <- (algebra_homo_mult _ _ f).
            apply f_equal.
            assert (algebra_homo_f g (vector_to_tensor a) =
                vector_to_tensor_base a) as a_eq.
            {
                rewrite <- tensor_algebra_iso_eq.
                rewrite tensor_algebra_iso_gf.
                reflexivity.
            }
            rewrite a_eq; clear a_eq.
            assert (homogeneous (H10 := TAG) (vector_to_tensor_base a))
                as a_homo.
            {
                exists 1.
                exists (vectors_to_power V (a :: list_end)).
                reflexivity.
            }
            assert (homogeneous (H10 := TAG)
                (power_to_tensor V (vectors_to_power V l))) as l_homo.
            {
                exists (list_size l).
                exists (vectors_to_power V l).
                reflexivity.
            }
            unfold mult; cbn.
            change (vector_to_tensor_base a) with [[_|a_homo]|].
            change (power_to_tensor V (vectors_to_power V l))
                with [[_|l_homo]|].
            pose (TA'N := tensor_algebra_neg V).
            pose (TA'PZ := tensor_algebra_plus_lid V).
            pose (TA'PN := tensor_algebra_plus_linv V).
            pose (TA'SM := tensor_algebra_scalar_mult V).
            pose (TA'SMO := tensor_algebra_scalar_id V).
            pose (TA'SML := tensor_algebra_scalar_ldist V).
            pose (TA'SMR := tensor_algebra_scalar_rdist V).
            rewrite bilinear_extend_homo.
            2: apply tensor_mult_base_lscalar.
            2: apply tensor_mult_base_rscalar.
            unfold vector_to_tensor_base,
                tensor_algebra_vector.vector_to_tensor.
            rewrite (power_to_tensor_tm V).
            change (tensor_product_universal.tensor_mult V (cring_module F) a 1)
                with (vectors_to_power V (a :: list_end)).
            change (one (U := nat)) with (list_size (a :: list_end)).
            rewrite (vectors_to_power_mult V).
            rewrite <- power_to_tensor_k_eq.
            cbn.
            reflexivity.
Qed.

Theorem tensor_simple_sum : ∀ x, ∃ l : ulist (set_type simple_tensor),
        x = ulist_sum (ulist_image l (λ x, [x|])).
    intros x.
    rewrite (grade_decomposition_eq (H10 := tensor_grade) x).
    pose (l := grade_decomposition x).
    change (grade_decomposition x) with l.
    clearbody l.
    clear x.
    induction l as [|v l] using ulist_induction.
    {
        exists ulist_end.
        do 2 rewrite ulist_image_end.
        reflexivity.
    }
    destruct IHl as [l' l'_eq].
    rewrite ulist_image_add, ulist_sum_add.
    assert (∃ vl : ulist (set_type simple_tensor),
        [v|] = ulist_sum (ulist_image vl (λ x, [x|]))) as [vl v_eq].
    {
        clear l l' l'_eq.
        destruct v as [v [i vi]]; cbn.
        pose proof (tensor_grade_sum v i vi) as [l v_eq].
        subst v; clear vi.
        assert (∀ p : cring_U F *
                      set_type (λ l : list (module_V V), list_size l = i),
              simple_tensor (fst p · vectors_to_tensor [snd p|])) as l_in.
        {
            clear l.
            intros [a [l l_eq]]; cbn.
            clear l_eq.
            exists a, l.
            reflexivity.
        }
        exists (ulist_image l (λ x, [_|l_in x])).
        rewrite ulist_image_comp; cbn.
        reflexivity.
    }
    exists (vl +++ l').
    rewrite l'_eq.
    pose (X := [v|]).
    fold X in v_eq.
    change [v|] with X.
    rewrite v_eq.
    clear X v_eq.
    rewrite ulist_image_conc, ulist_sum_plus.
    reflexivity.
Qed.

Theorem tensor_sum : ∀ x, ∃ l : ulist (cring_U F * list (module_V V)),
        x = ulist_sum (ulist_image l (λ p, fst p · list_prod
            (list_image (snd p) (λ v, vector_to_tensor v)))).
    intros x.
    pose proof (tensor_simple_sum x) as [l l_eq]; subst x.
    exists (ulist_image l (λ x, (ex_val [|x], ex_val (ex_proof [|x])))).
    rewrite ulist_image_comp; cbn.
    induction l using ulist_induction.
    {
        do 2 rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    }
    do 2 rewrite ulist_image_add, ulist_sum_add.
    rewrite <- IHl; clear IHl.
    apply rplus; clear l.
    destruct a as [a l_ex]; cbn.
    unfold ex_val at 1, ex_proof.
    destruct (ex_to_type l_ex) as [α C0]; cbn.
    rewrite_ex_val l l_eq; clear l_ex C0.
    subst a.
    apply f_equal.
    induction l.
    {
        cbn.
        reflexivity.
    }
    cbn.
    rewrite <- IHl; clear IHl.
    reflexivity.
Qed.

End TensorAlgebra.
