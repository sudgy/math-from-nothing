Require Import init.

Require Export exterior_base.
Require Import algebra_category.
Require Import linear_span.
Require Import linear_subspace.
Require Export linear_grade_sum.
Require Import linear_extend.
Require Import linear_bilinear.

Require Import nat.
Require Import list.
Require Import unordered_list.

Section ExteriorGrade.

Context {U : CRingObj} (V : ModuleObj U).
Local Notation φ := (vector_to_ext V).

Section Single.

Variable n : nat.

Definition ext_n_base (X : algebra_V (exterior_algebra V)) :=
    ∃ l, X = list_prod (list_image φ l) ∧ list_size l = n.

Definition ext_n_subspace := linear_span_subspace (cring_U U) ext_n_base.

Definition ext_n_module := make_module
    U
    (set_type (subspace_set ext_n_subspace))
    (subspace_plus_class _)
    (subspace_zero_class _)
    (subspace_neg_class _)
    (subspace_plus_assoc _)
    (subspace_plus_comm _)
    (subspace_plus_lid _)
    (subspace_plus_linv _)
    (subspace_scalar_class _)
    (subspace_scalar_id _)
    (subspace_scalar_ldist _)
    (subspace_scalar_rdist _)
    (subspace_scalar_comp _)
.

End Single.

Definition ext_n_algebra_module := sum_module nat ext_n_module.

Definition ext_n_grade := sum_module_grade nat ext_n_module
    : GradedSpace ext_n_algebra_module nat.
Local Existing Instances ext_n_grade.

Definition to_ext_n {k} (X : ext_n_module k)
    := single_to_sum_module nat ext_n_module X : module_V ext_n_algebra_module.

Definition to_ext_n_k {m n : nat} (eq : m = n)
    (X : module_V (ext_n_module m)) : module_V (ext_n_module n).
Proof.
    rewrite <- eq.
    exact X.
Defined.

Lemma to_ext_n_k_eq {m n : nat} (eq : m = n) :
    ∀ X : module_V (ext_n_module m), to_ext_n X = to_ext_n (to_ext_n_k eq X).
Proof.
    intros X.
    unfold to_ext_n_k.
    destruct eq; cbn.
    reflexivity.
Qed.

Lemma to_ext_n_eq : ∀ {k} a b AH BH, a = b →
    to_ext_n (k := k) [a|AH] = to_ext_n (k := k) [b|BH].
Proof.
    intros k a b AH BH eq.
    apply f_equal.
    apply set_type_eq; cbn.
    exact eq.
Qed.

Theorem to_ext_n_plus : ∀ {k} (u v : module_V (ext_n_module k)),
    to_ext_n (u + v) = to_ext_n u + to_ext_n v.
Proof.
    intros k u v.
    unfold to_ext_n.
    apply single_to_sum_module_plus.
Qed.

Theorem to_ext_n_scalar : ∀ {k} a (v : module_V (ext_n_module k)),
    to_ext_n (a · v) = a · to_ext_n v.
Proof.
    intros k a v.
    unfold to_ext_n.
    apply single_to_sum_module_scalar.
Qed.

Lemma vector_to_ext_n_in :
    ∀ v, subspace_set (ext_n_subspace 1) (φ v).
Proof.
    intros v.
    cbn.
    rewrite (span_linear_combination U).
    assert (linear_combination_set ((one (U := U), φ v) ː ulist_end)) as comb.
    {
        unfold linear_combination_set.
        rewrite ulist_image_add.
        rewrite ulist_image_end.
        apply ulist_unique_single.
    }
    exists [_|comb].
    split.
    -   unfold linear_combination; cbn.
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite scalar_id, plus_rid.
        reflexivity.
    -   unfold linear_list_in; cbn.
        rewrite ulist_prop_add; cbn.
        split; [>|apply ulist_prop_end].
        exists [v].
        split.
        +   rewrite list_image_single.
            rewrite list_prod_single.
            reflexivity.
        +   reflexivity.
Qed.

Definition vector_to_ext_n (v : module_V V) :=
    to_ext_n [φ v | vector_to_ext_n_in v] : module_V ext_n_algebra_module.

Theorem vector_to_ext_n_plus : ∀ u v,
    vector_to_ext_n (u + v) = vector_to_ext_n u + vector_to_ext_n v.
Proof.
    intros u v.
    unfold vector_to_ext_n.
    rewrite <- to_ext_n_plus.
    apply f_equal.
    unfold plus at 3; cbn.
    apply set_type_eq; cbn.
    apply module_homo_plus.
Qed.

Theorem vector_to_ext_n_scalar : ∀ a v,
    vector_to_ext_n (a · v) = a · vector_to_ext_n v.
Proof.
    intros a v.
    unfold vector_to_ext_n.
    rewrite <- to_ext_n_scalar.
    apply f_equal.
    unfold scalar_mult at 3; cbn.
    apply set_type_eq; cbn.
    apply module_homo_scalar.
Qed.

Lemma ext_n_algebra_mult_in : ∀ m n
    (a : ext_n_module m) (b : ext_n_module n),
    subspace_set (ext_n_subspace (m + n)) ([a|] * [b|]).
Proof.
    intros m n a b.
    destruct a as [a a_in].
    destruct b as [b b_in].
    cbn in *.
    rewrite (span_linear_combination U) in *.
    destruct a_in as [[u u_comb] [a_eq u_in]]; subst a.
    destruct b_in as [[v v_comb] [b_eq v_in]]; subst b.
    unfold linear_list_in in *; cbn in *.
    unfold linear_combination; cbn.
    clear u_comb v_comb.
    induction u as [|a u] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_lanni.
        apply linear_combination_of_zero.
    }
    rewrite ulist_prop_add in u_in.
    destruct u_in as [a_in u_in].
    specialize (IHu u_in).
    rewrite ulist_image_add, ulist_sum_add.
    rewrite rdist.
    apply linear_combination_of_plus; [>|exact IHu].
    clear u u_in IHu.
    induction v as [|b v] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_ranni.
        apply linear_combination_of_zero.
    }
    rewrite ulist_prop_add in v_in.
    destruct v_in as [b_in v_in].
    specialize (IHv v_in).
    rewrite ulist_image_add, ulist_sum_add.
    rewrite ldist.
    apply linear_combination_of_plus; [>|exact IHv].
    clear v v_in IHv.
    destruct a as [α a], b as [β b]; cbn in *.
    rewrite scalar_lmult, scalar_rmult.
    do 2 apply linear_combination_of_scalar.
    destruct a_in as [u [a_eq u_size]]; subst a.
    destruct b_in as [v [b_eq v_size]]; subst b.
    assert (linear_combination_set ((one (U := U), list_prod
        (list_image φ (u + v))) ː ulist_end)) as comb.
    {
        unfold linear_combination_set.
        rewrite ulist_image_add, ulist_image_end.
        cbn.
        apply ulist_unique_single.
    }
    exists [_|comb].
    split.
    -   unfold linear_combination.
        rewrite ulist_image_add, ulist_image_end.
        cbn.
        rewrite ulist_sum_add, ulist_sum_end.
        rewrite scalar_id, plus_rid.
        rewrite list_image_conc.
        rewrite list_prod_conc.
        reflexivity.
    -   unfold linear_list_in; cbn.
        rewrite ulist_prop_add.
        split; [>|apply ulist_prop_end].
        cbn.
        exists (u + v).
        split; [>reflexivity|].
        rewrite <- u_size, <- v_size.
        apply list_size_conc.
Qed.

Definition ext_n_mult_base i j
    (a : ext_n_module i) (b : ext_n_module j)
    := to_ext_n [[a|] * [b|] | ext_n_algebra_mult_in i j a b].

Theorem ext_n_mult_base_bilinear : ∀ i j, bilinear (ext_n_mult_base i j).
Proof.
    intros i j.
    repeat split.
    -   intros a u v.
        unfold ext_n_mult_base.
        unfold to_ext_n.
        rewrite <- single_to_sum_module_scalar.
        apply f_equal.
        unfold scalar_mult at 1; cbn.
        apply set_type_eq; cbn.
        apply scalar_lmult.
    -   intros a u v.
        unfold ext_n_mult_base.
        unfold to_ext_n.
        rewrite <- single_to_sum_module_scalar.
        apply f_equal.
        unfold scalar_mult at 1; cbn.
        apply set_type_eq; cbn.
        apply scalar_rmult.
    -   intros u v w.
        unfold ext_n_mult_base.
        unfold to_ext_n.
        rewrite <- single_to_sum_module_plus.
        apply f_equal.
        unfold plus at 3; cbn.
        apply set_type_eq; cbn.
        apply rdist.
    -   intros u v w.
        unfold ext_n_mult_base.
        unfold to_ext_n.
        rewrite <- single_to_sum_module_plus.
        apply f_equal.
        unfold plus at 3; cbn.
        apply set_type_eq; cbn.
        apply ldist.
Qed.
Instance ext_n_mult : Mult (module_V ext_n_algebra_module) := {
    mult A B := bilinear_extend (λ i j, [_|ext_n_mult_base_bilinear i j]) A B
}.

Local Instance ext_n_mult_ldist : Ldist (module_V ext_n_algebra_module).
Proof.
    split.
    apply bilinear_extend_ldist.
Qed.
Local Instance ext_n_mult_rdist : Rdist (module_V ext_n_algebra_module).
Proof.
    split.
    apply bilinear_extend_rdist.
Qed.
Local Instance ext_n_scalar_lmult
    : ScalarLMult U (module_V ext_n_algebra_module).
Proof.
    split.
    apply bilinear_extend_lscalar.
Qed.
Local Instance ext_n_scalar_rmult
    : ScalarRMult U (module_V ext_n_algebra_module).
Proof.
    split.
    apply bilinear_extend_rscalar.
Qed.

Theorem to_ext_n_mult : ∀ m n a b
    (ma : subspace_set (ext_n_subspace m) a)
    (nb : subspace_set (ext_n_subspace n) b),
    to_ext_n [a|ma] * to_ext_n [b|nb] =
    to_ext_n [a * b|ext_n_algebra_mult_in m n [a|ma] [b|nb]].
Proof.
    intros m n a b ma nb.
    unfold mult at 1; cbn.
    assert (of_grade m (to_ext_n [a|ma])) as ma'.
    {
        apply of_grade_ex.
        exists [a|ma].
        reflexivity.
    }
    assert (of_grade n (to_ext_n [b|nb])) as nb'.
    {
        apply of_grade_ex.
        exists [b|nb].
        reflexivity.
    }
    rewrite (bilinear_extend_homo _ _ _ _ _ ma' nb').
    unfold grade_to; cbn.
    unfold ext_n_mult_base.
    apply to_ext_n_eq.
    do 2 rewrite single_to_sum_module_base_eq.
    reflexivity.
Qed.

Lemma ext_n_one_in : subspace_set (ext_n_subspace 0) 1.
Proof.
    cbn.
    rewrite (span_linear_combination U).
    assert (linear_combination_set ((one (U := U),
        one (U := exterior_algebra V)) ː ulist_end)) as comb.
    {
        unfold linear_combination_set.
        rewrite ulist_image_add.
        rewrite ulist_image_end.
        apply ulist_unique_single.
    }
    exists [_|comb].
    split.
    -   unfold linear_combination; cbn.
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite scalar_id, plus_rid.
        reflexivity.
    -   unfold linear_list_in; cbn.
        rewrite ulist_prop_add; cbn.
        split; [>|apply ulist_prop_end].
        exists [].
        split.
        +   rewrite list_image_end.
            cbn.
            reflexivity.
        +   reflexivity.
Qed.

Local Instance ext_n_one : One (module_V ext_n_algebra_module) := {
    one := to_ext_n [1|ext_n_one_in]
}.

Lemma ext_n_list_in : ∀ l, subspace_set (ext_n_subspace (list_size l))
    (list_prod (list_image φ l)).
Proof.
    intros l.
    cbn.
    apply linear_span_sub.
    exists l.
    split; reflexivity.
Qed.

Lemma to_ext_n_list : ∀ l, to_ext_n [_|ext_n_list_in l] =
    list_prod (list_image vector_to_ext_n l).
Proof.
    intros l.
    induction l.
    -   unfold list_image; cbn.
        rewrite list_prod_end.
        unfold one; cbn.
        apply f_equal.
        apply set_type_eq; reflexivity.
    -   unfold list_image; fold (list_image vector_to_ext_n).
        rewrite list_prod_add.
        rewrite <- IHl.
        unfold vector_to_ext_n.
        rewrite to_ext_n_mult.
        apply f_equal.
        apply set_type_eq; reflexivity.
Qed.

Lemma ext_n_base_in : ∀ {n} (x : set_type (ext_n_base n)),
    subspace_set (ext_n_subspace n) [x|].
Proof.
    intros n x.
    apply linear_span_sub.
    exact [|x].
Qed.

Theorem ext_n_sum_grade : ∀ {n} x, of_grade n x →
    ∃ l : ulist (U * set_type (ext_n_base n)),
        x = ulist_sum (ulist_image
        (λ p, fst p · to_ext_n [_|ext_n_base_in (snd p)]) l).
Proof.
    intros n x nx.
    apply of_grade_ex in nx.
    destruct nx as [v x_eq]; subst x.
    change (single_to_sum_module nat ext_n_module v) with (to_ext_n v).
    assert (linear_combination_of (ext_n_base n) [v|]) as v_in.
    {
        rewrite <- (span_linear_combination U).
        exact [|v].
    }
    destruct v_in as [[l l_comb] [l_eq l_in]].
    assert (∃ l' : ulist (U * set_type (ext_n_base n)),
        [v|] = ulist_sum (ulist_image (λ p, fst p · [snd p|]) l')) as [l' l'_eq].
    {
        rewrite l_eq.
        unfold linear_combination; cbn.
        unfold linear_list_in in l_in; cbn in l_in.
        clear l_comb l_eq.
        induction l using ulist_induction.
        -   exists ulist_end.
            do 2 rewrite ulist_image_end.
            reflexivity.
        -   rewrite ulist_prop_add in l_in.
            destruct l_in as [a_in l_in].
            specialize (IHl l_in) as [l' l'_eq].
            destruct a as [a al]; cbn in *.
            exists ((a, [_|a_in]) ː l').
            do 2 rewrite ulist_image_add, ulist_sum_add; cbn.
            rewrite l'_eq.
            reflexivity.
    }
    clear l l_comb l_eq l_in.
    assert (∀ x : set_type (ext_n_base n), subspace_set (ext_n_subspace n) [x|]) as x_in.
    {
        intros x.
        cbn.
        apply linear_span_sub.
        exact [|x].
    }
    pose (x_transfer (x : set_type (ext_n_base n))
        := [_|x_in x] : module_V (ext_n_module n)).
    pose (l := ulist_image (λ x, fst x · x_transfer (snd x)) l').
    assert (v = ulist_sum l) as u_eq.
    {
        unfold l.
        apply set_type_eq.
        rewrite l'_eq.
        clear l.
        unfold x_transfer.
        clear x_transfer.
        clear l'_eq.
        induction l' using ulist_induction.
        -   do 2 rewrite ulist_image_end, ulist_sum_end.
            reflexivity.
        -   do 2 rewrite ulist_image_add, ulist_sum_add.
            unfold plus at 2; cbn.
            rewrite IHl'.
            apply rplus.
            unfold scalar_mult at 2; cbn.
            reflexivity.
    }
    subst v.
    exists l'.
    unfold l.
    clear l l'_eq.
    induction l' as [|a l] using ulist_induction.
    {
        do 2 rewrite ulist_image_end, ulist_sum_end.
        apply single_to_sum_module_zero.
    }
    do 2 rewrite ulist_image_add, ulist_sum_add.
    rewrite single_to_sum_module_plus.
    rewrite module_homo_plus.
    rewrite IHl.
    apply rplus.
    clear l IHl.
    destruct a as [a v]; cbn.
    rewrite single_to_sum_module_scalar.
    unfold grade_from; cbn.
    apply f_equal.
    unfold x_transfer.
    apply f_equal.
    apply set_type_eq; reflexivity.
Qed.

Theorem ext_n_sum : ∀ x, ∃ l : ulist (U * list (module_V V)),
    x = ulist_sum (ulist_image (λ p, fst p · list_prod
        (list_image vector_to_ext_n (snd p))) l).
Proof.
    intros x.
    induction x as [|u v] using grade_induction.
    {
        exists ulist_end.
        rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    }
    destruct IHv as [vl v_eq].
    destruct u as [u [i iu]].
    assert (∃ ul : ulist (U * list (module_V V)),
        u = ulist_sum (ulist_image (λ p, fst p · list_prod
            (list_image vector_to_ext_n (snd p))) ul)) as [ul u_eq].
    {
        clear v vl v_eq.
        pose proof (ext_n_sum_grade _ iu) as [l l_eq].
        subst u.
        clear iu.
        exists (ulist_image (λ x, (fst x, ex_val [|snd x])) l).
        rewrite ulist_image_comp; cbn.
        apply f_equal.
        apply f_equal2; [>|reflexivity].
        apply functional_ext.
        intros [a v]; cbn.
        apply f_equal.
        rewrite <- to_ext_n_list.
        clear l.
        rewrite_ex_val l [v_eq v_size].
        subst i.
        apply to_ext_n_eq.
        exact v_eq.
    }
    exists (ul + vl).
    subst u v.
    rewrite ulist_image_conc, ulist_sum_conc.
    reflexivity.
Qed.

Local Instance ext_n_mult_lid : MultLid (module_V ext_n_algebra_module).
Proof.
    split.
    intros a.
    pose proof (ext_n_sum a) as [l a_eq]; subst a.
    induction l as [|[a l] l'] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        apply mult_ranni.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ldist.
    rewrite IHl'.
    apply rplus.
    clear IHl' l'.
    rewrite scalar_rmult.
    apply f_equal.
    rewrite <- to_ext_n_list.
    unfold one; cbn.
    rewrite to_ext_n_mult.
    apply f_equal.
    apply set_type_eq; cbn.
    apply mult_lid.
Qed.

Local Instance ext_n_mult_rid : MultRid (module_V ext_n_algebra_module).
Proof.
    split.
    intros a.
    pose proof (ext_n_sum a) as [l a_eq]; subst a.
    induction l as [|[a l] l'] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        apply mult_lanni.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite rdist.
    rewrite IHl'.
    apply rplus.
    clear IHl' l'.
    rewrite scalar_lmult.
    apply f_equal.
    rewrite <- to_ext_n_list.
    unfold one; cbn.
    rewrite to_ext_n_mult.
    pose proof (plus_rid (list_size l)) as eq.
    rewrite (to_ext_n_k_eq eq).
    apply f_equal.
    apply set_type_eq; cbn.
    destruct eq; cbn.
    apply mult_rid.
Qed.

Local Instance ext_n_mult_assoc
    : MultAssoc (module_V ext_n_algebra_module).
Proof.
    split.
    intros a b c.
    pose proof (ext_n_sum a) as [l a_eq]; subst a.
    induction l as [|[α a] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite mult_lanni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    change (sum_module_type nat ext_n_module) with (module_V (ext_n_algebra_module)).
    do 3 rewrite rdist.
    rewrite IHl.
    apply rplus.
    clear l IHl.
    do 3 rewrite scalar_lmult.
    apply f_equal; clear α.
    pose proof (ext_n_sum b) as [l b_eq]; subst b.
    induction l as [|[α b] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_lanni.
        rewrite mult_ranni.
        rewrite mult_lanni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    change (sum_module_type nat ext_n_module) with (module_V (ext_n_algebra_module)).
    rewrite rdist.
    do 2 rewrite ldist.
    rewrite rdist.
    rewrite IHl.
    apply rplus.
    clear l IHl.
    rewrite scalar_lmult.
    do 2 rewrite scalar_rmult.
    rewrite scalar_lmult.
    apply f_equal; clear α.
    pose proof (ext_n_sum c) as [l c_eq]; subst c.
    induction l as [|[α c] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite mult_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    change (sum_module_type nat ext_n_module) with (module_V (ext_n_algebra_module)).
    do 3 rewrite ldist.
    rewrite IHl.
    apply rplus.
    clear l IHl.
    do 3 rewrite scalar_rmult.
    apply f_equal; clear α.
    do 3 rewrite <- to_ext_n_list.
    do 4 rewrite to_ext_n_mult.
    pose proof (plus_assoc (list_size a) (list_size b) (list_size c)) as eq.
    rewrite (to_ext_n_k_eq eq).
    apply f_equal.
    apply set_type_eq; cbn.
    destruct eq; cbn.
    apply mult_assoc.
Qed.

Theorem vector_to_ext_n_alternating :
    ∀ v, 0 = vector_to_ext_n v * vector_to_ext_n v.
Proof.
    intros v.
    unfold vector_to_ext_n.
    rewrite to_ext_n_mult.
    rewrite <- (single_to_sum_module_zero _ _ 2).
    apply to_ext_n_eq.
    apply ext_alternating.
Qed.

Definition ext_algebra_n := make_algebra
    U
    ext_n_algebra_module
    ext_n_mult
    ext_n_mult_ldist
    ext_n_mult_rdist
    ext_n_mult_assoc
    ext_n_one
    ext_n_mult_lid
    ext_n_mult_rid
    ext_n_scalar_lmult
    ext_n_scalar_rmult
: Algebra U.

Instance ext_n_grade_mult : GradedAlgebra ext_algebra_n nat.
Proof.
    split.
    intros u' v' i j iu vj.
    apply of_grade_ex in iu, vj.
    destruct iu as [u u_eq]; subst u'.
    destruct vj as [v v_eq]; subst v'.
    destruct u as [u u_in], v as [v v_in].
    rewrite to_ext_n_mult.
    pose proof (ext_n_algebra_mult_in _ _ [u|u_in] [v|v_in]) as uv_in.
    apply of_grade_ex.
    exists [_|uv_in].
    unfold grade_from; cbn.
    apply f_equal.
    apply set_type_eq; reflexivity.
Qed.

End ExteriorGrade.
