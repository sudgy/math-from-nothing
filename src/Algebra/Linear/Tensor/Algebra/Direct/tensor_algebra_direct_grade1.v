Require Import init.

Require Export tensor_algebra_direct_universal.
Require Import algebra_category.
Require Import linear_span.
Require Import linear_subspace.
Require Import linear_grade_sum.
Require Import linear_extend.
Require Import tensor_algebra_direct_inclusions.

Require Import nat.
Require Import list.
Require Import unordered_list.

Section TensorAlgebraGrade.

Context {F : CRingObj} (V : ModuleObj F).
Let U := cring_U F.

Section Single.

Variable n : nat.

Definition tensor_n_base (X : algebra_V (tensor_algebra V)) :=
    ∃ l, X = list_prod (list_image l vector_to_tensor) ∧ list_size l = n.

Definition tensor_n_subspace := linear_span_subspace (cring_U F) tensor_n_base.

Definition tensor_n_module := make_module
    F
    (set_type (subspace_set tensor_n_subspace))
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

Definition tensor_n_algebra_module := grade_sum nat tensor_n_module.

Definition tensor_n_grade := grade_sum_grade nat tensor_n_module
    : GradedSpace U (module_V tensor_n_algebra_module).
Local Existing Instances tensor_n_grade.

Definition to_tensor_n {k} (X : module_V (tensor_n_module k))
    := single_to_grade_sum nat tensor_n_module X
    : module_V tensor_n_algebra_module.

Definition to_tensor_n_k {m n : nat} (eq : m = n)
    (X : module_V (tensor_n_module m)) : module_V (tensor_n_module n).
Proof.
    rewrite <- eq.
    exact X.
Defined.

Lemma to_tensor_n_k_eq {m n : nat} (eq : m = n) :
    ∀ X : module_V (tensor_n_module m), to_tensor_n X =
    to_tensor_n (to_tensor_n_k eq X).
Proof.
    intros X.
    unfold to_tensor_n_k.
    destruct eq; cbn.
    reflexivity.
Qed.

Lemma to_tensor_n_eq : ∀ {k} a b AH BH, a = b →
    to_tensor_n (k := k) [a|AH] = to_tensor_n (k := k) [b|BH].
Proof.
    intros k a b AH BH eq.
    apply f_equal.
    apply set_type_eq; cbn.
    exact eq.
Qed.

Theorem to_tensor_n_plus : ∀ {k} (u v : module_V (tensor_n_module k)),
    to_tensor_n (u + v) = to_tensor_n u + to_tensor_n v.
Proof.
    intros k u v.
    unfold to_tensor_n.
    apply single_to_grade_sum_plus.
Qed.

Theorem to_tensor_n_scalar : ∀ {k} a (v : module_V (tensor_n_module k)),
    to_tensor_n (a · v) = a · to_tensor_n v.
Proof.
    intros k a v.
    unfold to_tensor_n.
    apply single_to_grade_sum_scalar.
Qed.

Lemma vector_to_tensor_n_in :
    ∀ v, subspace_set (tensor_n_subspace 1) (vector_to_tensor v).
Proof.
    intros v.
    cbn.
    rewrite (span_linear_combination U).
    assert (linear_combination_set
        ((one (U := U), vector_to_tensor v) ::: ulist_end)) as comb.
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
            cbn.
            rewrite mult_rid.
            reflexivity.
        +   reflexivity.
Qed.

Definition vector_to_tensor_n (v : module_V V) :=
    to_tensor_n [vector_to_tensor v | vector_to_tensor_n_in v]
    : module_V tensor_n_algebra_module.

Theorem vector_to_tensor_n_plus : ∀ u v,
    vector_to_tensor_n (u + v) = vector_to_tensor_n u + vector_to_tensor_n v.
Proof.
    intros u v.
    unfold vector_to_tensor_n.
    rewrite <- to_tensor_n_plus.
    apply f_equal.
    unfold plus at 3; cbn.
    apply set_type_eq; cbn.
    apply vector_to_tensor_plus.
Qed.

Theorem vector_to_tensor_n_scalar : ∀ a v,
    vector_to_tensor_n (a · v) = a · vector_to_tensor_n v.
Proof.
    intros a v.
    unfold vector_to_tensor_n.
    rewrite <- to_tensor_n_scalar.
    apply f_equal.
    unfold scalar_mult at 3; cbn.
    apply set_type_eq; cbn.
    apply vector_to_tensor_scalar.
Qed.

Lemma tensor_n_algebra_mult_in : ∀ m n a b,
    subspace_set (tensor_n_subspace m) a → subspace_set (tensor_n_subspace n) b
    → subspace_set (tensor_n_subspace (m + n)) (a * b).
Proof.
    intros m n a b a_in b_in.
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
        (list_image (u ++ v) vector_to_tensor)) ::: ulist_end)) as comb.
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
        rewrite list_prod_mult.
        reflexivity.
    -   unfold linear_list_in; cbn.
        rewrite ulist_prop_add.
        split; [>|apply ulist_prop_end].
        cbn.
        exists (u ++ v).
        split; [>reflexivity|].
        rewrite <- u_size, <- v_size.
        apply list_size_plus.
Qed.

Definition tensor_n_mult_base i j
    (a : module_V tensor_n_algebra_module)
    (b : module_V tensor_n_algebra_module)
    (ai : of_grade i a) (bj : of_grade j b)
    := to_tensor_n
        [[ex_val ai|] * [ex_val bj|] |
            tensor_n_algebra_mult_in i j [ex_val ai|] [ex_val bj|]
                [|ex_val ai] [|ex_val bj]].

Lemma tensor_n_mult_tm : ∀ i j a b AH BH,
    tensor_n_mult_base i j (to_tensor_n a) (to_tensor_n b) AH BH
    = to_tensor_n [[a|] * [b|] |
        tensor_n_algebra_mult_in i j [a|] [b|] [|a] [|b]].
Proof.
    intros i j a b AH BH.
    unfold tensor_n_mult_base.
    rewrite_ex_val a' a'_eq.
    rewrite_ex_val b' b'_eq.
    unfold to_tensor_n in a'_eq, b'_eq.
    apply single_to_grade_sum_eq in a'_eq, b'_eq.
    subst a' b'.
    reflexivity.
Qed.

Theorem tensor_n_mult_base_ldist :
    bilinear_extend_ldist_base tensor_n_mult_base.
Proof.
    intros u' v' w' i j iu jv jw.
    pose proof iu as [u u_eq].
    pose proof jv as [v v_eq].
    pose proof jw as [w w_eq].
    change (single_to_grade_sum nat tensor_n_module)
        with (to_tensor_n (k := i)) in u_eq.
    change (single_to_grade_sum nat tensor_n_module)
        with (to_tensor_n (k := j)) in v_eq, w_eq.
    subst u' v' w'.
    assert (of_grade j (to_tensor_n (v + w))) as vwj.
    {
        unfold to_tensor_n.
        rewrite single_to_grade_sum_plus.
        apply of_grade_plus; assumption.
    }
    rewrite (bilinear_extend_base_req _ _ _ _ _ _ _ _ vwj)
        by (symmetry; apply single_to_grade_sum_plus).
    do 3 rewrite tensor_n_mult_tm.
    unfold to_tensor_n.
    rewrite <- single_to_grade_sum_plus.
    apply f_equal.
    unfold plus at 6; cbn.
    apply set_type_eq; cbn.
    apply ldist.
Qed.

Theorem tensor_n_mult_base_rdist :
    bilinear_extend_rdist_base tensor_n_mult_base.
Proof.
    intros u' v' w' i j iu iv jw.
    pose proof iu as [u u_eq].
    pose proof iv as [v v_eq].
    pose proof jw as [w w_eq].
    change (single_to_grade_sum nat tensor_n_module)
        with (to_tensor_n (k := i)) in u_eq, v_eq.
    change (single_to_grade_sum nat tensor_n_module)
        with (to_tensor_n (k := j)) in w_eq.
    subst u' v' w'.
    assert (of_grade i (to_tensor_n (u + v))) as uvi.
    {
        unfold to_tensor_n.
        rewrite single_to_grade_sum_plus.
        apply of_grade_plus; assumption.
    }
    rewrite (bilinear_extend_base_leq _ _ _ _ _ _ _ uvi)
        by (symmetry; apply single_to_grade_sum_plus).
    do 3 rewrite tensor_n_mult_tm.
    unfold to_tensor_n.
    rewrite <- single_to_grade_sum_plus.
    apply f_equal.
    unfold plus at 6; cbn.
    apply set_type_eq; cbn.
    apply rdist.
Qed.

Theorem tensor_n_mult_base_lscalar :
    bilinear_extend_lscalar_base tensor_n_mult_base.
Proof.
    intros a u' v' i j iu jv.
    pose proof iu as [u u_eq].
    pose proof jv as [v v_eq].
    change (single_to_grade_sum nat tensor_n_module)
        with (to_tensor_n (k := i)) in u_eq.
    change (single_to_grade_sum nat tensor_n_module)
        with (to_tensor_n (k := j)) in v_eq.
    subst u' v'.
    assert (of_grade i (to_tensor_n (a · u))) as aui.
    {
        unfold to_tensor_n.
        rewrite single_to_grade_sum_scalar.
        apply of_grade_scalar; assumption.
    }
    rewrite (bilinear_extend_base_leq _ _ _ _ _ _ _ aui)
        by (symmetry; apply single_to_grade_sum_scalar).
    do 2 rewrite tensor_n_mult_tm.
    unfold to_tensor_n.
    rewrite <- single_to_grade_sum_scalar.
    apply f_equal.
    unfold scalar_mult at 4; cbn.
    apply set_type_eq; cbn.
    apply scalar_lmult.
Qed.

Theorem tensor_n_mult_base_rscalar :
    bilinear_extend_rscalar_base tensor_n_mult_base.
Proof.
    intros a u' v' i j iu jv.
    pose proof iu as [u u_eq].
    pose proof jv as [v v_eq].
    change (single_to_grade_sum nat tensor_n_module)
        with (to_tensor_n (k := i)) in u_eq.
    change (single_to_grade_sum nat tensor_n_module)
        with (to_tensor_n (k := j)) in v_eq.
    subst u' v'.
    assert (of_grade j (to_tensor_n (a · v))) as avj.
    {
        unfold to_tensor_n.
        rewrite single_to_grade_sum_scalar.
        apply of_grade_scalar; assumption.
    }
    rewrite (bilinear_extend_base_req _ _ _ _ _ _ _ _ avj)
        by (symmetry; apply single_to_grade_sum_scalar).
    do 2 rewrite tensor_n_mult_tm.
    unfold to_tensor_n.
    rewrite <- single_to_grade_sum_scalar.
    apply f_equal.
    unfold scalar_mult at 4; cbn.
    apply set_type_eq; cbn.
    apply scalar_rmult.
Qed.

Instance tensor_n_mult : Mult (module_V tensor_n_algebra_module) := {
    mult A B := bilinear_extend tensor_n_mult_base A B
}.

Local Instance tensor_n_mult_ldist : Ldist (module_V tensor_n_algebra_module).
Proof.
    split.
    apply bilinear_extend_ldist.
    -   apply tensor_n_mult_base_ldist.
    -   apply tensor_n_mult_base_rscalar.
Qed.
Local Instance tensor_n_mult_rdist : Rdist (module_V tensor_n_algebra_module).
Proof.
    split.
    apply bilinear_extend_rdist.
    -   apply tensor_n_mult_base_rdist.
    -   apply tensor_n_mult_base_lscalar.
Qed.
Local Instance tensor_n_scalar_lmult
    : ScalarLMult U (module_V tensor_n_algebra_module).
Proof.
    split.
    apply bilinear_extend_lscalar.
    -   apply tensor_n_mult_base_rdist.
    -   apply tensor_n_mult_base_lscalar.
Qed.
Local Instance tensor_n_scalar_rmult
    : ScalarRMult U (module_V tensor_n_algebra_module).
Proof.
    split.
    apply bilinear_extend_rscalar.
    -   apply tensor_n_mult_base_ldist.
    -   apply tensor_n_mult_base_rscalar.
Qed.

Theorem to_tensor_n_mult : ∀ m n a b
    (ma : subspace_set (tensor_n_subspace m) a)
    (nb : subspace_set (tensor_n_subspace n) b),
    to_tensor_n [a|ma] * to_tensor_n [b|nb] =
    to_tensor_n [a * b|tensor_n_algebra_mult_in m n a b ma nb].
Proof.
    intros m n a b ma nb.
    unfold mult at 1; cbn.
    assert (of_grade (H9 := tensor_n_grade) m (to_tensor_n [a|ma])) as ma'.
    {
        exists [a|ma].
        reflexivity.
    }
    assert (of_grade (H9 := tensor_n_grade) n (to_tensor_n [b|nb])) as nb'.
    {
        exists [b|nb].
        reflexivity.
    }
    rewrite (bilinear_extend_homo _
        tensor_n_mult_base_ldist tensor_n_mult_base_rdist
        tensor_n_mult_base_lscalar tensor_n_mult_base_rscalar _ _ _ _ ma' nb').
    rewrite tensor_n_mult_tm; cbn.
    reflexivity.
Qed.

Instance tensor_n_grade_mult : GradedAlgebraObj U (module_V tensor_n_algebra_module).
Proof.
    split.
    intros u' v' i j iu vj.
    destruct iu as [u u_eq]; subst u'.
    destruct vj as [v v_eq]; subst v'.
    destruct u as [u u_in], v as [v v_in].
    rewrite to_tensor_n_mult.
    pose proof (tensor_n_algebra_mult_in _ _ _ _ u_in v_in) as uv_in.
    exists [_|uv_in].
    apply f_equal.
    apply set_type_eq; reflexivity.
Qed.

Lemma tensor_n_one_in : subspace_set (tensor_n_subspace 0) 1.
Proof.
    cbn.
    rewrite (span_linear_combination U).
    assert (linear_combination_set ((one (U := U),
        one (U := algebra_V (tensor_algebra V))) ::: ulist_end)) as comb.
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

Local Instance tensor_n_one : One (module_V tensor_n_algebra_module) := {
    one := to_tensor_n [1|tensor_n_one_in]
}.

Lemma tensor_n_list_in : ∀ l, subspace_set (tensor_n_subspace (list_size l))
    (list_prod (list_image l vector_to_tensor)).
Proof.
    intros l.
    cbn.
    apply linear_span_sub.
    exists l.
    split; reflexivity.
Qed.

Lemma to_tensor_n_list : ∀ l, to_tensor_n [_|tensor_n_list_in l] =
    list_prod (list_image l vector_to_tensor_n).
Proof.
    intros l.
    induction l.
    -   unfold list_image; cbn.
        unfold one at 2; cbn.
        apply f_equal.
        apply set_type_eq; reflexivity.
    -   unfold list_image; fold list_image.
        cbn.
        rewrite <- IHl.
        unfold vector_to_tensor_n.
        rewrite to_tensor_n_mult.
        apply f_equal.
        apply set_type_eq; reflexivity.
Qed.

Lemma tensor_n_base_in : ∀ {n} (x : set_type (tensor_n_base n)),
    subspace_set (tensor_n_subspace n) [x|].
Proof.
    intros n x.
    apply linear_span_sub.
    exact [|x].
Qed.

Theorem tensor_n_sum_grade : ∀ {n} x, of_grade n x →
    ∃ l : ulist (cring_U F * set_type (tensor_n_base n)),
        x = ulist_sum (ulist_image l
        (λ p, fst p · to_tensor_n [_|tensor_n_base_in (snd p)])).
Proof.
    intros n x nx.
    destruct nx as [v x_eq]; subst x.
    change (single_to_grade_sum nat tensor_n_module v) with (to_tensor_n v).
    assert (linear_combination_of (tensor_n_base n) [v|]) as v_in.
    {
        rewrite <- (span_linear_combination U).
        exact [|v].
    }
    destruct v_in as [[l l_comb] [l_eq l_in]].
    assert (∃ l' : ulist (cring_U F * set_type (tensor_n_base n)),
        [v|] = ulist_sum (ulist_image l' (λ p, fst p · [snd p|]))) as [l' l'_eq].
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
            exists ((a, [_|a_in]) ::: l').
            do 2 rewrite ulist_image_add, ulist_sum_add; cbn.
            rewrite l'_eq.
            reflexivity.
    }
    clear l l_comb l_eq l_in.
    assert (∀ x : set_type (tensor_n_base n), subspace_set (tensor_n_subspace n) [x|]) as x_in.
    {
        intros x.
        cbn.
        apply linear_span_sub.
        exact [|x].
    }
    pose (x_transfer (x : set_type (tensor_n_base n))
        := [_|x_in x] : module_V (tensor_n_module n)).
    pose (l := ulist_image l' (λ x, fst x · x_transfer (snd x))).
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
        apply single_to_grade_sum_zero.
    }
    do 2 rewrite ulist_image_add, ulist_sum_add.
    rewrite to_tensor_n_plus.
    rewrite IHl.
    apply rplus.
    clear l IHl.
    destruct a as [a v]; cbn.
    rewrite to_tensor_n_scalar.
    apply f_equal.
    unfold x_transfer.
    apply f_equal.
    apply set_type_eq; reflexivity.
Qed.

Theorem tensor_n_sum : ∀ x, ∃ l : ulist (U * list (module_V V)),
    x = ulist_sum (ulist_image l (λ p, fst p · list_prod
        (list_image (snd p) vector_to_tensor_n))).
Proof.
    intros x.
    induction x as [|u v i iu iv IHx] using grade_induction.
    {
        exists ulist_end.
        rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    }
    destruct IHx as [vl v_eq].
    assert (∃ ul : ulist (U * list (module_V V)),
        u = ulist_sum (ulist_image ul (λ p, fst p · list_prod
            (list_image (snd p) vector_to_tensor_n)))) as [ul u_eq].
    {
        clear v iv vl v_eq.
        pose proof (tensor_n_sum_grade _ iu) as [l l_eq].
        subst u.
        clear iu.
        exists (ulist_image l (λ x, (fst x, ex_val [|snd x]))).
        rewrite ulist_image_comp; cbn.
        do 2 apply f_equal.
        apply functional_ext.
        intros [a v]; cbn.
        apply f_equal.
        rewrite <- to_tensor_n_list.
        clear l.
        rewrite_ex_val l [v_eq v_size].
        subst i.
        apply to_tensor_n_eq.
        exact v_eq.
    }
    exists (ul +++ vl).
    subst u v.
    rewrite ulist_image_conc, ulist_sum_plus.
    reflexivity.
Qed.

Local Instance tensor_n_mult_lid : MultLid (module_V tensor_n_algebra_module).
Proof.
    split.
    intros a.
    pose proof (tensor_n_sum a) as [l a_eq]; subst a.
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
    rewrite <- to_tensor_n_list.
    unfold one; cbn.
    rewrite to_tensor_n_mult.
    apply f_equal.
    apply set_type_eq; cbn.
    apply mult_lid.
Qed.

Local Instance tensor_n_mult_rid : MultRid (module_V tensor_n_algebra_module).
Proof.
    split.
    intros a.
    pose proof (tensor_n_sum a) as [l a_eq]; subst a.
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
    rewrite <- to_tensor_n_list.
    unfold one; cbn.
    rewrite to_tensor_n_mult.
    pose proof (plus_rid (list_size l)) as eq.
    rewrite (to_tensor_n_k_eq eq).
    apply f_equal.
    apply set_type_eq; cbn.
    destruct eq; cbn.
    apply mult_rid.
Qed.

Local Instance tensor_n_mult_assoc
    : MultAssoc (module_V tensor_n_algebra_module).
Proof.
    split.
    intros a b c.
    pose proof (tensor_n_sum a) as [l a_eq]; subst a.
    induction l as [|[α a] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite mult_lanni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    change (grade_sum_type nat tensor_n_module) with (module_V (tensor_n_algebra_module)).
    do 3 rewrite rdist.
    rewrite IHl.
    apply rplus.
    clear l IHl.
    do 3 rewrite scalar_lmult.
    apply f_equal; clear α.
    pose proof (tensor_n_sum b) as [l b_eq]; subst b.
    induction l as [|[α b] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_lanni.
        rewrite mult_ranni.
        rewrite mult_lanni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    change (grade_sum_type nat tensor_n_module) with (module_V (tensor_n_algebra_module)).
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
    pose proof (tensor_n_sum c) as [l c_eq]; subst c.
    induction l as [|[α c] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite mult_ranni.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    change (grade_sum_type nat tensor_n_module) with (module_V (tensor_n_algebra_module)).
    do 3 rewrite ldist.
    rewrite IHl.
    apply rplus.
    clear l IHl.
    do 3 rewrite scalar_rmult.
    apply f_equal; clear α.
    do 3 rewrite <- to_tensor_n_list.
    do 4 rewrite to_tensor_n_mult.
    pose proof (plus_assoc (list_size a) (list_size b) (list_size c)) as eq.
    rewrite (to_tensor_n_k_eq eq).
    apply f_equal.
    apply set_type_eq; cbn.
    destruct eq; cbn.
    apply mult_assoc.
Qed.

Definition tensor_algebra_n := make_algebra
    F
    tensor_n_algebra_module
    tensor_n_mult
    tensor_n_mult_ldist
    tensor_n_mult_rdist
    tensor_n_mult_assoc
    tensor_n_one
    tensor_n_mult_lid
    tensor_n_mult_rid
    tensor_n_scalar_lmult
    tensor_n_scalar_rmult
.

End TensorAlgebraGrade.
