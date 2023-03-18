Require Import init.

Require Export linear_base.
Require Export linear_grade.
Require Import module_category.
Require Import linear_subspace.

Require Import set.
Require Import nat.
Require Import unordered_list.

Section LinearGradeSum.

Context {R : CRingObj}.
Variable (I : Type).
Variable (V : I → ModuleObj R).

Let U := cring_U R.
Let UP := cring_plus R.
Let UM := cring_mult R.
Let UO := cring_one R.

Local Existing Instances UP UM UO.

Let VP k := module_plus (V k).
Let VZ k := module_zero (V k).
Let VN k := module_neg (V k).
Let VPC k := module_plus_comm (V k).
Let VPA k := module_plus_assoc (V k).
Let VPZ k := module_plus_lid (V k).
Let VPN k := module_plus_linv (V k).
Let VS k := module_scalar (V k).
Let VSC k := module_scalar_comp (V k).
Let VSE k := module_scalar_id (V k).
Let VSL k := module_scalar_ldist (V k).
Let VSR k := module_scalar_rdist (V k).

Local Existing Instances VP VZ VN VPC VPA VPZ VPN VS VSC VSE VSL VSR.

Definition grade_sum_base := (∀ k, module_V (V k)).
Definition grade_sum_finite (A : grade_sum_base) :=
    simple_finite (set_type (λ k, 0 ≠ A k)).
Definition grade_sum_type := set_type grade_sum_finite.

Definition single_to_grade_sum_base {k} (A : module_V (V k)) : grade_sum_base.
    intros n.
    classic_case (k = n).
    -   subst k.
        exact A.
    -   exact 0.
Defined.

Lemma single_to_grade_sum_finite {k} : ∀ A : module_V (V k),
    grade_sum_finite (single_to_grade_sum_base A).
Proof.
    intros A.
    exists 1.
    exists (λ _, [0|nat_one_pos]).
    split.
    intros [a a_neq] [b b_neq] eq; clear eq.
    unfold single_to_grade_sum_base in *.
    apply set_type_eq; cbn.
    classic_case (k = a) as [ak|ak];
    classic_case (k = b) as [bk|bk].
    1: subst; reflexivity.
    all: contradiction.
Qed.

Definition single_to_grade_sum {k} (A : module_V (V k))
    := [_|single_to_grade_sum_finite A].

Theorem single_to_grade_sum_eq : ∀ k, ∀ (A B : module_V (V k)),
    single_to_grade_sum A = single_to_grade_sum B → A = B.
Proof.
    intros k A B eq.
    apply set_type_eq in eq.
    assert (∀ x, [single_to_grade_sum A|] x = [single_to_grade_sum B|] x) as eq2.
    {
        rewrite eq.
        reflexivity.
    }
    clear eq.
    unfold single_to_grade_sum, single_to_grade_sum_base in eq2.
    cbn in eq2.
    specialize (eq2 k).
    destruct (sem (k = k)) as [eq|neq]; try contradiction.
    destruct eq; cbn in eq2.
    exact eq2.
Qed.

Lemma grade_sum_plus_finite : ∀ A B : grade_sum_type,
    grade_sum_finite (λ k, [A|] k + [B|] k).
Proof.
    intros [A A_fin] [B B_fin]; cbn.
    apply (simple_finite_trans _ _ (simple_finite_sum _ _ A_fin B_fin)).
    assert (∀ (n : set_type (λ k, 0 ≠ A k + B k)), {0 ≠ A [n|]} + {0 ≠ B [n|]})
        as n_in.
    {
        intros [n n_neq]; cbn.
        classic_case (0 = A n) as [Anz|Anz].
        -   right.
            rewrite <- Anz in n_neq.
            rewrite plus_lid in n_neq.
            exact n_neq.
        -   left; exact Anz.
    }
    exists (λ n, match (n_in n) with
        | strong_or_left  H => inl [[n|]|H]
        | strong_or_right H => inr [[n|]|H]
    end).
    split.
    intros a b eq.
    destruct (n_in a) as [neq1|neq1]; destruct (n_in b) as [neq2|neq2].
    all: inversion eq as [eq2].
    all: apply set_type_eq; exact eq2.
Qed.

Instance grade_sum_plus : Plus grade_sum_type := {
    plus A B := [_|grade_sum_plus_finite A B]
}.

Program Instance grade_sum_plus_comm : PlusComm grade_sum_type.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_comm.
Qed.

Program Instance grade_sum_plus_assoc : PlusAssoc grade_sum_type.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_assoc.
Qed.

Lemma grade_sum_zero_finite : grade_sum_finite (λ k, 0).
Proof.
    unfold grade_sum_finite.
    exists 0.
    exists (λ x : set_type (λ k : I, (zero (U := module_V (V k))) ≠ 0),
        False_rect _ ([|x] Logic.eq_refl)).
    split.
    intros [a neq].
    contradiction.
Qed.

Instance grade_sum_zero : Zero grade_sum_type := {
    zero := [_|grade_sum_zero_finite]
}.

Program Instance grade_sum_plus_lid : PlusLid grade_sum_type.
Next Obligation.
    unfold plus, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_lid.
Qed.

Lemma grade_sum_neg_finite : ∀ A : grade_sum_type, grade_sum_finite (λ k, -[A|] k).
Proof.
    intros [A A_fin]; cbn.
    apply (simple_finite_trans _ _ A_fin).
    assert (∀ (n : set_type (λ k, 0 ≠ - A k)), 0 ≠ A [n|]) as n_in.
    {
        intros [n n_neq]; cbn.
        intros eq.
        rewrite <- eq in n_neq.
        rewrite neg_zero in n_neq.
        contradiction.
    }
    exists (λ n, [[n|]|n_in n]).
    split.
    intros a b eq.
    apply set_type_eq in eq; cbn in eq.
    apply set_type_eq in eq; cbn in eq.
    exact eq.
Qed.

Instance grade_sum_neg : Neg grade_sum_type := {
    neg A := [_|grade_sum_neg_finite A]
}.

Program Instance grade_sum_plus_linv : PlusLinv grade_sum_type.
Next Obligation.
    unfold plus, neg, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_linv.
Qed.

Theorem single_to_grade_sum_plus : ∀ k (A B : module_V (V k)),
    single_to_grade_sum (A + B) =
    single_to_grade_sum A + single_to_grade_sum B.
Proof.
    intros k A B.
    apply set_type_eq; cbn.
    apply functional_ext; intros x.
    unfold plus at 2; cbn.
    unfold single_to_grade_sum_base.
    destruct (sem (k = x)) as [eq|neq].
    2: symmetry; apply plus_rid.
    destruct eq; cbn.
    reflexivity.
Qed.

Lemma grade_sum_scalar_finite : ∀ α (A : grade_sum_type),
    grade_sum_finite (λ k, α · [A|] k).
Proof.
    intros α [A A_fin]; cbn.
    apply (simple_finite_trans _ _ A_fin).
    assert (∀ (n : set_type (λ k, 0 ≠ α · A k)), 0 ≠ A [n|]) as n_in.
    {
        intros [n n_neq]; cbn.
        intros eq.
        rewrite <- eq in n_neq.
        rewrite scalar_ranni in n_neq.
        contradiction.
    }
    exists (λ n, [[n|]|n_in n]).
    split.
    intros a b eq.
    apply set_type_eq in eq; cbn in eq.
    apply set_type_eq in eq; cbn in eq.
    exact eq.
Qed.

Instance grade_sum_scalar_mult : ScalarMult U grade_sum_type := {
    scalar_mult α A := [_|grade_sum_scalar_finite α A]
}.

Program Instance grade_sum_scalar_comp : ScalarComp U grade_sum_type.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_comp.
Qed.

Program Instance grade_sum_scalar_id : ScalarId U grade_sum_type.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_id.
Qed.

Program Instance grade_sum_scalar_ldist : ScalarLdist U grade_sum_type.
Next Obligation.
    unfold plus, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_ldist.
Qed.

Program Instance grade_sum_scalar_rdist : ScalarRdist U grade_sum_type.
Next Obligation.
    unfold plus at 2, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_rdist.
Qed.

Theorem single_to_grade_sum_scalar : ∀ k α (A : module_V (V k)),
    single_to_grade_sum (α · A) = α · single_to_grade_sum A.
Proof.
    intros k A B.
    apply set_type_eq; cbn.
    apply functional_ext; intros x.
    unfold scalar_mult at 2; cbn.
    unfold single_to_grade_sum_base.
    destruct (sem (k = x)) as [eq|neq].
    -   destruct eq; cbn.
        reflexivity.
    -   rewrite scalar_ranni.
        reflexivity.
Qed.

Lemma single_to_grade_sum_zero : ∀ k, (single_to_grade_sum (k := k) 0) = 0.
Proof.
    intros k.
    apply set_type_eq; cbn.
    unfold single_to_grade_sum_base.
    apply functional_ext.
    intros x.
    destruct (sem (k = x)) as [eq|neq].
    -   destruct eq; cbn.
        reflexivity.
    -   reflexivity.
Qed.

Lemma grade_sum_list_sum_k : ∀ (al : ulist (grade_sum_type)) k,
    [ulist_sum al|] k = ulist_sum (ulist_image (λ a, [a|] k) al).
Proof.
    intros al k.
    induction al using ulist_induction.
    -   rewrite ulist_image_end.
        do 2 rewrite ulist_sum_end.
        reflexivity.
    -   rewrite ulist_image_add.
        do 2 rewrite ulist_sum_add.
        unfold plus at 1; cbn.
        rewrite IHal.
        reflexivity.
Qed.

Definition grade_sum_subspace_set n (v : grade_sum_type)
    := ∃ v' : module_V (V n), single_to_grade_sum v' = v.

Lemma grade_sum_subspace_zero : ∀ n, grade_sum_subspace_set n 0.
Proof.
    intros n.
    exists 0.
    apply single_to_grade_sum_zero.
Qed.

Lemma grade_sum_subspace_plus : ∀ n u v,
    grade_sum_subspace_set n u → grade_sum_subspace_set n v →
    grade_sum_subspace_set n (u + v).
Proof.
    intros n u' v' [u u_eq] [v v_eq]; subst u' v'.
    exists (u + v).
    apply single_to_grade_sum_plus.
Qed.

Lemma grade_sum_subspace_scalar : ∀ n a v,
    grade_sum_subspace_set n v → grade_sum_subspace_set n (a · v).
Proof.
    intros n a v' [v v_eq]; subst v'.
    exists (a · v).
    apply single_to_grade_sum_scalar.
Qed.

Definition grade_sum_subspace n := make_subspace
    (grade_sum_subspace_set n)
    (grade_sum_subspace_zero n)
    (grade_sum_subspace_plus n)
    (grade_sum_subspace_scalar n).

Program Instance grade_sum_grade : GradedSpace U grade_sum_type := {
    grade_I := I;
    grade_subspace n := grade_sum_subspace n;
}.
Next Obligation.
    rename H into neq.
    destruct H0 as [v1 v1_eq].
    destruct H1 as [v2 v2_eq].
    rewrite <- v2_eq in v1_eq.
    unfold single_to_grade_sum_base in v1_eq; cbn in v1_eq.
    apply set_type_eq in v1_eq; cbn in v1_eq.
    unfold single_to_grade_sum_base in v1_eq.
    (* I don't know why Coq is being so finicky about this *)
    assert (∀ n,
           match sem (i = n) with
           | strong_or_left a =>
               Logic.eq_rect_r (λ k : I, module_V (V k) → module_V (V n))
                 (λ A : module_V (V n), A) a v1
           | strong_or_right _ => 0
           end =
           match sem (j = n) with
           | strong_or_left a =>
               Logic.eq_rect_r (λ k : I, module_V (V k) → module_V (V n))
                 (λ A : module_V (V n), A) a v2
           | strong_or_right _ => 0
           end) as v1_eq'.
    {
        intros m.
        change
            match sem (i = m) with
            | strong_or_left a =>
                Logic.eq_rect_r (λ k : I, module_V (V k) → module_V (V m))
                  (λ A : module_V (V m), A) a v1
            | strong_or_right _ => 0
            end
            with
            ((λ n, match sem (i = n) with
            | strong_or_left a =>
                Logic.eq_rect_r (λ k : I, module_V (V k) → module_V (V n))
                  (λ A : module_V (V n), A) a v1
            | strong_or_right _ => 0
            end) m).
        rewrite v1_eq.
        reflexivity.
    }
    clear v1_eq.
    specialize (v1_eq' j).
    destruct (sem (i = j)) as [ij_eq|ij_neq];
    destruct (sem (j = j)) as [jj_eq|jj_neq];
    try contradiction.
    destruct jj_eq; cbn in v1_eq'.
    subst v2.
    rewrite single_to_grade_sum_zero in v2_eq.
    exact v2_eq.
Qed.
Next Obligation.
    pose proof (simple_finite_bij _ [|v]) as [n [f f_bij]].
    revert v f f_bij.
    nat_induction n; intros.
    {
        exists ulist_end.
        split.
        -   rewrite ulist_image_end, ulist_sum_end.
            apply set_type_eq.
            apply functional_ext.
            intros k.
            symmetry.
            classic_contradiction contr.
            contradiction (nat_lt_0_false (f [k|contr])).
        -   apply ulist_prop_end.
    }
    pose proof (sur f [n|nat_lt_suc n]) as [x x_eq].
    pose (v' (i : I) := If [x|] = i then 0 else [v|] i).
    assert (∀ k : set_type (λ k, 0 ≠ v' k), 0 ≠ [v|] [k|]) as f_in.
    {
        intros [k k_neq].
        unfold v' in k_neq.
        cbn.
        case_if [eq|neq].
        -   contradiction.
        -   exact k_neq.
    }
    assert (grade_sum_finite v') as v'_fin.
    {
        apply (simple_finite_trans _ _ [|v]).
        exists (λ k, [[k|]|f_in k]).
        split.
        intros a b eq.
        apply set_type_eq.
        inversion eq.
        reflexivity.
    }
    pose (f' (k : set_type (λ k, 0 ≠ v' k)) := [f [[k|]|f_in k]|]).
    assert (∀ k, initial_segment n (f' k)) as f'_in.
    {
        intros k.
        unfold initial_segment.
        unfold f'.
        split.
        -   rewrite <- nat_lt_suc_le.
            apply [|f _].
        -   destruct k as [k k_neq].
            cbn.
            unfold v' in k_neq.
            intros contr.
            apply set_type_eq in x_eq.
            cbn in x_eq.
            rewrite <- x_eq in contr.
            apply set_type_eq in contr.
            apply inj in contr.
            apply set_type_eq in contr.
            cbn in contr.
            case_if [eq|neq].
            +   contradiction.
            +   symmetry in contr.
                contradiction.
    }
    specialize (IHn [v'|v'_fin] (λ k, [f' k|f'_in k])).
    prove_parts IHn.
    {
        split; split.
        -   intros a b eq.
            unfold f' in eq.
            apply set_type_eq in eq; cbn in eq.
            apply set_type_eq in eq; cbn in eq.
            apply inj in eq.
            apply set_type_eq in eq; cbn in eq.
            apply set_type_eq in eq; cbn in eq.
            exact eq.
        -   intros [y y_lt].
            unfold initial_segment in y_lt.
            pose proof (trans y_lt (nat_lt_suc n)) as y_lt2.
            pose proof (sur f [y|y_lt2]) as [[z z_neq] z_eq].
            assert (0 ≠ v' z) as z_neq'.
            {
                unfold v'.
                case_if [eq|neq].
                -   subst z.
                    rewrite set_type_simpl in z_eq.
                    rewrite x_eq in z_eq.
                    apply set_type_eq in z_eq; cbn in z_eq.
                    subst y.
                    contradiction (irrefl _ y_lt).
                -   exact z_neq.
            }
            exists [z|z_neq'].
            unfold f'.
            apply set_type_eq; cbn.
            apply set_type_eq in z_eq; cbn in z_eq.
            rewrite <- z_eq.
            do 2 apply f_equal.
            apply set_type_eq; reflexivity.
    }
    destruct IHn as [l [v'_eq l_in]].
    assert (∀ n, grade_sum_subspace_set n (single_to_grade_sum ([v|] n))) as v_in.
    {
        intros m.
        exists ([v|] m).
        reflexivity.
    }
    exists (make_subspace_vector (grade_sum_subspace [x|]) _ (v_in [x|]) ː l).
    split.
    -   rewrite ulist_image_add; cbn.
        rewrite ulist_sum_add.
        rewrite <- v'_eq.
        apply set_type_eq.
        unfold plus; cbn.
        unfold single_to_grade_sum_base.
        unfold v'.
        apply functional_ext.
        intros k.
        case_if [eq|neq].
        +   destruct eq; cbn.
            rewrite plus_rid.
            reflexivity.
        +   rewrite plus_lid.
            reflexivity.
    -   rewrite ulist_prop_add; cbn.
        split.
        +   exists [x|].
            reflexivity.
        +   exact l_in.
Qed.
Next Obligation.
    rename H into l_in.
    rename H0 into l_uni.
    rename H1 into l_zero.
    destruct l as [|v l] using ulist_induction.
    1: apply ulist_prop_end.
    assert (0 = sub_vector_v v) as v_z.
    {
        clear IHl.
        classic_contradiction v_nz.
        apply ulist_prop_add in l_in as [[i i_eq] l_in].
        pose proof (sub_vector_in v) as v_in.
        rewrite <- i_eq in v_in.
        destruct v_in as [v' v_eq].
        rewrite ulist_image_add, ulist_unique_add in l_uni.
        rewrite <- i_eq in l_uni.
        rewrite ulist_image_add in l_zero.
        rewrite <- v_eq in l_zero, v_nz.
        clear v v_eq i_eq.
        rename v' into v.
        destruct l_uni as [v_nin l_uni].
        clear l_uni.
        rewrite ulist_sum_add in l_zero.
        unfold zero, plus in l_zero; cbn in l_zero.
        apply set_type_eq in l_zero; cbn in l_zero.
        assert (∀ k, 0 = single_to_grade_sum_base v k +
            [ulist_sum (ulist_image sub_vector_v l)|] k) as eq2.
        {
            intros k.
            unfold VZ.
            change (@zero _ (module_zero (V k))) with
                ((λ k : I, (@zero _ (module_zero (V k)))) k).
            rewrite l_zero.
            reflexivity.
        }
        clear l_zero.
        specialize (eq2 i).
        unfold single_to_grade_sum_base in eq2.
        destruct (sem (i = i)) as [eq|];
            [>destruct eq; cbn in eq2|contradiction].
        induction l as [|a l] using ulist_induction.
        1: {
            rewrite ulist_image_end, ulist_sum_end in eq2.
            unfold zero at 2 in eq2; cbn in eq2.
            rewrite plus_rid in eq2.
            subst v.
            rewrite (single_to_grade_sum_zero) in v_nz.
            contradiction.
        }
        apply ulist_prop_add in l_in as [[j aj] l_in].
        apply IHl; clear IHl.
        -   exact l_in.
        -   rewrite ulist_image_add, in_ulist_add in v_nin.
            rewrite not_or in v_nin.
            apply v_nin.
        -   rewrite ulist_image_add, ulist_sum_add in eq2.
            unfold plus at 2 in eq2; cbn in eq2.
            rewrite plus_assoc in eq2.
            rewrite (plus_comm v) in eq2.
            rewrite <- plus_assoc in eq2.
            rewrite plus_0_ab_na_b in eq2.
            rewrite <- eq2; clear eq2.
            rewrite <- neg_zero.
            apply f_equal.
            assert (grade_sum_subspace_set j (sub_vector_v a)) as a_in.
            {
                rewrite aj.
                apply sub_vector_in.
            }
            destruct a_in as [a' a_eq].
            rewrite ulist_image_add in v_nin.
            rewrite <- aj in v_nin.
            rewrite <- a_eq.
            clear a_eq a aj.
            rename a' into a.
            unfold single_to_grade_sum; cbn.
            unfold single_to_grade_sum_base.
            destruct (sem (j = i)) as [ij_eq|ij_neq].
            +   rewrite in_ulist_add in v_nin.
                rewrite not_or in v_nin.
                subst.
                destruct v_nin; contradiction.
            +   reflexivity.
    }
    rewrite ulist_prop_add.
    split.
    1: exact v_z.
    apply IHl.
    -   rewrite ulist_prop_add in l_in.
        apply l_in.
    -   rewrite ulist_image_add, ulist_unique_add in l_uni.
        apply l_uni.
    -   rewrite ulist_image_add, ulist_sum_add in l_zero.
        rewrite <- v_z in l_zero.
        rewrite plus_lid in l_zero.
        exact l_zero.
Qed.
(* begin hide *)

End LinearGradeSum.
(* end hide *)

Definition grade_sum {R} I (V : I → ModuleObj R) := make_module R
    (grade_sum_type I V)
    (grade_sum_plus I V)
    (grade_sum_zero I V)
    (grade_sum_neg I V)
    (grade_sum_plus_assoc I V)
    (grade_sum_plus_comm I V)
    (grade_sum_plus_lid I V)
    (grade_sum_plus_linv I V)
    (grade_sum_scalar_mult I V)
    (grade_sum_scalar_id I V)
    (grade_sum_scalar_ldist I V)
    (grade_sum_scalar_rdist I V)
    (grade_sum_scalar_comp I V)
.
