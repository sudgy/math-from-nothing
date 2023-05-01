Require Import init.

Require Export linear_base.
Require Export linear_sum_module.
Require Export module_category.
Require Export algebra_category.

Require Import set.
Require Import nat.
Require Import unordered_list.

#[universes(template)]
Class GradedSpace {U} (V : Module U) (I : Type) := {
    grade_modules : I → Module U;
    grade_sum := sum_module I grade_modules;
    grade_to : cat_morphism V grade_sum;
    grade_from : cat_morphism grade_sum V;
    grade_to_from : ∀ x : grade_sum, grade_to (grade_from x) = x;
    grade_from_to : ∀ x : V, grade_from (grade_to x) = x;
}.
Arguments grade_modules : simpl never.
Arguments grade_sum : simpl never.
Arguments grade_to : simpl never.
Arguments grade_from : simpl never.

Section LinearGrade.

Context {U} {V : Module U} {I : Type}.
Context `{GradedSpace U V I}.

Global Instance grade_to_bij : Bijective grade_to.
Proof.
    apply (inverse_ex_bijective grade_to grade_from).
    split.
    -   apply grade_to_from.
    -   apply grade_from_to.
Qed.

Global Instance grade_from_bij : Bijective grade_from.
Proof.
    apply (inverse_ex_bijective grade_from grade_to).
    split.
    -   apply grade_from_to.
    -   apply grade_to_from.
Qed.

Definition grade_project (v : V) (i : I)
    := grade_from (sum_project I grade_modules (grade_to v) i).
Arguments grade_project : simpl never.

Definition of_grade (i : I) (v : V) := grade_project v i = v.
Arguments of_grade : simpl never.

Definition homogeneous v := ∃ i, of_grade i v.
Arguments homogeneous : simpl never.

Definition grade_modules_from_base {i} (v : grade_modules i)
    := grade_from (single_to_sum_module I grade_modules v).

Theorem grade_modules_from_scalar i : ∀ a (v : grade_modules i),
    grade_modules_from_base (a · v) = a · grade_modules_from_base v.
Proof.
    intros a v.
    unfold grade_modules_from_base.
    rewrite single_to_sum_module_scalar.
    apply module_homo_scalar.
Qed.

Theorem grade_modules_from_plus i : ∀ (u v : grade_modules i),
    grade_modules_from_base (u + v) =
    grade_modules_from_base u + grade_modules_from_base v.
Proof.
    intros u v.
    unfold grade_modules_from_base.
    rewrite single_to_sum_module_plus.
    apply module_homo_plus.
Qed.

Definition grade_modules_from {i} := make_module_homomorphism _ _ _ _
    (grade_modules_from_plus i) (grade_modules_from_scalar i).

Theorem grade_modules_from_to {i} : ∀ u, of_grade i u →
    grade_modules_from ([grade_to u|] i) = u.
Proof.
    intros u iu.
    unfold grade_modules_from; cbn.
    unfold grade_modules_from_base.
    rewrite <- (grade_from_to u) at 2.
    apply f_equal.
    apply set_type_eq; cbn.
    apply functional_ext; intros x.
    unfold of_grade in iu.
    replace ([grade_to u|] x) with ([grade_to (grade_project u i)|] x).
    2: rewrite iu; reflexivity.
    unfold grade_project.
    rewrite grade_to_from; cbn.
    unfold single_to_sum_module_base, sum_project_base.
    case_if [eq|neq].
    -   destruct eq; cbn.
        reflexivity.
    -   reflexivity.
Qed.

Theorem of_grade_ex : ∀ v i, of_grade i v ↔ ∃ v' : grade_modules i,
    v = grade_from (single_to_sum_module I grade_modules v').
Proof.
    intros v i.
    split.
    -   intros iv.
        exists ([grade_to v|] i).
        unfold of_grade in iv.
        rewrite <- iv.
        unfold grade_project.
        rewrite grade_to_from.
        apply f_equal.
        apply set_type_eq; cbn.
        apply functional_ext; intros x.
        unfold sum_project_base, single_to_sum_module_base; cbn.
        case_if [eq|neq]; cbn.
        +   destruct eq; cbn.
            rewrite if_true by reflexivity.
            reflexivity.
        +   reflexivity.
    -   intros [v' v_eq].
        subst v.
        unfold of_grade.
        unfold grade_project.
        rewrite grade_to_from.
        apply f_equal.
        apply set_type_eq; cbn.
        apply functional_ext; intros x.
        unfold single_to_sum_module.
        unfold sum_project_base, single_to_sum_module_base; cbn.
        case_if [eq|neq]; reflexivity.
Qed.

Theorem grade_project_project : ∀ v i,
    grade_project (grade_project v i) i = grade_project v i.
Proof.
    intros v i.
    unfold grade_project.
    rewrite grade_to_from.
    rewrite sum_project_project.
    reflexivity.
Qed.

Theorem grade_project_grade : ∀ v i, of_grade i (grade_project v i).
Proof.
    intros v i.
    unfold of_grade.
    apply grade_project_project.
Qed.

Theorem grade_project_homo : ∀ v i, homogeneous (grade_project v i).
Proof.
    intros v i.
    exists i.
    apply grade_project_grade.
Qed.

Theorem grade_project_zero : ∀ i, grade_project 0 i = 0.
Proof.
    intros i.
    unfold grade_project.
    rewrite module_homo_zero.
    rewrite sum_project_zero.
    rewrite module_homo_zero.
    reflexivity.
Qed.

Theorem grade_project_of_grade : ∀ v i, of_grade i v → grade_project v i = v.
Proof.
    trivial.
Qed.

Theorem grade_project_neq : ∀ i j v, i ≠ j →
    grade_project (grade_project v i) j = 0.
Proof.
    intros i j v neq.
    unfold grade_project.
    rewrite grade_to_from.
    rewrite sum_project_neq by exact neq.
    rewrite module_homo_zero.
    reflexivity.
Qed.

Theorem grade_project_of_grade_neq : ∀ i j v, of_grade i v → i ≠ j →
    grade_project v j = 0.
Proof.
    intros i j v iv neq.
    unfold of_grade in iv.
    rewrite <- iv.
    apply grade_project_neq.
    exact neq.
Qed.

Theorem grade_project_plus : ∀ u v i,
    grade_project (u + v) i = grade_project u i + grade_project v i.
Proof.
    intros u v i.
    unfold grade_project.
    rewrite module_homo_plus.
    rewrite sum_project_plus.
    apply module_homo_plus.
Qed.

Theorem grade_project_scalar : ∀ a v i,
    grade_project (a · v) i = a · grade_project v i.
Proof.
    intros a v i.
    unfold grade_project.
    rewrite module_homo_scalar.
    rewrite sum_project_scalar.
    apply module_homo_scalar.
Qed.

Theorem grade_project_neg : ∀ v i, grade_project (-v) i = -grade_project v i.
Proof.
    intros v i.
    rewrite <- scalar_neg_one.
    rewrite grade_project_scalar.
    apply scalar_neg_one.
Qed.

Theorem of_grade_zero : ∀ i, of_grade i 0.
Proof.
    intros i.
    unfold of_grade.
    apply grade_project_zero.
Qed.

Theorem of_grade_scalar : ∀ a v i, of_grade i v → of_grade i (a · v).
Proof.
    intros a v i v_in.
    unfold of_grade.
    rewrite grade_project_scalar.
    rewrite v_in.
    reflexivity.
Qed.

Theorem of_grade_neg : ∀ v i, of_grade i v → of_grade i (-v).
Proof.
    intros v i v_in.
    unfold of_grade.
    rewrite grade_project_neg.
    rewrite v_in.
    reflexivity.
Qed.

Theorem of_grade_plus : ∀ u v i,
    of_grade i u → of_grade i v → of_grade i (u + v).
Proof.
    intros u v i u_in v_in.
    unfold of_grade.
    rewrite grade_project_plus.
    rewrite u_in, v_in.
    reflexivity.
Qed.

Theorem homo_scalar : ∀ a v, homogeneous v → homogeneous (a · v).
Proof.
    intros a v [i v_in].
    exists i.
    exact (of_grade_scalar _ _ _ v_in).
Qed.

Theorem homo_neg : ∀ v, homogeneous v → homogeneous (-v).
Proof.
    intros v [i v_in].
    exists i.
    exact (of_grade_neg _ _ v_in).
Qed.

Theorem all_grade_project_eq : ∀ u v,
    (∀ i, grade_project u i = grade_project v i) → u = v.
Proof.
    intros u v all_eq.
    apply (inj (f := grade_to)).
    apply all_sum_project_eq.
    intros i.
    specialize (all_eq i).
    unfold grade_project in all_eq.
    apply inj in all_eq.
    exact all_eq.
Qed.

Theorem grade_project_sum : ∀ f n a b,
    grade_project (sum f a b) n = sum (λ m, grade_project (f m) n) a b.
Proof.
    intros f n a b.
    nat_induction b.
    -   unfold zero; cbn.
        apply grade_project_zero.
    -   cbn.
        rewrite grade_project_plus.
        rewrite IHb.
        reflexivity.
Qed.

Theorem sum_grade_project_single : ∀ f A n a b, Injective f →
    ∀ m, f m = n → a ≤ m → m < a + b →
    sum (λ m, grade_project (grade_project A (f m)) n) a b =
    grade_project A n.
Proof.
    intros f A n a b f_inj m eq m_geq m_leq.
    subst n.
    nat_induction b.
    {
        rewrite plus_rid in m_leq.
        exfalso; clear - m_leq m_geq.
        destruct (lt_le_trans m_leq m_geq); contradiction.
    }
    cbn.
    classic_case (m = a + b) as [eq|neq].
    -   subst m.
        rewrite sum_zero_eq.
        {
            rewrite plus_lid.
            apply grade_project_project.
        }
        intros n n_lt.
        assert (f (a + n) ≠ f (a + b)) as neq.
        {
            intros contr.
            apply f_inj in contr.
            apply plus_lcancel in contr.
            subst n.
            destruct n_lt; contradiction.
        }
        pose proof (grade_project_grade A (f (a + n))) as A_grade.
        apply (grade_project_of_grade_neq _ _ _ A_grade neq).
    -   rewrite nat_plus_rsuc in m_leq.
        rewrite nat_lt_suc_le in m_leq.
        specialize (IHb (make_and m_leq neq)).
        rewrite IHb.
        assert (f (a + b) ≠ f m) as neq'.
        {
            intros contr.
            apply f_inj in contr.
            subst m.
            contradiction.
        }
        pose proof (grade_project_grade A (f (a + b))) as A_grade.
        rewrite (grade_project_of_grade_neq _ _ _ A_grade neq').
        apply plus_rid.
Qed.

Theorem of_grade_unique : ∀ v i j, 0 ≠ v → of_grade i v → of_grade j v → i = j.
Proof.
    intros v i j v_nz iv jv.
    pose proof (grade_project_of_grade _ _ iv) as i_eq.
    rewrite <- i_eq in jv.
    pose proof (grade_project_of_grade _ _ jv) as j_eq.
    rewrite i_eq in j_eq at 2.
    classic_contradiction contr.
    rewrite (grade_project_neq _ _ _ contr) in j_eq.
    contradiction.
Qed.

Definition grades_set (v : V) := λ i : I, 0 ≠ grade_project v i.

Theorem grades_set_finite : ∀ v, simple_finite (set_type (grades_set v)).
Proof.
    intros v.
    pose proof [|grade_to v] as [n [f f_inj]].
    exists n.
    unfold grades_set.
    assert (∀ i, 0 ≠ grade_project v i → 0 ≠ [grade_to v|] i) as f_in.
    {
        intros i i_neq i_z.
        apply i_neq; clear i_neq.
        unfold grade_project.
        rewrite <- (module_homo_zero grade_from).
        apply f_equal.
        apply set_type_eq.
        apply functional_ext; intros x.
        unfold zero; cbn.
        unfold sum_project_base.
        case_if [eq|neq].
        -   subst.
            exact i_z.
        -   reflexivity.
    }
    exists (λ i, f [[i|] | f_in [i|] [|i]]).
    split.
    intros a b eq.
    apply inj in eq.
    rewrite set_type_eq2 in eq.
    rewrite set_type_eq in eq.
    exact eq.
Qed.

Definition grade_set_to_list {S : I → Prop} (S_fin : simple_finite (set_type S))
    := ulist_image set_value (ex_val (ulist_finite S_fin)).
Definition grades_list (v : V) := grade_set_to_list (grades_set_finite v).
Definition grades_project (v : V) (l : ulist I)
    := ulist_sum (ulist_image (λ i, grade_project v i) l).

Theorem grades_list_nz :
    ∀ v, ulist_prop (λ i, 0 ≠ grade_project v i) (grades_list v).
Proof.
    intros v.
    unfold grades_list, grade_set_to_list.
    rewrite_ex_val l [l_uni l_in].
    clear l_uni l_in.
    induction l using ulist_induction.
    -   rewrite ulist_image_end.
        apply ulist_prop_end.
    -   rewrite ulist_image_add, ulist_prop_add.
        split.
        +   exact [|a].
        +   exact IHl.
Qed.

Theorem grades_list_eq : ∀ v, v = grades_project v (grades_list v).
Proof.
    intros v.
    pose proof (grades_list_nz v) as l_nz.
    unfold grades_project, grades_list, grade_set_to_list in *.
    rewrite_ex_val l' [l'_uni l'_in].
    pose (l := ulist_image set_value l').
    fold l.
    fold l in l_nz.
    assert (ulist_unique l) as l_uni.
    {
        unfold l.
        apply ulist_image_unique_inj.
        -   split.
            intros a b.
            rewrite set_type_eq.
            trivial.
        -   exact l'_uni.
    }
    assert (∀ i : I, grades_set v i → in_ulist l i) as l_in.
    {
        intros i i_in.
        specialize (l'_in [i|i_in]).
        unfold l.
        apply (in_ulist_image set_value) in l'_in.
        exact l'_in.
    }
    clearbody l.
    clear l' l'_uni l'_in.
    clear l_nz.
    revert v l_in.
    ulist_unique_induction l l_uni as n n_nin IHl; intros.
    {
        rewrite ulist_image_end, ulist_sum_end.
        apply all_grade_project_eq.
        intros i.
        rewrite grade_project_zero.
        symmetry.
        classic_contradiction nz.
        specialize (l_in _ nz).
        contradiction (in_ulist_end _ l_in).
    }
    specialize (IHl (v - grade_project v n)).
    prove_parts IHl.
    {
        intros i i_in.
        unfold grades_set in i_in.
        rewrite grade_project_plus, grade_project_neg in i_in.
        classic_case (n = i) as [eq|neq].
        -   subst i.
            rewrite grade_project_project in i_in.
            rewrite plus_rinv in i_in.
            contradiction.
        -   rewrite grade_project_neq in i_in by exact neq.
            rewrite neg_zero, plus_rid in i_in.
            specialize (l_in i i_in).
            rewrite in_ulist_add_eq in l_in.
            destruct l_in as [|]; [>contradiction|assumption].
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite plus_rlmove.
    rewrite plus_comm.
    rewrite IHl; clear IHl.
    clear - n_nin.
    induction l as [|i l] using ulist_induction.
    {
        do 2 rewrite ulist_image_end.
        reflexivity.
    }
    rewrite in_ulist_add_eq in n_nin.
    rewrite not_or in n_nin.
    destruct n_nin as [neq n_nin].
    specialize (IHl n_nin).
    do 2 rewrite ulist_image_add, ulist_sum_add.
    rewrite IHl; clear IHl.
    apply rplus.
    rewrite grade_project_plus, grade_project_neg.
    rewrite neq_sym in neq.
    rewrite grade_project_neq by exact neq.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem grade_induction : ∀ S : V → Prop,
    S 0 → (∀ (u : set_type homogeneous) v, S v → S ([u|] + v)) → ∀ v, S v.
Proof.
    intros S S0 S_ind v.
    remember (grades_list v) as l.
    rewrite (grades_list_eq v).
    rewrite <- Heql.
    clear Heql.
    unfold grades_project.
    induction l using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        exact S0.
    }
    rewrite ulist_image_add, ulist_sum_add.
    pose proof (grade_project_homo v a) as va.
    exact (S_ind [_|va] _ IHl).
Qed.

Theorem grades_list_zero : grades_list 0 = ⟦⟧.
Proof.
    unfold grades_list, grade_set_to_list.
    rewrite_ex_val l [l_uni l_nz].
    destruct l as [|a l] using ulist_destruct.
    -   apply ulist_image_end.
    -   destruct a as [a a_nz].
        unfold grades_set in a_nz.
        exfalso; clear - a_nz.
        rewrite grade_project_zero in a_nz.
        contradiction.
Qed.

Theorem grades_list_homo : ∀ v i, 0 ≠ v → of_grade i v → grades_list v = ⟦i⟧.
Proof.
    intros v i v_nz iv.
    unfold grades_list, grade_set_to_list.
    rewrite_ex_val l [l_uni l_nz].
    assert (grades_set v i) as i_in.
    {
        unfold grades_set.
        unfold of_grade in iv.
        rewrite iv.
        exact v_nz.
    }
    assert (∀ j, grades_set v j → i = j) as i_eq.
    {
        intros j j_in.
        unfold grades_set in j_in.
        unfold of_grade in iv.
        rewrite <- iv in j_in.
        classic_contradiction contr.
        rewrite grade_project_neq in j_in by exact contr.
        contradiction.
    }
    destruct l as [|a l] using ulist_destruct.
    2: destruct l as [|b l] using ulist_destruct.
    -   contradiction (in_ulist_end _ (l_nz [i|i_in])).
    -   rewrite ulist_image_single.
        specialize (l_nz [i|i_in]).
        rewrite in_ulist_single_eq in l_nz.
        subst.
        reflexivity.
    -   pose proof (i_eq [a|] [|a]) as a_eq.
        pose proof (i_eq [b|] [|b]) as b_eq.
        rewrite a_eq in b_eq.
        rewrite set_type_eq in b_eq.
        subst b.
        rewrite ulist_unique_add in l_uni.
        rewrite in_ulist_add_eq in l_uni.
        rewrite not_or in l_uni.
        destruct l_uni as [[neq]].
        contradiction.
Qed.

End LinearGrade.

Class GradedAlgebra {U} (V : Algebra U) (I : Type)
    `{GradedSpace U (algebra_module V) I} `{Plus I} :=
{
    of_grade_mult : ∀ u v i j,
        of_grade i u → of_grade j v → of_grade (i + j) (u * v)
}.

Section LinearGrade.

Context {U} {V : Algebra U} {I : Type} `{AllPlusClass I}.
Context `{VG : GradedSpace U V I} `{@GradedAlgebra U V I VG UP}.

Theorem homo_mult : ∀ u v, homogeneous u → homogeneous v → homogeneous (u * v).
Proof.
    intros u v [i ui] [j vj].
    exists (i + j).
    apply of_grade_mult; assumption.
Qed.

Theorem homo_lmult_project : ∀ i j u v, of_grade i u →
    grade_project (u * v) (i + j) = u * (grade_project v j).
Proof.
    intros i j u v ui.
    induction v as [|v' v IHv] using grade_induction.
    1: {
        rewrite mult_ranni.
        do 2 rewrite grade_project_zero.
        rewrite mult_ranni.
        reflexivity.
    }
    rewrite ldist.
    do 2 rewrite grade_project_plus.
    rewrite ldist.
    rewrite IHv.
    apply rplus.
    clear v IHv.
    rename v' into v.
    destruct v as [v [j' vj']].
    pose proof (of_grade_mult u v _ _ ui vj') as uv_ij.
    classic_case (j = j') as [j_eq|j_neq].
    -   subst j'.
        rewrite grade_project_of_grade by exact uv_ij.
        rewrite grade_project_of_grade by exact vj'.
        reflexivity.
    -   rewrite (grade_project_of_grade_neq (i + j')).
        +   rewrite neq_sym in j_neq.
            rewrite (grade_project_of_grade_neq j') by assumption.
            rewrite mult_ranni.
            reflexivity.
        +   exact uv_ij.
        +   intros contr.
            apply plus_lcancel in contr.
            symmetry in contr; contradiction.
Qed.

Theorem homo_rmult_project : ∀ i j u v, of_grade j v →
    grade_project (u * v) (i + j) = (grade_project u i) * v.
Proof.
    intros i j u v vj.
    induction u as [|u' u IHu] using grade_induction.
    1: {
        rewrite mult_lanni.
        do 2 rewrite grade_project_zero.
        rewrite mult_lanni.
        reflexivity.
    }
    rewrite rdist.
    do 2 rewrite grade_project_plus.
    rewrite rdist.
    rewrite IHu.
    apply rplus.
    clear u IHu.
    rename u' into u.
    destruct u as [u [i' ui']].
    pose proof (of_grade_mult u v _ _ ui' vj) as uv_ij.
    classic_case (i = i') as [i_eq|i_neq].
    -   subst i'.
        rewrite grade_project_of_grade by exact uv_ij.
        rewrite grade_project_of_grade by exact ui'.
        reflexivity.
    -   rewrite (grade_project_of_grade_neq (i' + j)).
        +   rewrite neq_sym in i_neq.
            rewrite (grade_project_of_grade_neq i') by assumption.
            rewrite mult_lanni.
            reflexivity.
        +   exact uv_ij.
        +   intros contr.
            apply plus_rcancel in contr.
            symmetry in contr; contradiction.
Qed.

End LinearGrade.
