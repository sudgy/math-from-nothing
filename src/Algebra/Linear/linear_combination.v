Require Import init.

Require Export linear_base.
Require Import unordered_list.
Require Import set.

Definition linear_combination_set {U V : Type} (l : ulist (U * V))
    := ulist_unique (ulist_image snd l).
Definition linear_combination {U V}
    `{VZ : Zero V, VP : Plus V, @PlusComm V VP,
        @PlusAssoc V VP, @PlusLid V VP VZ, ScalarMult U V}
    (l : set_type (@linear_combination_set U V))
    := ulist_sum (ulist_image (λ x, fst x · snd x) [l|]).
Definition linear_list_in {U V}
    (S : V → Prop) (l : set_type (@linear_combination_set U V))
    := ulist_prop (λ v, S (snd v)) [l|].
Definition linear_combination_of {U V}
    `{VZ : Zero V, VP : Plus V, @PlusComm V VP,
        @PlusAssoc V VP, @PlusLid V VP VZ, ScalarMult U V}
    (S : V → Prop) (v : V) :=
    ∃ l, v = linear_combination l ∧ linear_list_in S l.

(* begin hide *)
Section LinearBase.

Context {U V} `{AlgebraField U V}.

Theorem linear_combination_add : ∀ x l H1 H2,
    linear_combination [x ː l | H1] =
    fst x · snd x + linear_combination [l | H2].
Proof.
    intros x l HH1 HH2.
    unfold linear_combination; cbn.
    rewrite ulist_image_add, ulist_sum_add.
    reflexivity.
Qed.

Theorem linear_combination_of_zero : ∀ S, linear_combination_of S 0.
Proof.
    intros S.
    assert (@linear_combination_set U V ulist_end) as end_in.
    {
        unfold linear_combination_set.
        rewrite ulist_image_end.
        apply ulist_unique_end.
    }
    exists [ulist_end|end_in].
    split.
    -   unfold linear_combination; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        reflexivity.
    -   unfold linear_list_in; cbn.
        apply ulist_prop_end.
Qed.

Theorem linear_combination_of_combination : ∀ S l,
    (∀ v, (∃ α, in_ulist [l|] (α, v)) → linear_combination_of S v) →
    linear_combination_of S (linear_combination l).
Proof.
    intros S [l l_comb] v_combs.
    induction l using ulist_induction.
    {
        unfold linear_combination; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        apply linear_combination_of_zero.
    }
    cbn in v_combs.
    assert (linear_combination_set l) as l_comb'.
    {
        unfold linear_combination_set in l_comb.
        rewrite ulist_image_add, ulist_unique_add in l_comb.
        apply l_comb.
    }
    specialize (IHl l_comb').
    cbn in IHl.
    assert (∀ v, (∃ α, in_ulist l (α, v)) → linear_combination_of S v)
        as v_combs'.
    {
        intros v [α v_in].
        apply v_combs.
        exists α.
        rewrite in_ulist_add.
        right.
        exact v_in.
    }
    specialize (IHl v_combs').
    assert (linear_combination_of S (snd a)) as Sa.
    {
        apply v_combs.
        exists (fst a).
        rewrite in_ulist_add.
        left.
        destruct a; reflexivity.
    }
    unfold linear_combination; cbn.
    unfold linear_combination in IHl; cbn in IHl.
    clear v_combs v_combs' l_comb l_comb'.
    destruct IHl as [bl [bl_eq Sbl]].
    rewrite ulist_image_add, ulist_sum_add.
    rewrite bl_eq; clear bl_eq l.
    destruct Sa as [al [al_eq Sal]].
    rewrite al_eq; clear al_eq.
    destruct a as [α v]; cbn; clear v.
    destruct al as [al al_comb].
    induction al using ulist_induction.
    {
        unfold linear_combination at 1; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite scalar_ranni.
        rewrite plus_lid.
        exists bl.
        split.
        -   reflexivity.
        -   exact Sbl.
    }
    unfold linear_combination at 1; cbn.
    unfold linear_combination_set in al_comb.
    unfold linear_list_in in Sal; cbn in Sal.
    rewrite ulist_image_add, ulist_unique_add in al_comb.
    assert (linear_combination_set al) as al_comb'.
    {
        apply al_comb.
    }
    assert (linear_list_in S [al|al_comb']) as Sal'.
    {
        rewrite ulist_prop_add in Sal.
        apply Sal.
    }
    specialize (IHal al_comb' Sal').
    rewrite ulist_image_add, ulist_sum_add.
    rewrite scalar_ldist.
    rewrite <- plus_assoc.
    destruct IHal as [l [l_eq Sl]].
    destruct a as [β v]; cbn in *.
    assert (S v) as Sv.
    {
        rewrite ulist_prop_add in Sal.
        apply Sal.
    }
    unfold linear_combination in l_eq at 1; cbn in l_eq.
    rewrite l_eq; clear al al_comb bl Sbl l_eq al_comb' Sal Sal'.
    destruct l as [l l_comb].
    unfold linear_list_in in Sl; cbn in Sl.
    rewrite scalar_comp.
    classic_case (∃ a, in_ulist l (a, v)) as [v_in|v_nin].
    -   destruct v_in as [a v_in].
        apply in_ulist_split in v_in as [l1 l1_eq].
        subst l.
        remember (α * β + a) as a'.
        pose (l' := (a', v) ː l1).
        assert (linear_combination_set l') as l'_comb.
        {
            unfold linear_combination_set in *.
            unfold l'.
            rewrite ulist_image_add, ulist_unique_add; cbn.
            rewrite ulist_image_add, ulist_unique_add in l_comb; cbn in l_comb.
            exact l_comb.
        }
        exists [l'|l'_comb].
        split.
        +   unfold l', linear_combination; cbn.
            do 2 rewrite ulist_image_add, ulist_sum_add.
            cbn.
            rewrite Heqa'.
            rewrite scalar_rdist.
            apply plus_assoc.
        +   unfold linear_list_in, l'; cbn.

            rewrite ulist_prop_add; cbn.
            rewrite ulist_prop_add in Sl; cbn in Sl.
            exact Sl.
    -   pose (l' := (α * β, v) ː l).
        assert (linear_combination_set l') as l'_comb.
        {
            unfold l', linear_combination_set; cbn.
            rewrite ulist_image_add, ulist_unique_add; cbn.
            split.
            2: exact l_comb.
            intros v_in.
            apply v_nin.
            apply image_in_ulist in v_in as [[a v'] [v_eq v_in]].
            cbn in v_eq.
            subst v'.
            exists a.
            exact v_in.
        }
        exists [l'|l'_comb].
        split.
        +   unfold l', linear_combination; cbn.
            rewrite ulist_image_add, ulist_sum_add; cbn.
            reflexivity.
        +   unfold linear_list_in, l'; cbn.
            rewrite ulist_prop_add; cbn.
            split; assumption.
Qed.

Theorem linear_combination_of_scalar : ∀ S a v,
    linear_combination_of S v → linear_combination_of S (a · v).
Proof.
    intros S a v v_comb.
    pose (l := (a, v) ː ulist_end).
    assert (linear_combination_set l) as l_comb.
    {
        unfold linear_combination_set, l.
        rewrite ulist_image_add, ulist_unique_add, ulist_image_end.
        split.
        -   apply in_ulist_end.
        -   apply ulist_unique_end.
    }
    pose proof (linear_combination_of_combination S [l|l_comb]) as eq.
    unfold linear_combination, l in eq; cbn in eq.
    rewrite ulist_image_add, ulist_sum_add in eq.
    rewrite ulist_image_end, ulist_sum_end in eq.
    rewrite plus_rid in eq.
    apply eq; clear eq.
    setoid_rewrite in_ulist_add.
    intros u [b [u_eq|contr]].
    2: contradiction (in_ulist_end _ contr).
    inversion u_eq.
    subst.
    exact v_comb.
Qed.

Theorem linear_combination_of_plus : ∀ S u v,
    linear_combination_of S u → linear_combination_of S v →
    linear_combination_of S (u + v).
Proof.
    intros S u v u_comb v_comb.
    classic_case (u = v) as [eq|neq].
    {
        subst.
        rewrite <- (scalar_id v).
        rewrite <- scalar_rdist.
        apply linear_combination_of_scalar.
        exact v_comb.
    }
    pose (l := (1, u) ː (1, v) ː ulist_end : ulist (U * V)).
    assert (linear_combination_set l) as l_comb.
    {
        unfold linear_combination_set, l; cbn.
        do 2 rewrite ulist_image_add, ulist_unique_add.
        rewrite in_ulist_add.
        rewrite ulist_image_end.
        rewrite not_or.
        cbn.
        repeat split.
        -   rewrite neq_sym; exact neq.
        -   apply in_ulist_end.
        -   apply in_ulist_end.
        -   apply ulist_unique_end.
    }
    pose proof (linear_combination_of_combination S [l|l_comb]) as eq.
    unfold linear_combination, l in eq; cbn in eq.
    do 2 rewrite ulist_image_add, ulist_sum_add in eq; cbn in eq.
    rewrite ulist_image_end, ulist_sum_end in eq.
    do 2 rewrite scalar_id in eq.
    rewrite plus_rid in eq.
    apply eq; clear eq.
    setoid_rewrite in_ulist_add.
    setoid_rewrite in_ulist_add.
    intros w [a [w_eq|[w_eq|contr]]].
    3: contradiction (in_ulist_end _ contr).
    all: inversion w_eq; subst.
    -   exact u_comb.
    -   exact v_comb.
Qed.

Definition linear_remove_zeros_base (l : set_type (@linear_combination_set U V))
    := ulist_filter (λ x, 0 ≠ fst x) [l|].

Lemma linear_remove_zeros_comb :
    ∀ l, linear_combination_set (linear_remove_zeros_base l).
Proof.
    intros l.
    apply ulist_filter_image_unique.
    exact [|l].
Qed.

Definition linear_remove_zeros l :=
    [linear_remove_zeros_base l|linear_remove_zeros_comb l].

Theorem linear_combination_remove_zeros : ∀ l,
    linear_combination l = linear_combination (linear_remove_zeros l).
Proof.
    intros [l l_uni].
    unfold linear_combination, linear_remove_zeros, linear_remove_zeros_base.
    cbn.
    clear l_uni.
    induction l using ulist_induction.
    -   rewrite ulist_filter_end.
        reflexivity.
    -   rewrite ulist_image_add, ulist_sum_add.
        rewrite IHl; clear IHl.
        classic_case (0 ≠ fst a).
        +   rewrite ulist_filter_add_in by exact n.
            rewrite ulist_image_add, ulist_sum_add.
            reflexivity.
        +   rewrite ulist_filter_add_nin by exact n.
            rewrite not_not in n.
            rewrite <- n.
            rewrite scalar_lanni.
            rewrite plus_lid.
            reflexivity.
Qed.

Theorem linear_list_in_remove_zeros : ∀ l S,
    linear_list_in S l → linear_list_in S (linear_remove_zeros l).
Proof.
    intros l S Sl.
    apply ulist_prop_other_filter.
    exact Sl.
Qed.

(* begin hide *)
End LinearBase.
(* end hide *)
