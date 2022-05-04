Require Import init.

Require Export plus_group.
Require Import plus_sum.
Require Export mult_ring.
Require Import unordered_list.
Require Import set.

#[universes(template)]
Class ScalarMult U V := {
    scalar_mult : U → V → V
}.
Infix "·" := scalar_mult : algebra_scope.
Arguments scalar_mult : simpl never.

Class ScalarComp U V `{Mult U, ScalarMult U V} := {
    scalar_comp : ∀ a b v, a · (b · v) = (a * b) · v
}.

Class ScalarId U V `{One U, ScalarMult U V} := {
    scalar_id : ∀ v, 1 · v = v
}.

Class ScalarLdist U V `{Plus V, ScalarMult U V} := {
    scalar_ldist : ∀ a u v, a · (u + v) = a · u + a · v
}.
Class ScalarRdist U V `{Plus U, Plus V, ScalarMult U V} := {
    scalar_rdist : ∀ a b v, (a + b) · v = a · v + b · v
}.

Class ScalarLMult U V `{Mult V, ScalarMult U V} := {
    scalar_lmult : ∀ a u v, (a · u) * v = a · (u * v)
}.
Class ScalarRMult U V `{Mult V, ScalarMult U V} := {
    scalar_rmult : ∀ a u v, u * (a · v) = a · (u * v)
}.

Class Module U V `{
    MR : CRing U,
    MG : AbelianGroup V,
    SM : ScalarMult U V,
    SMC : @ScalarComp U V UM SM,
    SME : @ScalarId U V UE SM,
    SML : @ScalarLdist U V UP0 SM,
    SMR : @ScalarRdist U V UP UP0 SM
}.

Class VectorSpace U V `{
    VF : Field U,
    VG : AbelianGroup V,
    SM : ScalarMult U V,
    SMC : @ScalarComp U V UM SM,
    SME : @ScalarId U V UE SM,
    SML : @ScalarLdist U V UP0 SM,
    SMR : @ScalarRdist U V UP UP0 SM
}.

Class Algebra U V `{
    AR : CRing U,
    AR : Ring V,
    SM : ScalarMult U V,
    SMC : @ScalarComp U V UM SM,
    SME : @ScalarId U V UE SM,
    SML : @ScalarLdist U V UP0 SM,
    SMR : @ScalarRdist U V UP UP0 SM,
    SMLM : @ScalarLMult U V UM0 SM,
    SMRM : @ScalarRMult U V UM0 SM
}.

Class AlgebraField U V `{
    AF : Field U,
    AR : Ring V,
    SM : ScalarMult U V,
    SMC : @ScalarComp U V UM SM,
    SME : @ScalarId U V UE SM,
    SML : @ScalarLdist U V UP0 SM,
    SMR : @ScalarRdist U V UP UP0 SM,
    SMLM : @ScalarLMult U V UM0 SM,
    SMRM : @ScalarRMult U V UM0 SM
}.

Definition linear_combination_set {U V : Type} (l : ulist (U * V))
    := ulist_unique (ulist_image l snd).
Definition linear_combination {U V}
    `{Zero V, VP : Plus V, @PlusComm V VP, @PlusAssoc V VP, ScalarMult U V}
    (l : set_type (@linear_combination_set U V))
    := ulist_sum (ulist_image [l|] (λ x, fst x · snd x)).
Definition linear_list_in {U V}
    (S : V → Prop) (l : set_type (@linear_combination_set U V))
    := ulist_prop (λ v, S (snd v)) [l|].
Definition linear_combination_of {U V}
    `{Zero V, VP : Plus V, @PlusComm V VP, @PlusAssoc V VP, ScalarMult U V}
    (S : V → Prop) (v : V) :=
    ∃ l, v = linear_combination l ∧ linear_list_in S l.

(* begin hide *)
Section LinearBase.

Context {U V} `{AlgebraField U V}.

(* end hide *)
Theorem lscalar : ∀ {u v} a, u = v → a · u = a · v.
    intros u v a eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem rscalar : ∀ {a b} v, a = b → a · v = b · v.
    intros u v a eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem lrscalar : ∀ {a b u v}, a = b → u = v → a · u = b · v.
    intros a b u v eq1 eq2.
    apply lscalar with b in eq2.
    apply rscalar with u in eq1.
    rewrite eq1, <- eq2.
    reflexivity.
Qed.

Theorem scalar_lanni : ∀ v, 0 · v = 0.
    intros v.
    assert (0 · v = 0 · v) as eq by reflexivity.
    rewrite <- (plus_lid 0) in eq at 1.
    rewrite scalar_rdist in eq.
    apply plus_0_a_ab_b in eq.
    symmetry; exact eq.
Qed.

Theorem scalar_ranni : ∀ a, a · 0 = 0.
    intros a.
    assert (a · 0 = a · 0) as eq by reflexivity.
    rewrite <- (plus_lid 0) in eq at 1.
    rewrite scalar_ldist in eq.
    apply plus_0_a_ab_b in eq.
    symmetry; exact eq.
Qed.

Theorem scalar_lneg : ∀ a b, -a · b = -(a · b).
    intros a b.
    apply plus_lcancel with (a · b).
    rewrite <- scalar_rdist.
    do 2 rewrite plus_rinv.
    apply scalar_lanni.
Qed.

Theorem scalar_rneg : ∀ a b, a · -b = -(a · b).
    intros a b.
    apply plus_lcancel with (a · b).
    rewrite <- scalar_ldist.
    do 2 rewrite plus_rinv.
    apply scalar_ranni.
Qed.

Theorem scalar_neg_one : ∀ a, (-(1)) · a = -a.
    intros a.
    rewrite scalar_lneg.
    rewrite scalar_id.
    reflexivity.
Qed.

Theorem scalar_lcancel : ∀ {a b} c, 0 ≠ c → c · a = c · b → a = b.
    intros a b c c_nz eq.
    apply lscalar with (/c) in eq.
    do 2 rewrite scalar_comp in eq.
    rewrite mult_linv in eq by exact c_nz.
    do 2 rewrite scalar_id in eq.
    exact eq.
Qed.

Theorem scalar_rcancel : ∀ {a b} c, 0 ≠ c → a · c = b · c → a = b.
    intros a b c c_nz eq.
    rewrite <- plus_0_anb_a_b in eq.
    rewrite <- scalar_lneg in eq.
    rewrite <- scalar_rdist in eq.
    classic_contradiction contr.
    rewrite <- (scalar_ranni (a - b)) in eq.
    apply scalar_lcancel in eq; [>contradiction|].
    intros contr2.
    rewrite plus_0_anb_a_b in contr2.
    contradiction.
Qed.

Theorem linear_combination_add : ∀ x l H1 H2,
        linear_combination [x ::: l | H1] =
        fst x · snd x + linear_combination [l | H2].
    intros x l HH1 HH2.
    unfold linear_combination; cbn.
    rewrite ulist_image_add, ulist_sum_add.
    reflexivity.
Qed.

Theorem linear_combination_of_zero : ∀ S, linear_combination_of S 0.
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
        pose (l' := (a', v) ::: l1).
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
    -   pose (l' := (α * β, v) ::: l).
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
    intros S a v v_comb.
    pose (l := (a, v) ::: ulist_end).
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
    intros S u v u_comb v_comb.
    classic_case (u = v) as [eq|neq].
    {
        subst.
        rewrite <- (scalar_id v).
        rewrite <- scalar_rdist.
        apply linear_combination_of_scalar.
        exact v_comb.
    }
    pose (l := (1, u) ::: (1, v) ::: ulist_end : ulist (U * V)).
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
    intros l.
    apply ulist_filter_image_unique.
    exact [|l].
Qed.

Definition linear_remove_zeros l :=
    [linear_remove_zeros_base l|linear_remove_zeros_comb l].

Theorem linear_combination_remove_zeros : ∀ l,
        linear_combination l = linear_combination (linear_remove_zeros l).
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
    intros l S Sl.
    apply ulist_prop_filter.
    exact Sl.
Qed.

(* begin hide *)
End LinearBase.
(* end hide *)
