Require Import init.

Require Export plus_group.
Require Import plus_sum.
Require Export mult_ring.
Require Import list.
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

Definition linear_combination_set {U V : Type} (l : list (U * V))
    := list_unique (list_image l snd).
Definition linear_combination {U V} `{Zero V, Plus V, ScalarMult U V}
    (l : set_type (@linear_combination_set U V))
    := list_sum (list_image [l|] (λ x, fst x · snd x)).
Definition linear_combination_of {U V} `{Zero V, Plus V, ScalarMult U V}
    (S : V → Prop) (v : V) :=
    ∃ l, v = linear_combination l ∧ (∀ v, (∃ α, in_list [l|] (α, v)) → S v).

(* begin hide *)
Section LinearBase.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    UD : Div U,
    @MultAssoc U UM,
    @MultLid U UM UO,
    @MultLinv U UZ UM UO UD,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM,
    @ScalarComp U V UM SM
}.
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

Theorem linear_combination_of_zero : ∀ S, linear_combination_of S 0.
    intros S.
    assert (@linear_combination_set U V list_end) as end_in by exact true.
    exists [list_end|end_in].
    split.
    -   cbn.
        reflexivity.
    -   intros v [α v_in].
        cbn in v_in.
        contradiction v_in.
Qed.

Theorem linear_combination_of_combination : ∀ S l,
        (∀ v, (∃ α, in_list [l|] (α, v)) → linear_combination_of S v) →
        linear_combination_of S (linear_combination l).
    intros S [l l_comb] v_combs.
    induction l.
    {
        cbn.
        apply linear_combination_of_zero.
    }
    change [[a::l|l_comb]|] with (a::l) in v_combs.
    assert (linear_combination_set l) as l_comb'.
    {
        apply l_comb.
    }
    specialize (IHl l_comb').
    change [[l|l_comb']|] with l in IHl.
    assert (∀ v, (∃ α, in_list l (α, v)) → linear_combination_of S v)
        as v_combs'.
    {
        intros v [α v_in].
        apply v_combs.
        exists α.
        right.
        exact v_in.
    }
    specialize (IHl v_combs').
    assert (linear_combination_of S (snd a)) as Sa.
    {
        apply v_combs.
        exists (fst a).
        left.
        destruct a; reflexivity.
    }
    cbn in *.
    clear v_combs v_combs' l_comb l_comb'.
    destruct IHl as [bl [bl_eq Sbl]].
    rewrite bl_eq; clear bl_eq l.
    destruct Sa as [al [al_eq Sal]].
    rewrite al_eq; clear al_eq.
    destruct a as [α v]; cbn; clear v.
    destruct al as [al al_comb].
    induction al.
    {
        cbn.
        rewrite scalar_ranni.
        rewrite plus_lid.
        exists bl.
        split.
        -   reflexivity.
        -   exact Sbl.
    }
    cbn in *.
    assert (linear_combination_set al) as al_comb'.
    {
        apply al_comb.
    }
    assert (∀ v, (∃ α, in_list al (α, v)) → S v) as Sal'.
    {
        intros v [b v_in].
        apply Sal.
        exists b.
        right.
        exact v_in.
    }
    specialize (IHal al_comb' Sal').
    rewrite scalar_ldist.
    rewrite <- plus_assoc.
    destruct IHal as [l [l_eq Sl]].
    destruct a as [β v]; cbn in *.
    assert (S v) as Sv.
    {
        apply Sal.
        exists β.
        left; reflexivity.
    }
    rewrite l_eq; clear al al_comb bl Sbl l_eq al_comb' Sal Sal'.
    destruct l as [l l_comb].
    cbn in Sl.
    rewrite scalar_comp.
    classic_case (∃ a, in_list l (a, v)) as [v_in|v_nin].
    -   destruct v_in as [a v_in].
        pose proof (in_list_split l (a, v) v_in) as [l1 [l2 eq]].
        subst l; cbn.
        rewrite list_image_conc; cbn.
        rewrite list_sum_plus; cbn.
        rewrite plus_assoc.
        rewrite (plus_comm (α * β · v)).
        rewrite <- plus_assoc.
        rewrite (plus_assoc _ (a · v)).
        rewrite <- scalar_rdist.
        remember (α * β + a) as a'.
        pose (l' := l1 ++ (a', v) :: l2).
        assert (linear_combination_set l') as l'_comb.
        {
            unfold l'.
            clear α β v_in Sl Sv Heqa' l'.
            unfold linear_combination_set in *.
            assert (list_image (l1 ++ (a, v) :: l2) snd =
                    list_image (l1 ++ (a', v) :: l2) snd) as l_eq.
            {
                clear l_comb.
                induction l1.
                -   cbn.
                    reflexivity.
                -   cbn.
                    rewrite IHl1.
                    reflexivity.
            }
            rewrite <- l_eq.
            exact l_comb.
        }
        exists [l'|l'_comb].
        split.
        +   unfold l'; cbn.
            rewrite list_image_conc; cbn.
            rewrite list_sum_plus; cbn.
            reflexivity.
        +   cbn.
            unfold l'.
            intros u [b b_in].
            apply Sl.
            apply in_list_conc in b_in.
            cbn in b_in.
            destruct b_in as [b_in|[b_eq|b_in]].
            *   exists b.
                apply in_list_lconc.
                exact b_in.
            *   inversion b_eq; clear b_eq.
                subst b u.
                exists a.
                apply in_list_rconc.
                left.
                reflexivity.
            *   exists b.
                apply in_list_rconc.
                right.
                exact b_in.
    -   pose (l' := (α * β, v) :: l).
        assert (linear_combination_set l') as l'_comb.
        {
            unfold l'; cbn.
            split.
            2: exact l_comb.
            intros v_in.
            clear l' Sl l_comb Sv α β.
            induction l.
            -   contradiction v_in.
            -   classic_case (snd a = v) as [eq|neq].
                +   subst v.
                    apply v_nin.
                    exists (fst a).
                    left.
                    destruct a; reflexivity.
                +   apply IHl.
                    *   intros [b v_in'].
                        apply v_nin.
                        exists b.
                        right.
                        exact v_in'.
                    *   destruct v_in as [eq|v_in].
                        --  contradiction.
                        --  exact v_in.
        }
        exists [l'|l'_comb].
        split.
        +   unfold l'; cbn.
            reflexivity.
        +   cbn.
            intros u [a [u_eq|u_in]].
            *   inversion u_eq; clear u_eq.
                subst a u.
                exact Sv.
            *   apply Sl.
                exists a.
                exact u_in.
Qed.

Theorem linear_combination_of_scalar : ∀ S a v,
        linear_combination_of S v → linear_combination_of S (a · v).
    intros S a v v_comb.
    pose (l := (a, v) :: list_end).
    assert (linear_combination_set l) as l_comb.
    {
        cbn.
        rewrite not_false.
        split; exact true.
    }
    pose proof (linear_combination_of_combination S [l|l_comb]) as eq.
    cbn in eq.
    rewrite plus_rid in eq.
    apply eq; clear eq.
    intros u [b [u_eq|contr]].
    2: contradiction contr.
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
    pose (l := (1, u) :: (1, v) :: list_end).
    assert (linear_combination_set l) as l_comb.
    {
        cbn.
        rewrite not_or.
        rewrite not_false.
        repeat split; try exact true.
        rewrite neq_sym; exact neq.
    }
    pose proof (linear_combination_of_combination S [l|l_comb]) as eq.
    cbn in eq.
    do 2 rewrite scalar_id in eq.
    rewrite plus_rid in eq.
    apply eq; clear eq.
    intros w [a [w_eq|[w_eq|contr]]].
    3: contradiction contr.
    all: inversion w_eq; subst.
    -   exact u_comb.
    -   exact v_comb.
Qed.

(* begin hide *)
End LinearBase.
(* end hide *)
