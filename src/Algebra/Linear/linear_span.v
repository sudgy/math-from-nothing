Require Import init.

Require Export linear_base.
Require Import linear_subspace.
Require Import set.
Require Import list.
Require Import plus_sum.

Definition linear_span U {V} `{Plus V, Zero V, Neg V, ScalarMult U V}
    (S : V → Prop) :=
    λ v, ∀ sub : Subspace U V, S ⊆ subspace_set sub → subspace_set sub v.

Section Span.

Context U {V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    UD : Div U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
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
    @ScalarComp U V UM SM,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM
}.
Variable A : V → Prop.

Let S := linear_span U A.

Lemma linear_span_zero : S 0.
    intros [T T_zero T_plus T_scalar]; cbn.
    intros sub.
    exact T_zero.
Qed.
Lemma linear_span_plus : ∀ a b, S a → S b → S (a + b).
    intros a b Sa Sb T sub.
    specialize (Sa T sub).
    specialize (Sb T sub).
    apply subspace_plus; assumption.
Qed.
Lemma linear_span_scalar : ∀ a v, S v → S (a · v).
    intros a v Sv T sub.
    specialize (Sv T sub).
    apply subspace_scalar.
    exact Sv.
Qed.

Definition linear_span_subspace := make_subspace S
    linear_span_zero linear_span_plus linear_span_scalar.

Theorem linear_span_sub : A ⊆ S.
    intros v Av.
    unfold S, linear_span.
    intros sub A_sub.
    apply A_sub.
    exact Av.
Qed.

Definition linear_span_quotient := quotient_space linear_span_subspace.
Definition to_quotient v :=
    to_equiv_type (subspace_equiv linear_span_subspace) v.
Definition linear_span_quotient_plus
    := quotient_space_plus linear_span_subspace.
Definition linear_span_quotient_plus_assoc
    := quotient_space_plus_assoc linear_span_subspace.
Definition linear_span_quotient_plus_comm
    := quotient_space_plus_comm linear_span_subspace.
Definition linear_span_quotient_zero
    := quotient_space_zero linear_span_subspace.
Definition linear_span_quotient_plus_lid
    := quotient_space_plus_lid linear_span_subspace.
Definition linear_span_quotient_neg
    := quotient_space_neg linear_span_subspace.
Definition linear_span_quotient_plus_linv
    := quotient_space_plus_linv linear_span_subspace.
Definition linear_span_quotient_scalar_mult
    := quotient_space_scalar_mult linear_span_subspace.
Definition linear_span_quotient_scalar_comp
    := quotient_space_scalar_comp linear_span_subspace.
Definition linear_span_quotient_scalar_id
    := quotient_space_scalar_id linear_span_subspace.
Definition linear_span_quotient_scalar_ldist
    := quotient_space_scalar_ldist linear_span_subspace.
Definition linear_span_quotient_scalar_rdist
    := quotient_space_scalar_rdist linear_span_subspace.

Theorem span_linear_combination :
        S = (λ v, ∃ l,
            (∀ v, (∃ α, in_list l (α, v)) → S v) ∧ v = linear_combination l
        ).
    pose (L u := ∃ l,
        (∀ v, (∃ α, in_list l (α, v)) → S v) ∧ u = linear_combination l).
    assert (L 0) as L_zero.
    {
        exists list_end.
        split.
        -   intros v [α v_in].
            cbn in v_in.
            contradiction v_in.
        -   cbn.
            reflexivity.
    }
    assert (∀ u v, L u → L v → L (u + v)) as L_plus.
    {
        intros u v Lu Lv.
        destruct Lu as [ul [Sul u_eq]].
        destruct Lv as [vl [Svl v_eq]].
        subst u v.
        exists (ul ++ vl).
        split.
        -   intros v [α v_in].
            apply in_list_conc in v_in as [v_in|v_in].
            +   apply Sul.
                exists α.
                exact v_in.
            +   apply Svl.
                exists α.
                exact v_in.
        -   unfold linear_combination.
            rewrite list_image_conc.
            rewrite list_sum_plus.
            reflexivity.
    }
    assert (∀ a v, L v → L (a · v)) as L_scalar.
    {
        intros α v [l [Sl v_eq]].
        subst v.
        classic_case (0 = α) as [α_z|α_nz].
        {
            subst α.
            rewrite scalar_lanni.
            exact L_zero.
        }
        exists (list_image l (λ a, (α * fst a, snd a))).
        split.
        -   intros v [β v_in].
            apply Sl.
            exists (/α * β).
            clear Sl.
            induction l.
            +   cbn in v_in.
                contradiction v_in.
            +   cbn.
                destruct a as [γ u]; cbn in *.
                destruct v_in as [eq|v_in].
                *   left.
                    inversion eq.
                    apply f_equal2; try reflexivity.
                    rewrite mult_llinv by exact α_nz.
                    reflexivity.
                *   right.
                    exact (IHl v_in).
        -   clear Sl.
            induction l.
            +   cbn.
                apply scalar_ranni.
            +   cbn.
                unfold linear_combination in IHl.
                rewrite scalar_ldist.
                rewrite IHl.
                rewrite scalar_comp.
                reflexivity.
    }
    pose (L_sub := make_subspace L L_zero L_plus L_scalar).
    apply antisym.
    -   intros v Sv.
        unfold S, linear_span in Sv.
        apply (Sv L_sub).
        cbn.
        clear v Sv.
        intros v Av.
        exists ((1, v) :: list_end).
        split.
        +   intros u [α u_in].
            cbn in u_in.
            destruct u_in as [u_in|u_in].
            2: contradiction u_in.
            inversion u_in.
            subst.
            apply linear_span_sub.
            exact Av.
        +   cbn.
            rewrite scalar_id.
            rewrite plus_rid.
            reflexivity.
    -   intros v [l [Sv v_eq]].
        rewrite v_eq; clear v_eq.
        apply (subspace_linear_combination linear_span_subspace).
        cbn.
        exact Sv.
Qed.

End Span.
