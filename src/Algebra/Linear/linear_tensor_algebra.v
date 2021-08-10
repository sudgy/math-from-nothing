Require Import init.

Require Export linear_base.
Require Import linear_free.
Require Import linear_subspace.
Require Import linear_span.

Require Export list.
Require Import set.
Require Import card.
Require Import plus_sum.

Section TensorAlgebra.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @MultAssoc U UM,
    @MultComm U UM,
    @MultLid U UM UO,
    @Ldist U UP UM,
    @NotTrivial U UZ UO,

    VP : Plus V,
    VZ : Zero V,

    SM : ScalarMult U V
}.

Let FR := free_linear U (list V).
Let to_FR vs := to_free U (list V) vs.

Let FR_plus := free_plus_class U (list V).
Let FR_zero := free_zero U (list V).
Let FR_neg := free_neg U (list V).
Let FR_plus_comm := free_plus_comm_class U (list V).
Let FR_plus_assoc := free_plus_assoc_class U (list V).
Let FR_plus_lid := free_plus_lid_class U (list V).
Let FR_plus_linv := free_plus_linv_class U (list V).
Let FR_scalar := free_scalar U (list V).
Let FR_scalar_id := free_scalar_id_class U (list V).
Let FR_scalar_comp := free_scalar_comp_class U (list V).
Let FR_scalar_ldist := free_scalar_ldist_class U (list V).
Let FR_scalar_rdist := free_scalar_rdist_class U (list V).
Existing Instances FR_plus FR_zero FR_neg FR_plus_comm FR_plus_assoc FR_plus_lid
    FR_plus_linv FR_scalar FR_scalar_id FR_scalar_comp FR_scalar_ldist
    FR_scalar_rdist.

Let sub1 v := ∃ vs1 al bl vs2, v =
    to_FR (vs1 ++ (al ++ bl) ++ vs2)
    - to_FR (vs1 ++ al ++ vs2) - to_FR (vs1 ++ bl ++ vs2).
Let sub2 v := ∃ a vs1 u vs2, v =
    a · to_FR (vs1 ++ u :: vs2) - to_FR (vs1 ++ (a · u) :: vs2).
Let sub := sub1 ∪ sub2.

Definition tensor_algebra := linear_span_quotient U sub.
Definition to_tensor_algebra x := to_quotient U sub (to_FR x).
Definition tensor_plus := quotient_space_plus (linear_span_subspace U sub).
Definition tensor_plus_comm
    := quotient_space_plus_comm (linear_span_subspace U sub).
Definition tensor_plus_assoc
    := quotient_space_plus_assoc (linear_span_subspace U sub).
Definition tensor_zero := quotient_space_zero (linear_span_subspace U sub).
Definition tensor_plus_lid
    := quotient_space_plus_lid (linear_span_subspace U sub).
Definition tensor_neg := quotient_space_neg (linear_span_subspace U sub).
Definition tensor_plus_linv
    := quotient_space_plus_linv (linear_span_subspace U sub).
Definition tensor_scalar_mult
    := quotient_space_scalar_mult (linear_span_subspace U sub).
Definition tensor_scalar_comp
    := quotient_space_scalar_comp (linear_span_subspace U sub).
Definition tensor_scalar_id
    := quotient_space_scalar_id (linear_span_subspace U sub).
Definition tensor_scalar_ldist
    := quotient_space_scalar_ldist (linear_span_subspace U sub).
Definition tensor_scalar_rdist
    := quotient_space_scalar_rdist (linear_span_subspace U sub).
Existing Instances tensor_plus tensor_plus_comm tensor_plus_assoc tensor_zero
    tensor_neg tensor_plus_linv tensor_plus_lid tensor_scalar_mult
    tensor_scalar_comp tensor_scalar_id tensor_scalar_ldist tensor_scalar_rdist.

Definition simple_tensor_scale x := ∃ α b, x = α · (to_tensor_algebra b).

Lemma simple_tensor_neg_simple :
        ∀ x : set_type simple_tensor_scale, simple_tensor_scale (-[x|]).
    intros [x [α [b eq]]].
    exists (-α), b.
    cbn.
    rewrite eq.
    rewrite scalar_lneg.
    reflexivity.
Qed.

Definition simple_tensor_neg x := [-[x|] | simple_tensor_neg_simple x].

Local Open Scope card_scope.

Theorem tensor_sum : ∀ a, ∃ (l : list (set_type simple_tensor_scale)),
        a = list_sum (list_image l (λ x, [x|])).
    intros a.
    equiv_get_value a.
    destruct a as [af af_fin].
    pose proof (fin_nat_ex _ af_fin) as [n n_eq].
    unfold nat_to_card in n_eq; equiv_simpl in n_eq.
    destruct n_eq as [nf nf_bij].
    revert af af_fin nf nf_bij.
    nat_induction n.
    -   intros.
        exists list_end.
        cbn.
        unfold zero; cbn.
        apply f_equal.
        apply free_eq; cbn.
        intros x.
        unfold zero; cbn.
        classic_contradiction contr.
        pose proof (rand nf_bij [x|contr]) as [m m_eq].
        contradiction (nat_lt_0_false m).
    -   intros.
        pose (af' x := If x = [nf [n|nat_lt_suc n]|] then 0 else af x).
        assert (∀ x, af' x ≠ 0 → af x ≠ 0) as af'_neq.
        {
            intros x.
            unfold af'.
            case_if.
            -   intros contr; contradiction.
            -   trivial.
        }
        assert (finite (|set_type (λ x, af' x ≠ 0)|)) as af'_fin.
        {
            apply (le_lt_trans2 af_fin).
            unfold le; equiv_simpl.
            exists (λ x, [[x|] | af'_neq [x|] [|x]]).
            intros a b eq.
            inversion eq as [eq2].
            apply set_type_eq; exact eq2.
        }
        assert (∀ m : (set_type (λ x, x < n)),
            let res := nf [[m|]|trans [|m] (nat_lt_suc n)] in
            af [res|] ≠ 0 → af' [res|] ≠ 0) as af'_neq2.
        {
            intros [m m_ltq]; cbn.
            intros eq.
            unfold af'; case_if.
            -   apply set_type_eq in e.
                apply nf_bij in e.
                inversion e.
                subst.
                destruct m_ltq; contradiction.
            -   exact eq.
        }
        pose (nf' (x : set_type (λ x, x < n))
            := let res := nf [[x|]|trans [|x] (nat_lt_suc n)] in
                [[res|] | af'_neq2 _ [|res]] : set_type (λ x, af' x ≠ 0)).
        assert (bijective nf') as nf'_bij.
        {
            unfold nf'.
            split.
            -   intros a b eq.
                inversion eq as [eq2].
                apply set_type_eq in eq2.
                apply nf_bij in eq2.
                inversion eq2 as [eq3].
                apply set_type_eq; exact eq3.
            -   intros [y y_neq].
                specialize (af'_neq y y_neq).
                pose proof (rand nf_bij [y|af'_neq]) as [[x x_ltq] eq].
                pose proof x_ltq as x_ltq2.
                rewrite nat_lt_suc_le in x_ltq2.
                classic_case (x = n) as [x_eq|x_neq].
                +   exfalso.
                    subst.
                    unfold af' in y_neq.
                    case_if.
                    *   contradiction.
                    *   rewrite (proof_irrelevance _ x_ltq) in n0.
                        rewrite eq in n0.
                        contradiction.
                +   exists [x|make_and x_ltq2 x_neq].
                    apply set_type_eq; cbn.
                    rewrite (proof_irrelevance _ x_ltq).
                    rewrite eq.
                    reflexivity.
        }
        specialize (IHn af' af'_fin nf' nf'_bij) as [l l_eq].
        pose (fn := af [nf [n|nat_lt_suc n]|] ·
            to_tensor_algebra [nf [n|nat_lt_suc n]|]).
        assert (simple_tensor_scale fn) as fn_in.
        {
            exists (af [nf [n|nat_lt_suc n]|]), ([nf [n | nat_lt_suc n]|]).
            reflexivity.
        }
        exists (l ++ [fn|fn_in] :: list_end).
        rewrite list_image_conc.
        rewrite list_sum_plus.
        rewrite <- l_eq.
        cbn.
        rewrite plus_rid.
        unfold plus; cbn.
        unfold fn.
        unfold to_tensor_algebra, to_quotient.
        unfold scalar_mult; cbn.
        rewrite equiv_binary_rself_op.
        rewrite equiv_binary_self_op.
        apply f_equal.
        apply free_eq; cbn.
        intros x.
        unfold af'.
        unfold plus; cbn.
        unfold scalar_mult; cbn.
        case_if.
        *   rewrite plus_lid.
            rewrite mult_rid.
            rewrite e.
            reflexivity.
        *   rewrite mult_ranni.
            rewrite plus_rid.
            reflexivity.
Qed.

Definition tensor_product_base (a b : set_type simple_tensor_scale) :=
    (ex_val [|a] * ex_val [|b]) ·
    to_tensor_algebra (ex_val (ex_proof [|a]) ++ ex_val (ex_proof [|b])).

Instance tensor_mult : Mult tensor_algebra := {
    mult a b := list_sum (list_prod2 tensor_product_base
        (ex_val (tensor_sum a))
        (ex_val (tensor_sum b)))
}.

Infix "⊗" := (mult (U := tensor_algebra)) : algebra_scope.

Theorem tensor_lscalar : ∀ γ a b, (γ · a) ⊗ b = γ · (a ⊗ b).
    intros γ a b.
    unfold mult; cbn.
    rewrite_ex_val γal γal_eq.
    rewrite_ex_val bl bl_eq.
    rewrite_ex_val al al_eq.
    subst.
    induction bl.
    {
        cbn.
        rewrite scalar_ranni.
        reflexivity.
    }
    cbn.
    do 2 rewrite list_sum_plus.
    rewrite IHbl.
    rewrite scalar_ldist.
    apply rplus.
    clear IHbl bl.
Abort.

Lemma tensor_rscalar1 : ∀ α a b bH,
        tensor_product_base a [α · [b|] | bH] =
        α · (tensor_product_base a b).
    intros α a b bH.
    unfold tensor_product_base.
    destruct a as [a a_simple]; cbn.
    destruct b as [b b_simple]; cbn in *.
    unfold ex_val at 1 5.
    unfold ex_proof at 1 3.
    destruct (ex_to_type a_simple) as [β βH]; cbn.
    unfold ex_val at 2 5.
    destruct (ex_to_type βH) as [al a_eq]; cbn in *.
    clear βH.
    subst a.
    unfold ex_val at 1, ex_proof at 1.
    destruct (ex_to_type bH) as [γ γH]; cbn.
    unfold ex_val at 1.
    destruct (ex_to_type γH) as [αbl αb_eq]; cbn in *.
    clear γH.
    unfold ex_val at 1, ex_proof.
    destruct (ex_to_type b_simple) as [δ δH]; cbn.
    unfold ex_val.
    destruct (ex_to_type δH) as [bl b_eq]; cbn in *.
    subst b.
    clear a_simple b_simple δH bH.
    rewrite scalar_comp.
    unfold to_tensor_algebra, to_quotient.
    unfold scalar_mult; equiv_simpl.
    rewrite scalar_comp in αb_eq.
    unfold to_tensor_algebra, to_quotient in αb_eq.
    unfold scalar_mult in αb_eq; equiv_simpl in αb_eq.
    intros subs subs_sub.
    rewrite <- scalar_lneg.
    rewrite <- mult_lneg.
    rewrite (mult_comm (-α) _).
    rewrite <- mult_assoc.
    do 2 rewrite <- scalar_comp.
    rewrite <- scalar_ldist.
    apply subspace_scalar.
    rewrite <- neg_neg.
    apply subspace_neg.
    rewrite neg_plus.
    rewrite plus_comm.
    rewrite <- scalar_lneg.
    rewrite mult_rneg.
    rewrite neg_neg.
    rewrite mult_comm.

    (*
    induction al.
    {
        cbn.
        apply αb_eq.
        exact subs_sub.
    }
    *)


    destruct bl.
    {
        destruct αbl.
        -   admit.
        -   admit.
    }
    destruct αbl.
    {
        admit.
    }
Admitted.

Lemma tensor_ldist1 : ∀ a bl cl,
        list_sum (list_image bl (λ x, [x|])) =
        list_sum (list_image cl (λ x, [x|])) →
        list_sum (list_image bl (λ x, tensor_product_base a x)) =
        list_sum (list_image cl (λ x, tensor_product_base a x)).
    intros a bl cl eq.
    revert cl eq.
    induction bl.
    {
        cbn; intros cl eq.
        admit.
    }
    intros.
    cbn in *.
    specialize (IHbl ((simple_tensor_neg a0) :: cl)).
    rewrite IHbl; clear IHbl.
    2: {
        cbn.
        rewrite <- eq.
        rewrite plus_llinv.
        reflexivity.
    }
    clear eq.
    cbn.
    assert (tensor_product_base a (simple_tensor_neg a0)
        = -tensor_product_base a a0) as eq.
    {
        unfold simple_tensor_neg.
        pose proof (scalar_neg_one [a0|]) as eq.
        assert (simple_tensor_scale (-(1) · [a0|])) as stupid.
        {
            rewrite eq.
            apply simple_tensor_neg_simple.
        }
        assert ([-[a0|] | simple_tensor_neg_simple a0] = [_|stupid]) as eq2.
        {
            apply set_type_eq; cbn.
            symmetry; exact eq.
        }
        rewrite eq2.
        rewrite tensor_rscalar1.
        rewrite scalar_neg_one.
        reflexivity.
    }
    rewrite eq; clear eq.
    rewrite plus_lrinv.
    reflexivity.
Admitted.

Lemma tensor_ldist : ∀ a b c, a ⊗ (b + c) = a ⊗ b + a ⊗ c.
    intros a b c.
    unfold mult; cbn.
    rewrite_ex_val al al_eq.
    rewrite_ex_val bcl bcl_eq.
    rewrite_ex_val bl bl_eq.
    rewrite_ex_val cl cl_eq.
    subst a b c.
    rewrite <- list_sum_plus in bcl_eq.
    rewrite <- list_image_conc in bcl_eq.
    assert (list_sum (list_prod2 tensor_product_base al (bl ++ cl)) =
            list_sum (list_prod2 tensor_product_base al bcl)) as bcl_eq'.
    {
        induction al.
        {
            do 2 rewrite list_prod2_lend.
            reflexivity.
        }
        do 2 rewrite list_prod2_lconc.
        rewrite IHal; clear IHal.
        apply lplus.
        clear al.
        rewrite (tensor_ldist1 _ _ _ bcl_eq).
        reflexivity.
    }
    rewrite <- bcl_eq'.
    clear bcl_eq bcl_eq'.
    induction bl.
    {
        cbn.
        rewrite plus_lid.
        reflexivity.
    }
    cbn.
    do 2 rewrite list_sum_plus.
    rewrite IHbl.
    apply plus_assoc.
Admitted.

Instance tensor_ldist_class : Ldist tensor_algebra := {
    ldist := tensor_ldist
}.

Lemma tensor_mult_assoc : ∀ a b c, a ⊗ (b ⊗ c) = (a ⊗ b) ⊗ c.
Admitted.

Instance tensor_mult_assoc_class : MultAssoc tensor_algebra := {
    mult_assoc := tensor_mult_assoc
}.

End TensorAlgebra.
