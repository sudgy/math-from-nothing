Require Import init.

Require Export geometric_construction2.
Require Import plus_sum.
Require Import linear_free.
Require Import card.
Require Import list.
Require Import set.

Section GA3.

Context {V : Type}.
Variable metric : ga_metric V.

Context U `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @MultComm U UM,
    @MultLid U UM UO,
    @Ldist U UP UM,
    @NotTrivial U UZ UO
}.

Let ga2' := ga2 metric.

Definition ga3 := free_linear U ga2'.
Definition ga23 b := to_free U ga2' b.
Definition ga13 b := ga23 (ga12 metric b).

Definition ga3_plus := free_plus_class U ga2'.
Definition ga3_zero := free_zero U ga2'.
Definition ga3_neg := free_neg U ga2'.
Definition ga3_plus_comm := free_plus_comm_class U ga2'.
Definition ga3_plus_assoc := free_plus_assoc_class U ga2'.
Definition ga3_plus_lid := free_plus_lid_class U ga2'.
Definition ga3_plus_linv := free_plus_linv_class U ga2'.
Definition ga3_scalar := free_scalar U ga2'.
Definition ga3_scalar_ldist := free_scalar_ldist_class U ga2'.
Definition ga3_scalar_rdist := free_scalar_rdist_class U ga2'.
Existing Instances ga3_plus ga3_zero ga3_neg ga3_plus_comm ga3_plus_assoc
    ga3_plus_lid ga3_plus_linv ga3_scalar ga3_scalar_ldist ga3_scalar_rdist.

Definition ga3_basis_scale x := ∃ α b, x = α · ga23 b.

Local Open Scope card_scope.

Theorem ga3_decompose_basis : ∀ a,
        ∃ (l : list (set_type ga3_basis_scale)),
        a = list_sum (list_image l (λ x, [x|])).
    intros a.
    destruct a as [af af_fin].
    pose proof (fin_nat_ex _ af_fin) as [n n_eq].
    unfold nat_to_card in n_eq; equiv_simpl in n_eq.
    destruct n_eq as [nf nf_bij].
    revert af af_fin nf nf_bij.
    nat_induction n.
    -   intros.
        exists list_end.
        cbn.
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
            to_free U ga2' [nf [n|nat_lt_suc n]|]).
        assert (ga3_basis_scale fn) as fn_in.
        {
            exists (af [nf [n|nat_lt_suc n]|]), [nf [n | nat_lt_suc n]|].
            reflexivity.
        }
        exists (l ++ [fn|fn_in] :: list_end).
        rewrite list_image_conc.
        rewrite list_sum_plus.
        rewrite <- l_eq.
        cbn.
        unfold plus; cbn.
        apply free_eq; cbn.
        intros x.
        unfold af'.
        unfold zero at 7; cbn.
        rewrite plus_rid.
        unfold fn, scalar_mult; cbn.
        case_if.
        *   rewrite plus_lid.
            rewrite mult_rid.
            rewrite e.
            reflexivity.
        *   rewrite mult_ranni.
            rewrite plus_rid.
            reflexivity.
Qed.

End GA3.
