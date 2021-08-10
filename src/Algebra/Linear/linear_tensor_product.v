(*
Require Import init.

Require Export linear_base.
Require Import linear_free.
Require Import linear_subspace.
Require Import linear_span.
Require Import set.
Require Import card.
Require Import plus_sum.

Section TensorProduct.

Context {U V1 V2} `{
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
    @NotTrivial U UZ UO,

    UV1 : Plus V1,
    UV2 : Plus V2,
    UZ1 : Zero V1,
    UZ2 : Zero V2,

    SM1 : ScalarMult U V1,
    SM2 : ScalarMult U V2
}.

Let FR := free_linear U (V1 * V2).
Let to_FR a b := to_free U (V1 * V2) (a, b).

Let FR_plus := free_plus_class U (V1 * V2).
Let FR_zero := free_zero U (V1 * V2).
Let FR_neg := free_neg U (V1 * V2).
Let FR_plus_comm := free_plus_comm_class U (V1 * V2).
Let FR_plus_assoc := free_plus_assoc_class U (V1 * V2).
Let FR_plus_lid := free_plus_lid_class U (V1 * V2).
Let FR_plus_linv := free_plus_linv_class U (V1 * V2).
Let FR_scalar := free_scalar U (V1 * V2).
Let FR_scalar_ldist := free_scalar_ldist_class U (V1 * V2).
Existing Instances FR_plus FR_zero FR_neg FR_plus_comm FR_plus_assoc FR_plus_lid
    FR_plus_linv FR_scalar FR_scalar_ldist.

Let sub1 v := ∃ a b c, v = to_FR (a + b) c - to_FR a c - to_FR b c.
Let sub2 v := ∃ a b c, v = to_FR a (b + c) - to_FR a b - to_FR a c.
Let sub3 v := ∃ a m n, v = a · to_FR m n - to_FR (a · m) n.
Let sub4 v := ∃ a m n, v = a · to_FR m n - to_FR m (a · n).
Let sub := sub1 ∪ sub2 ∪ sub3 ∪ sub4.

Definition tensor_space := linear_span_quotient U sub.
Definition tensor_mult a b := to_quotient U sub (to_free U (V1 * V2) (a, b)).
Infix "⊗" := tensor_mult : algebra_scope.

Definition tensor_plus := quotient_space_plus (linear_span_subspace U sub).
Definition tensor_zero := quotient_space_zero (linear_span_subspace U sub).
Definition tensor_scalar_mult
    := quotient_space_scalar_mult (linear_span_subspace U sub).
Existing Instances tensor_plus tensor_zero tensor_scalar_mult.

Theorem tensor_ldist : ∀ a b c, a ⊗ (b + c) = a ⊗ b + a ⊗ c.
    intros a b c.
    unfold tensor_mult; cbn.
    unfold plus at 2; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    left; left; right.
    exists a, b, c.
    unfold to_FR.
    rewrite neg_plus.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem tensor_rdist : ∀ a b c, (a + b) ⊗ c = a ⊗ c + b ⊗ c.
    intros a b c.
    unfold tensor_mult, plus at 2; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    repeat left.
    exists a, b, c.
    unfold to_FR.
    rewrite neg_plus.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem tensor_lscalar : ∀ a u v, (a · u) ⊗ v = a · (u ⊗ v).
    intros a u v.
    symmetry.
    unfold tensor_mult, scalar_mult; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    left; right.
    exists a, u, v; cbn.
    unfold to_FR.
    reflexivity.
Qed.

Theorem tensor_rscalar : ∀ a u v, u ⊗ (a · v) = a · (u ⊗ v).
    intros a u v.
    symmetry.
    unfold tensor_mult, scalar_mult; cbn.
    unfold to_quotient; equiv_simpl.
    intros S S_sub.
    apply S_sub.
    right.
    exists a, u, v; cbn.
    unfold to_FR.
    reflexivity.
Qed.

Definition simple_tensor T := ∃ a b, T = a ⊗ b.

Local Open Scope card_scope.

Theorem tensor_sum : ∀ T, ∃ (f : nat0 → tensor_space) n,
        (∀ m, m < n → simple_tensor (f m)) ∧
        T = sum f 0 n.
    intros T.
    equiv_get_value T.
    destruct T as [Tf Tf_fin].
    pose proof (fin_nat0_ex _ Tf_fin) as [n n_eq].
    unfold nat0_to_card in n_eq; equiv_simpl in n_eq.
    destruct n_eq as [nf nf_bij].
    pose (f m := match (strong_excluded_middle (m < n)) with
        | strong_or_left ltq =>
            Tf [nf [m|ltq]|] · (fst [nf [m|ltq]|] ⊗ snd [nf [m|ltq]|])
        | strong_or_right _ => 0
        end).
    exists f, n.
    split.
    -   intros m m_ltq.
        unfold f.
        destruct (strong_excluded_middle _) as [ltq|leq].
        +   exists (Tf [nf [m|ltq]|] · fst [nf [m|ltq]|]), (snd [nf [m|ltq]|]).
            rewrite tensor_lscalar.
            reflexivity.
        +   contradiction.
    -   revert nf nf_bij f.
        revert Tf Tf_fin.
        nat0_induction n.
        +   intros.
            unfold zero at 2; cbn.
            unfold zero; equiv_simpl.
            apply f_equal.
            apply free_eq.
            intros [u v]; cbn.
            unfold zero; cbn.
            classic_contradiction contr.
            pose proof (rand nf_bij [(u, v)|contr]) as [x x_eq].
            contradiction (nat0_lt_0_false x).
        +   intros.
            cbn.
            pose (Tf' x := If x = [nf [n|nat0_lt_suc n]|] then 0 else Tf x).
            assert (∀ x, Tf' x ≠ 0 → Tf x ≠ 0) as Tf'_neq.
            {
                intros x.
                unfold Tf'.
                case_if.
                -   intros contr; contradiction.
                -   trivial.
            }
            assert (finite (|set_type (λ x, Tf' x ≠ 0)|)) as Tf'_fin.
            {
                apply (le_lt_trans2 Tf_fin).
                unfold le; equiv_simpl.
                exists (λ x, [[x|] | Tf'_neq [x|] [|x]]).
                intros a b eq.
                inversion eq as [eq2].
                apply set_type_eq; exact eq2.
            }
            assert (∀ m : (set_type (λ x, x < n)),
                let res := nf [[m|]|trans [|m] (nat0_lt_suc n)] in
                Tf [res|] ≠ 0 → Tf' [res|] ≠ 0) as Tf'_neq2.
            {
                intros [m m_ltq]; cbn.
                intros eq.
                unfold Tf'; case_if.
                -   apply set_type_eq in e.
                    apply nf_bij in e.
                    inversion e.
                    subst.
                    destruct m_ltq; contradiction.
                -   exact eq.
            }
            pose (nf' (x : set_type (λ x, x < n))
                := let res := nf [[x|]|trans [|x] (nat0_lt_suc n)] in
                    [[res|] | Tf'_neq2 _ [|res]] : set_type (λ x, Tf' x ≠ 0)).
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
                    specialize (Tf'_neq y y_neq).
                    pose proof (rand nf_bij [y|Tf'_neq]) as [[x x_ltq] eq].
                    pose proof x_ltq as x_ltq2.
                    rewrite nat0_lt_suc_le in x_ltq2.
                    classic_case (x = n) as [x_eq|x_neq].
                    +   exfalso.
                        subst.
                        unfold Tf' in y_neq.
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
            pose (f' m := match (strong_excluded_middle (m < n)) with
                | strong_or_left ltq =>
                  Tf' [nf' [m|ltq]|] · (fst [nf' [m|ltq]|] ⊗ snd [nf' [m|ltq]|])
                | strong_or_right _ => 0
                end).
            specialize (IHn Tf' Tf'_fin nf' nf'_bij).
            fold f' in IHn.
            cbn in IHn.
            assert (sum (U := tensor_space) f 0 n =
                    sum (U := tensor_space) f' 0 n) as sum_eq.
            {
                apply sum_eq.
                intros m m_ltq.
                rewrite plus_lid.
                unfold f'.
                destruct (strong_excluded_middle _) as [ltq|ltq].
                2: contradiction.
                unfold f.
                destruct (strong_excluded_middle _) as [ltq2|ltq2].
                2: {
                    rewrite nlt_le in ltq2.
                    pose proof (le_lt_trans ltq2 m_ltq) as eq.
                    pose proof (nat0_le_suc n).
                    rewrite <- nle_lt in eq.
                    contradiction.
                }
                unfold Tf'.
                case_if.
                -   unfold nf' in e; cbn in e.
                    apply set_type_eq in e.
                    apply nf_bij in e.
                    inversion e as [eq].
                    rewrite eq in m_ltq.
                    destruct m_ltq; contradiction.
                -   unfold nf'; cbn.
                    unfold tensor_mult, to_quotient, scalar_mult; equiv_simpl.
                    apply f_equal.
                    apply free_eq; cbn.
                    rewrite (proof_irrelevance (trans _ _) ltq2).
                    reflexivity.
            }
            rewrite sum_eq.
            rewrite <- IHn.
            rewrite plus_lid.
            unfold f.
            destruct (strong_excluded_middle _) as [ltq|contr].
            2: {
                contradiction (contr (nat0_lt_suc n)).
            }
            unfold tensor_mult, to_quotient, scalar_mult; cbn.
            unfold plus; equiv_simpl.
            apply f_equal.
            unfold plus; cbn.
            apply free_eq; cbn.
            intros [u v].
            unfold Tf'.
            rewrite (proof_irrelevance (nat0_lt_suc n) ltq).
            assert ((fst [nf [n|ltq]|], snd [nf [n|ltq]|]) = [nf [n|ltq]|])
                as eq.
            {
                destruct [nf [n|ltq]|]; cbn.
                reflexivity.
            }
            rewrite eq.
            unfold scalar_mult; cbn.
            case_if.
            *   rewrite e, plus_lid.
                rewrite mult_rid.
                reflexivity.
            *   rewrite mult_ranni.
                rewrite plus_rid.
                reflexivity.
Qed.

End TensorProduct.
*)
