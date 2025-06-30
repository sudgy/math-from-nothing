Require Import init.

Require Export card_infinite_arithmetic.
Require Export set.

Open Scope card_scope.
Open Scope set_scope.

Theorem card_le_sub : ∀ κ A, κ ≤ |A| → ∃ S : A → Prop, |set_type S| = κ.
Proof.
    intros U A U_le.
    equiv_get_value U.
    unfold le in U_le; equiv_simpl in U_le.
    destruct U_le as [f f_inj].
    exists (image f).
    symmetry.
    equiv_simpl.
    exists (λ a, [f a|ex_intro _ a Logic.eq_refl]).
    split; split.
    -   intros a b eq.
        rewrite set_type_eq2 in eq.
        apply inj in eq.
        exact eq.
    -   intros [y [x eq]].
        exists x.
        rewrite set_type_eq2.
        symmetry; exact eq.
Qed.

Theorem card_subs_le {U} : ∀ A B : U → Prop, A ⊆ B →
    |set_type A| ≤ |set_type B|.
Proof.
    intros A B sub.
    unfold le; equiv_simpl.
    exists (λ x, [[x|] | sub _ [|x]]).
    split.
    intros a b eq.
    rewrite set_type_eq2 in eq.
    apply set_type_eq; exact eq.
Qed.

Theorem card_all : ∀ U, |U| = |set_type (U := U) all|.
Proof.
    intros U.
    equiv_simpl.
    exists (λ x, [x|true]).
    apply (inverse_ex_bijective _ (λ x, [x|])).
    split.
    -   intros [x x_in].
        rewrite set_type_eq2.
        reflexivity.
    -   reflexivity.
Qed.

Theorem card_sub_le : ∀ (A : Type) (S : A → Prop), |set_type S| ≤ |A|.
Proof.
    intros A S.
    rewrite (card_all A).
    apply card_subs_le.
    apply all_sub.
Qed.

Theorem card_minus_le {U} : ∀ (A B : U → Prop),
    |set_type (A - B)| ≤ |set_type A|.
Proof.
    intros A B.
    apply card_subs_le.
    rewrite set_minus_formula.
    apply inter_lsub.
Qed.

Theorem image_le {U V} : ∀ (f : U → V), |set_type (image f)| ≤ |U|.
Proof.
    intros f.
    unfold le; equiv_simpl.
    apply (partition_principle (λ x, [f x|ex_intro _ x Logic.eq_refl])).
    split.
    intros [y [x x_eq]].
    exists x.
    rewrite set_type_eq2.
    symmetry; exact x_eq.
Qed.

Theorem image_under_le {U V} : ∀ (A : U → Prop) (f : U → V),
    |set_type (image_under f A)| ≤ |set_type A|.
Proof.
    intros A f.
    unfold le; equiv_simpl.
    apply (partition_principle (λ x,
        [f [x|] | ex_intro _ _ (make_and [|x] Logic.eq_refl)])).
    split.
    intros [y [x [Ax y_eq]]].
    exists [x|Ax]; cbn.
    rewrite set_type_eq2.
    symmetry; exact y_eq.
Qed.

Theorem card_union_left {U} : ∀ S T : U → Prop,
    |set_type S| ≤ |set_type (S ∪ T)%set|.
Proof.
    intros S T.
    apply card_subs_le.
    apply union_lsub.
Qed.

Theorem card_union_right {U} : ∀ S T : U → Prop,
    |set_type T| ≤ |set_type (S ∪ T)%set|.
Proof.
    intros S T.
    apply card_subs_le.
    apply union_rsub.
Qed.

Close Scope set_scope.

Theorem card_plus_union {U} : ∀ S T : U → Prop,
    |set_type (S ∪ T)%set| ≤ |set_type S| + |set_type T|.
Proof.
    intros S T.
    unfold le, plus; equiv_simpl.
    exists (λ x, match or_to_strong _ _ [|x] with
        | strong_or_left  H => inl [[x|] | H]
        | strong_or_right H => inr [[x|] | H]
        end).
    split.
    intros a b eq.
    destruct (or_to_strong _ _ _) as [Sa|Ta].
    all: destruct (or_to_strong _ _ _) as [Sb|Tb].
    -   apply inl_eq in eq.
        rewrite set_type_eq2 in eq.
        apply set_type_eq; exact eq.
    -   contradiction (inlr_neq eq).
    -   contradiction (inrl_neq eq).
    -   apply inr_eq in eq.
        rewrite set_type_eq2 in eq.
        apply set_type_eq; exact eq.
Qed.

Theorem zero_is_empty {U} : ∀ S : U → Prop, 0 = |set_type S| → S = ∅.
Proof.
    intros S S_z.
    apply empty_eq.
    intros x Sx.
    contradiction (card_0_false _ S_z [x|Sx]).
Qed.

Theorem empty_set_size {U} : 0 = |set_type (U := U) ∅|.
Proof.
    apply card_false_0.
    intros [x x_in].
    exact x_in.
Qed.

Theorem singleton_set_size {U} : ∀ a : U, |set_type ❴a❵| = 1.
Proof.
    intros a.
    unfold one; equiv_simpl.
    exists (λ _, Single).
    apply (inverse_ex_bijective _ (λ _, [a|Logic.eq_refl])).
    split.
    -   apply singleton_type_eq.
    -   intros [x x_eq].
        subst.
        reflexivity.
Qed.

Section Order.

Context {U} `{TotalOrder U}.

Theorem all_greater_inf_set : ∀ S : U → Prop,
    (∃ x, S x) → (∀ a : set_type S, ∃ b : set_type S, [a|] < [b|]) →
    infinite (|set_type S|).
Proof.
    intros S [x Sx] all_greater.
    apply all_greater_inf.
    1: exact [x|Sx].
    intros a.
    specialize (all_greater a).
    destruct all_greater as [b b_gt].
    exists b.
    rewrite set_type_lt in b_gt.
    exact b_gt.
Qed.

End Order.

Theorem empty_finite {U} : finite (|set_type (@empty U)|).
Proof.
    rewrite <- empty_set_size.
    rewrite <- (homo_zero (f := from_nat)).
    apply nat_is_finite.
Qed.

Theorem singleton_finite {U} : ∀ a : U, finite (|set_type ❴a❵|).
Proof.
    intros a.
    rewrite singleton_set_size.
    rewrite <- (homo_one (f := from_nat)).
    apply nat_is_finite.
Qed.

Theorem card_plus_one {U} : ∀ (S : U → Prop) (a : set_type S),
    |set_type S| = |set_type (S - ❴[a|]❵)%set| + 1.
Proof.
    intros S a.
    unfold one, plus; equiv_simpl.
    assert (∀ x : set_type S, x ≠ a → (S - ❴[a|]❵)%set [x|]) as x_in.
    {
        intros x x_neq.
        split.
        -   exact [|x].
        -   rewrite singleton_eq.
            symmetry.
            rewrite set_type_eq.
            exact x_neq.
    }
    exists (λ x : set_type S, IfH (x = a)
        then λ _, inr Single
        else λ H, inl [[x|] | x_in x H]).
    apply (inverse_ex_bijective _ (λ x, match x with
        | inl y => [[y|] | land [|y]]
        | inr _ => a
        end)).
    split.
    -   intros [[x [Sx x_neq]]|s]; cbn.
        +   destruct (sem _) as [eq|neq].
            *   exfalso.
                pose proof x_neq as x_neq2.
                rewrite <- eq in x_neq2.
                rewrite singleton_eq in x_neq2.
                contradiction.
            *   apply f_equal; rewrite set_type_eq2.
                reflexivity.
        +   classic_case (a = a); [>|contradiction].
            apply f_equal; apply singleton_type_eq.
    -   intros x.
        classic_case (x = a) as [eq|neq].
        +   symmetry; exact eq.
        +   apply set_type_eq; reflexivity.
Qed.

Theorem card_plus_one_nat {U} : ∀ (S : U → Prop) n (a : set_type S),
    |set_type S| = from_nat (nat_suc n) →
    |set_type (S - ❴[a|]❵)%set| = from_nat n.
Proof.
    intros S n a eq.
    rewrite (card_plus_one S a) in eq.
    rewrite from_nat_suc in eq.
    rewrite plus_comm in eq.
    rewrite <- (homo_one (f := from_nat)) in eq.
    apply card_nat_plus_lcancel in eq.
    exact eq.
Qed.

Theorem inter_le {U} : ∀ (SS : (U → Prop) → Prop) S μ,
    SS S → |set_type S| ≤ μ → |set_type (⋂ SS)| ≤ μ.
Proof.
    intros SS S μ SS_S S_le.
    apply (trans2 S_le).
    apply card_subs_le.
    apply (inter_sub _ _ SS_S).
Qed.

Theorem inter_lt {U} : ∀ (SS : (U → Prop) → Prop) S μ,
    SS S → |set_type S| < μ → |set_type (⋂ SS)| < μ.
Proof.
    intros SS S μ SS_S S_le.
    apply (le_lt_trans2 S_le).
    apply card_subs_le.
    apply (inter_sub _ _ SS_S).
Qed.

Theorem finite_inter_finite {U} : ∀ SS : (U → Prop) → Prop,
    (∃ S, SS S ∧ finite (|set_type S|)) →
    finite (|set_type (⋂ SS)|).
Proof.
    intros SS [S [SS_S S_fin]].
    apply (inter_lt SS S _ SS_S S_fin).
Qed.

Theorem union_size_mult {U} : ∀ (SS : (U → Prop) → Prop) κ μ,
    |set_type SS| ≤ κ → (∀ S, SS S → |set_type S| ≤ μ) →
    |set_type (⋃ SS)| ≤ κ * μ.
Proof.
    intros SS A B leq all_leq'.
    equiv_get_value A B.
    assert (∀ S, SS S → ∃ f : set_type S → B, Injective f) as all_leq.
    {
        intros S SS_S.
        specialize (all_leq' S SS_S).
        unfold le in all_leq'; equiv_simpl in all_leq'.
        exact all_leq'.
    }
    clear all_leq'.
    unfold mult, le; equiv_simpl.
    unfold le in leq; equiv_simpl in leq.
    destruct leq as [f f_inj].
    pose (get_set (x : set_type (⋃ SS)) :=[ex_val [|x] | land (ex_proof [|x])]).
    assert (∀ x, [get_set x|] [x|]) as get_in.
    {
        intros x.
        unfold get_set; cbn.
        rewrite_ex_val S [SS_S Sx].
        exact Sx.
    }
    pose (get_g (S : set_type SS) := ex_val (all_leq [S|] [|S])).
    assert (get_g_inj : ∀ S, Injective (get_g S)).
    {
        intros S.
        exact (ex_proof (all_leq [S|] [|S])).
    }
    assert (∀ X Y a b, X = Y → get_g X a = get_g Y b → [a|] = [b|]) as get_g_eq.
    {
        intros X Y a b eq1 eq2.
        subst Y.
        pose proof (get_g_inj X).
        apply inj in eq2.
        subst; reflexivity.
    }
    exists (λ x, (
        f (get_set x),
        get_g (get_set x) [[x|] | get_in x]
    )).
    split.
    intros a b eq.
    apply prod_split in eq as [eq1 eq2].
    apply inj in eq1.
    apply (get_g_eq _ _ _ _ eq1) in eq2.
    cbn in eq2.
    apply set_type_eq; exact eq2.
Qed.

Theorem countable_union_countable {U} : ∀ (SS : (U → Prop) → Prop),
    |set_type SS| ≤ |nat| → (∀ S, SS S → |set_type S| ≤ |nat|) →
    |set_type (⋃ SS)| ≤ |nat|.
Proof.
    intros SS SS_count S_count.
    rewrite <- (card_mult_idemp (|nat|)) by apply refl.
    apply (union_size_mult _ _ _ SS_count S_count).
Qed.

Theorem union_size_mult_strict_false : ¬(∀ U, ∀ (SS : (U → Prop) → Prop) κ μ,
    |set_type SS| < κ → (∀ S, SS S → |set_type S| < μ) →
    |set_type (⋃ SS)| < κ * μ).
Proof.
    intros contr.
    remember (aleph ω) as U.
    equiv_get_value U.
    rename H0 into U_eq.
    assert (∀ n, aleph (from_nat n) ≤ |U|) as n_lt.
    {
        intros n.
        rewrite U_eq.
        apply homo_le.
        apply nat_lt_ω.
    }
    pose (build n := ex_val (card_le_sub _ _ (n_lt n))).
    pose (SS := image build).
    specialize (contr U SS (aleph ω) (aleph ω)).
    prove_parts contr.
    {
        assert (aleph 0 < aleph ω) as ltq.
        {
            apply homo_lt.
            apply all_pos2.
            exact ω_nz.
        }
        apply (le_lt_trans2 ltq); clear ltq.
        rewrite aleph_0.
        apply image_le.
    }
    {
        intros S [n S_eq].
        subst S.
        unfold build.
        rewrite_ex_val S S_eq.
        rewrite S_eq.
        apply homo_lt.
        apply nat_lt_ω.
    }
    rewrite card_mult_idemp in contr by apply aleph_infinite.
    rewrite <- nle_lt in contr.
    apply contr; clear contr.
    apply (aleph_least _ _ ω_nz).
    intros β β_lt.
    apply ord_lt_ω in β_lt as [n n_eq]; subst β.
    assert (|set_type (build (nat_suc n))| ≤ |set_type (⋃ SS)|) as leq.
    {
        apply card_subs_le.
        unfold SS.
        apply union_sub.
        exists (nat_suc n).
        reflexivity.
    }
    apply (lt_le_trans2 leq).
    unfold build.
    rewrite_ex_val S S_eq.
    rewrite S_eq.
    apply homo_lt.
    apply homo_lt.
    apply nat_lt_suc.
Qed.

Theorem finite_union_finite {U} : ∀ SS : (U → Prop) → Prop,
    finite (|set_type SS|) → (∀ S, SS S → finite (|set_type S|)) →
    finite (|set_type (⋃ SS)|).
Proof.
    intros SS SS_fin SS_le.
    classic_case (0 = |set_type SS|) as [SS_z|SS_nz].
    {
        apply zero_is_empty in SS_z.
        rewrite SS_z.
        rewrite union_empty.
        rewrite <- empty_set_size.
        rewrite <- (homo_zero (f := from_nat)).
        apply nat_is_finite.
    }
    apply card_nz_ex in SS_nz.
    assert (∀ S, SS S → ∃ n, from_nat n = |set_type S|) as n_ex.
    {
        intros S SS_S.
        apply fin_nat_ex.
        exact (SS_le S SS_S).
    }
    pose (get_n (S : set_type SS) := ex_val (n_ex [S|] [|S])).
    assert (finite (|set_type (image get_n)|)) as image_fin.
    {
        apply (le_lt_trans (image_le _)).
        exact SS_fin.
    }
    assert (set_type (image get_n)) as sn.
    {
        exists (get_n SS_nz).
        exists SS_nz.
        reflexivity.
    }
    pose proof (finite_max image_fin sn) as [[n n_in] n_ge].
    clear sn SS_nz.
    assert (∀ S, SS S → |set_type S| ≤ from_nat n) as all_leq.
    {
        intros S SS_S.
        specialize (n_ge [_|ex_intro _ [S|SS_S] Logic.eq_refl]).
        unfold get_n in n_ge; cbn in n_ge.
        unfold le in n_ge; cbn in n_ge.
        rewrite_ex_val m m_eq.
        rewrite <- m_eq.
        apply homo_le.
        exact n_ge.
    }
    apply fin_nat_ex in SS_fin as [m m_eq].
    assert (|set_type SS| ≤ from_nat m) as SS_leq by (rewrite m_eq; apply refl).
    apply (le_lt_trans (union_size_mult _ _ _ SS_leq all_leq)).
    rewrite <- homo_mult.
    apply nat_is_finite.
Qed.

Close Scope card_scope.
