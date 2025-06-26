Require Import init.

Require Export card2_infinite.
Require Import ord.
Require Import order_minmax.
Require Import well_order.

Open Scope card_scope.

Lemma card_inf_plus_one : ∀ μ, infinite μ → μ + 1 = μ.
Proof.
    intros U U_inf.
    unfold infinite in U_inf.
    equiv_get_value U.
    unfold le in U_inf; equiv_simpl in U_inf.
    destruct U_inf as [f f_inj].
    unfold one, plus; equiv_simpl.
    pose (g (x : U + singleton_type) := match x with
        | inl a => IfH (∃ n, f n = a)
                   then λ H, f (nat_suc (ex_val H))
                   else λ _, a
        | inr _ => f 0
        end).
    pose (h (a : U) :=
        If a = f 0 then inr Single
        else IfH (∃ n, f (nat_suc n) = a)
            then λ H, inl (f (ex_val H))
            else λ _, inl a).
    exists g.
    apply (inverse_ex_bijective _ h).
    unfold g, h.
    split.
    -   intros x.
        classic_case (x = f 0) as [x_eq|x_neq].
        +   symmetry; exact x_eq.
        +   classic_case (∃ n, f (nat_suc n) = x) as [n_ex|n_nex].
            *   rewrite_ex_val n n_eq.
                assert (∃ m, f m = f n) as H by (exists n; reflexivity).
                rewrite (ifH_true H).
                rewrite_ex_val m m_eq.
                apply inj in m_eq.
                subst.
                reflexivity.
            *   assert (¬(∃ n, f n = x)) as H.
                {
                    intros [n eq].
                    subst x.
                    nat_destruct n; [>contradiction|].
                    apply n_nex.
                    exists n.
                    reflexivity.
                }
                rewrite (ifH_false H).
                reflexivity.
    -   intros [x|s].
        +   classic_case (∃ n, f n = x) as [n_ex|n_nex].
            *   rewrite_ex_val n n_eq.
                assert (f (nat_suc n) ≠ f 0) as neq.
                {
                    intros contr.
                    apply inj in contr.
                    symmetry in contr.
                    contradiction (nat_zero_suc contr).
                }
                rewrite (if_false neq).
                destruct (sem _) as [m_ex|m_nex].
                2: (exfalso; apply m_nex; exists n; reflexivity).
                rewrite_ex_val m m_eq.
                apply f_equal.
                apply inj in m_eq.
                rewrite nat_suc_eq in m_eq.
                subst m.
                exact n_eq.
            *   assert (x ≠ f 0) as H.
                {
                    intros contr.
                    apply n_nex.
                    exists 0.
                    symmetry; exact contr.
                }
                rewrite (if_false H).
                destruct (sem _) as [[m m_eq]|m_nex].
                1: (exfalso; apply n_nex; exists (nat_suc m); exact m_eq).
                reflexivity.
        +   rewrite (if_true Logic.eq_refl).
            apply f_equal.
            apply singleton_type_eq.
Qed.

Lemma card_inf_minus_one_inf : ∀ μ, infinite (μ + 1) → infinite μ.
Proof.
    intros μ μ_inf.
    unfold infinite in *.
    order_contradiction ltq.
    apply card_lt_nat in ltq as [n μ_eq]; subst μ.
    rewrite <- nlt_le in μ_inf.
    apply μ_inf.
    rewrite <- (homo_one (f := from_nat)).
    rewrite <- homo_plus.
    apply nat_lt_card.
Qed.

Lemma card_inf_remove_one : ∀ U (a : U), infinite (|U|) →
    |U| = |set_type (λ x, x ≠ a)|.
Proof.
    intros U a U_inf.
    assert (|set_type (λ x, x ≠ a)| + 1 = |U|) as eq.
    {
        unfold one, plus; equiv_simpl.
        exists (λ x, match x with
            | inl y => [y|]
            | inr _ => a
            end).
        apply (inverse_ex_bijective _ (λ x,
            IfH (x = a) then λ _, (inr Single) else λ H, (inl [x|H]))).
        split.
        -   intros x.
            classic_case (x = a) as [eq|neq].
            +   symmetry; exact eq.
            +   reflexivity.
        -   intros [[x x_neq]|s]; cbn.
            +   classic_case (x = a); [>contradiction|].
                rewrite (proof_irrelevance _ x_neq).
                reflexivity.
            +   classic_case (a = a); [>|contradiction].
                apply f_equal; apply singleton_type_eq.
    }
    rewrite <- eq.
    apply card_inf_plus_one.
    apply card_inf_minus_one_inf.
    rewrite eq.
    exact U_inf.
Qed.

Module CardMultIdemp.
Section CardMultIdemp.

Context (A : ord_type).
Context (A_inf : |nat| ≤ |A|).

Local Instance godel_pairing : Order (A * A) := {
    le a b :=
    (max (fst a) (snd a) < max (fst b) (snd b)) ∨
    (max (fst a) (snd a) = max (fst b) (snd b) ∧ fst a < fst b) ∨
    (max (fst a) (snd a) = max (fst b) (snd b) ∧ fst a = fst b ∧ snd a ≤ snd b)
}.

Local Instance godel_antisym : Antisymmetric le.
Proof.
    split.
    intros [a1 a2] [b1 b2] leq1 leq2.
    destruct leq1 as [leq1|[leq1|leq1]].
    all: destruct leq2 as [leq2|[leq2|leq2]].
    all: cbn in *.
    -   contradiction (irrefl _ (trans leq1 leq2)).
    -   destruct leq2 as [eq2 leq2].
        rewrite eq2 in leq1.
        contradiction (irrefl _ leq1).
    -   destruct leq2 as [eq2 leq2].
        rewrite eq2 in leq1.
        contradiction (irrefl _ leq1).
    -   destruct leq1 as [eq1 leq1].
        rewrite eq1 in leq2.
        contradiction (irrefl _ leq2).
    -   destruct leq1 as [eq1 leq1].
        destruct leq2 as [eq2 leq2].
        contradiction (irrefl _ (trans leq1 leq2)).
    -   destruct leq1 as [eq1 leq1].
        destruct leq2 as [eq2 [eq3]].
        rewrite eq3 in leq1.
        contradiction (irrefl _ leq1).
    -   destruct leq1 as [eq1 leq1].
        rewrite eq1 in leq2.
        contradiction (irrefl _ leq2).
    -   destruct leq1 as [eq1 [eq3]].
        destruct leq2 as [eq2 leq2].
        rewrite eq3 in leq2.
        contradiction (irrefl _ leq2).
    -   destruct leq1 as [eq1 [eq2 leq1]].
        destruct leq2 as [eq3 [eq4 leq2]].
        pose proof (antisym leq1 leq2).
        subst.
        reflexivity.
Qed.

Local Instance godel_wo : WellOrdered le.
Proof.
    split.
    intros S S_ex.
    pose (S' a := ∃ a1 a2, S (a1, a2) ∧ a = max a1 a2).
    pose proof (well_ordered S') as d_ex.
    prove_parts d_ex.
    {
        destruct S_ex as [[a1 a2] Sa].
        exists (max a1 a2).
        exists a1, a2.
        split; trivial.
    }
    destruct d_ex as [d [S'd d_least]].
    pose (S'' a1 := ∃ a2, S (a1, a2) ∧ d = max a1 a2).
    pose proof (well_ordered S'') as x_ex.
    prove_parts x_ex.
    {
        destruct S'd as [x [y [Sxy d_eq]]].
        exists x, y.
        split; assumption.
    }
    destruct x_ex as [x [S''x x_least]].
    pose (S''' a2 := S (x, a2) ∧ d = max x a2).
    pose proof (well_ordered S''') as y_ex.
    prove_parts y_ex.
    {
        destruct S''x as [y [Sxy d_eq]].
        exists y.
        split; assumption.
    }
    destruct y_ex as [y [S'''y y_least]].
    exists (x, y).
    split; [>apply S'''y|].
    intros [a1 a2] Sa.
    unfold le; cbn.
    destruct S'''y as [Sxy d_eq]; subst d.
    classic_case (max x y = max a1 a2) as [eq1|neq1].
    1: classic_case (x = a1) as [eq2|neq2].
    -   right.
        right.
        split; [>exact eq1|].
        split; [>exact eq2|].
        apply y_least.
        unfold S'''.
        subst x.
        split; [>exact Sa|].
        exact eq1.
    -   right.
        left.
        split; [>exact eq1|].
        split; [>|exact neq2].
        apply x_least.
        unfold S''.
        exists a2.
        split; [>exact Sa|].
        exact eq1.
    -   left.
        split; [>|exact neq1].
        apply d_least.
        exists a1, a2.
        split; trivial.
Qed.

Definition godel_pair := make_ord_type (A*A)%type _ _ _ : ord_type.

Section Induction.

Context (IHα : ∀ B, to_ord B < to_ord A → |nat| ≤ |B| → |B| = |(B*B)%type|).

Section NotCard.

Context B (B_lt : to_ord B < to_ord A) (B_eq : |B| = |A|).

Lemma not_card_idemp : |A| = |(A*A)%type|.
Proof.
    rewrite <- B_eq in A_inf.
    specialize (IHα B B_lt A_inf).
    rewrite card_mult_type.
    rewrite card_mult_type in IHα.
    rewrite B_eq in IHα.
    exact IHα.
Qed.

End NotCard.

Section Card.

Context (β_nex : ¬(∃ β : ord, β < to_ord A ∧
    ord_to_card β = ord_to_card (to_ord A))).

Lemma gt_ex : ∀ a : A, ∃ b, a < b.
Proof.
    intros a.
    classic_contradiction contr.
    apply β_nex.
    exists (ord_type_init_ord_base A a).
    split; [>apply ord_type_init_ord_in|].
    rewrite ord_to_card_init.
    unfold ord_to_card.
    rewrite unary_op_eq.
    symmetry.
    assert (initial_segment a = (λ x, x ≠ a)) as eq.
    {
        unfold initial_segment.
        apply antisym.
        -   intros x x_lt eq.
            subst.
            contradiction (irrefl _ x_lt).
        -   intros x x_neq.
            split; [>|exact x_neq].
            order_contradiction ltq.
            apply contr.
            exists x.
            exact ltq.
    }
    rewrite eq.
    apply card_inf_remove_one.
    exact A_inf.
Qed.

Lemma l_leq : ∀ l1 l2 l : A, max l1 l2 < l →
    |set_type (initial_segment (l1, l2))| ≤
    |set_type (initial_segment l)| * |set_type(initial_segment l)|.
Proof.
    intros l1 l2 l l_lt.
    rewrite <- card_mult_type.
    unfold le; equiv_simpl.
    assert (∀ d : set_type (initial_segment (l1, l2)),
        fst [d|] < l ∧ snd [d|] < l) as lt.
    {
        intros [[d1 d2] d_lt]; cbn.
        assert (max d1 d2 = max l1 l2 → d1 < l ∧ d2 < l) as lem.
        {
            intros eq.
            split.
            -   apply (le_lt_trans (lmax d1 d2)).
                rewrite eq.
                exact l_lt.
            -   apply (le_lt_trans (rmax d1 d2)).
                rewrite eq.
                exact l_lt.
        }
        destruct d_lt as [d_le d_neq].
        destruct d_le as [d_le|[d_le|d_le]]; cbn in d_le.
        -   split.
            +   apply (le_lt_trans (lmax d1 d2)).
                exact (trans d_le l_lt).
            +   apply (le_lt_trans (rmax d1 d2)).
                exact (trans d_le l_lt).
        -   destruct d_le as [d_eq d_lt].
            exact (lem d_eq).
        -   destruct d_le as [d_eq1 [d_eq2 d_le]].
            exact (lem d_eq1).
    }
    exists (λ d, ([fst [d|] | land (lt d)], [snd [d|] | rand (lt d)])).
    split.
    intros [[c1 c2] c_lt] [[d1 d2] d_lt]; cbn.
    intros eq.
    apply prod_split in eq as [eq1 eq2].
    rewrite set_type_eq2.
    rewrite set_type_eq2 in eq1.
    rewrite set_type_eq2 in eq2.
    subst; reflexivity.
Qed.

Lemma l_lt : ∀ l1 l2, ord_type_init_ord_base godel_pair (l1, l2) < to_ord A.
Proof.
    intros l1 l2.
    pose proof (gt_ex (max l1 l2)) as [l l_lt].
    apply ord_to_card_lt.
    rewrite ord_to_card_init.
    apply (le_lt_trans (l_leq l1 l2 l l_lt)); clear l1 l2 l_lt.
    classic_case (|nat| ≤ |set_type (initial_segment l)|) as [l_inf|l_fin].
    -   specialize (IHα (sub_ord_type (initial_segment l))).
        specialize (IHα (ord_type_init_ord_in _)).
        specialize (IHα l_inf).
        rewrite card_mult_type in IHα.
        rewrite <- IHα; clear IHα.
        rewrite <- ord_to_card_init.
        split.
        +   apply ord_to_card_le.
            apply ord_type_init_ord_in.
        +   rewrite not_ex in β_nex.
            specialize (β_nex (ord_type_init_ord_base A l)).
            rewrite not_and_impl in β_nex.
            apply β_nex.
            apply ord_type_init_ord_in.
    -   rewrite nle_lt in l_fin.
        apply fin_nat_ex in l_fin as [n n_eq].
        rewrite <- n_eq.
        rewrite <- homo_mult.
        unfold ord_to_card.
        rewrite unary_op_eq.
        apply (lt_le_trans2 A_inf).
        apply nat_lt_card.
Qed.

Lemma A_leq : to_ord godel_pair ≤ to_ord A.
Proof.
    order_contradiction ltq.
    pose proof (ord_type_init_ord_bij godel_pair).
    pose proof (sur (ord_type_init_ord godel_pair) [to_ord A|ltq])
        as [[x1 x2] x_eq].
    unfold ord_type_init_ord in x_eq.
    rewrite set_type_eq2 in x_eq.
    pose proof (l_lt x1 x2) as l_lt.
    rewrite x_eq in l_lt.
    contradiction (irrefl _ l_lt).
Qed.

Lemma card_idemp : |A| = |(A * A)%type|.
Proof.
    apply antisym.
    -   unfold le; equiv_simpl.
        exists (λ x, (x, x)).
        split.
        intros a b eq.
        apply prod_split in eq as [eq1 eq2].
        exact eq1.
    -   pose proof A_leq as A_leq.
        apply ord_to_card_le in A_leq.
        unfold ord_to_card in A_leq; equiv_simpl in A_leq.
        exact A_leq.
Qed.

End Card.

End Induction.

End CardMultIdemp.
End CardMultIdemp.

Import CardMultIdemp.

Lemma ord_mult_idemp : ∀ A : ord_type, |nat| ≤ |A| → |A| = |(A * A)%type|.
Proof.
    intros A.
    remember (to_ord A) as α.
    revert A Heqα.
    induction α as [α IHα] using transfinite_induction.
    intros A Heqα A_inf.
    classic_case (∃ β, β < α ∧ ord_to_card β = ord_to_card α) as [β_ex|β_nex].
    -   subst α.
        destruct β_ex as [B [B_lt B_eq]].
        equiv_get_value B.
        pose proof (not_card_idemp A A_inf) as H.
        prove_parts H.
        {
            intros C C_lt C_inf.
            apply (IHα (to_ord C) C_lt _ Logic.eq_refl C_inf).
        }
        unfold ord_to_card in B_eq.
        do 2 rewrite unary_op_eq in B_eq.
        apply (H B B_lt B_eq).
    -   subst α.
        apply (card_idemp A A_inf).
        2: exact β_nex.
        intros B B_lt B_inf.
        exact (IHα (to_ord B) B_lt B Logic.eq_refl B_inf).
Qed.

Theorem card_mult_idemp : ∀ μ, infinite μ → μ * μ = μ.
Proof.
    intros U U_inf.
    equiv_get_value U.
    pose (A := make_ord_type U _ wo_antisym wo_wo).
    rewrite <- card_mult_type.
    rewrite <- (ord_mult_idemp A U_inf).
    reflexivity.
Qed.

Theorem card_plus_idemp : ∀ κ, infinite κ → κ + κ = κ.
Proof.
    intros κ κ_inf.
    rewrite plus_two.
    rewrite <- (homo_one (f := from_nat)).
    rewrite <- homo_plus.
    apply antisym.
    -   rewrite <- (card_mult_idemp κ κ_inf) at 2.
        apply le_rmult.
        apply (trans2 κ_inf).
        apply nat_lt_card.
    -   rewrite <- (mult_lid κ) at 1.
        apply le_rmult.
        rewrite <- (homo_one (f := from_nat)).
        apply homo_le.
        apply nat_le_suc.
Qed.

Theorem card_plus_lmax : ∀ κ μ, infinite κ → μ ≤ κ → κ + μ = κ.
Proof.
    intros κ μ κ_inf leq.
    apply antisym.
    -   rewrite <- (card_plus_idemp κ) at 2 by exact κ_inf.
        apply le_lplus.
        exact leq.
    -   rewrite <- (plus_rid κ) at 1.
        apply le_lplus.
        apply all_pos.
Qed.

Theorem card_mult_lmax : ∀ κ μ, infinite κ → 0 ≠ μ → μ ≤ κ → κ * μ = κ.
Proof.
    intros κ μ κ_inf μ_nz leq.
    apply antisym.
    -   rewrite <- (card_mult_idemp _ κ_inf) at 2.
        apply le_lmult.
        exact leq.
    -   rewrite <- (mult_rid κ) at 1.
        apply le_lmult.
        apply card_pos_one.
        exact μ_nz.
Qed.

Theorem card_plus_max : ∀ κ μ, infinite κ → infinite μ → κ + μ = max κ μ.
Proof.
    intros κ μ κ_inf μ_inf.
    destruct (connex κ μ) as [leq|leq].
    -   rewrite plus_comm.
        rewrite (max_req _ _ leq).
        apply card_plus_lmax; assumption.
    -   rewrite (max_leq _ _ leq).
        apply card_plus_lmax; assumption.
Qed.

Theorem card_mult_max : ∀ κ μ, infinite κ → infinite μ → κ * μ = max κ μ.
Proof.
    intros κ μ κ_inf μ_inf.
    pose proof (infinite_nz κ_inf).
    pose proof (infinite_nz μ_inf).
    destruct (connex κ μ) as [leq|leq].
    -   rewrite mult_comm.
        rewrite (max_req _ _ leq).
        apply card_mult_lmax; assumption.
    -   rewrite (max_leq _ _ leq).
        apply card_mult_lmax; assumption.
Qed.

Theorem card_inf_plus_mult : ∀ κ μ, infinite κ → infinite μ → κ + μ = κ * μ.
Proof.
    intros κ μ κ_inf μ_inf.
    rewrite card_plus_max by assumption.
    rewrite card_mult_max by assumption.
    reflexivity.
Qed.

Close Scope card_scope.
