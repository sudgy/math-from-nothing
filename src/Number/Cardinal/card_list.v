Require Import init.

Require Export card_set.
Require Export list.
Require Export order_minmax.

Open Scope card_scope.

Theorem empty_list_card {U} : ¬inhabited U → |list U| = 1.
Proof.
    intros U_nex.
    unfold one; equiv_simpl.
    exists (λ _, Single).
    split; split.
    -   intros al bl eq.
        destruct al as [|a al].
        2: exfalso; apply U_nex; split; exact a.
        destruct bl as [|b bl].
        2: exfalso; apply U_nex; split; exact b.
        reflexivity.
    -   intros y.
        exists [].
        apply singleton_type_eq.
Qed.

Lemma list_infinite {U} (x : U) : |nat| ≤ |list U|.
Proof.
    unfold le; equiv_simpl.
    exists (list_constant x).
    split.
    intros m n eq.
    pose proof (list_count_constant x m) as eq1.
    pose proof (list_count_constant x n) as eq2.
    rewrite <- eq1, <- eq2.
    rewrite eq.
    reflexivity.
Qed.

Lemma list_card_le U : |U| ≤ |list U|.
Proof.
    unfold le; equiv_simpl.
    exists (λ x, [x]).
    split.
    intros a b eq.
    apply list_inversion in eq.
    apply eq.
Qed.

Lemma list_size_card {U} : ∀ n,
    |set_type (λ l : list U, list_size l = n)| = |U| ^ from_nat n.
Proof.
    intros n.
    nat_induction n.
    -   rewrite homo_zero.
        rewrite card_pow_zero.
        unfold one; equiv_simpl.
        exists (λ _, Single).
        split; split.
        +   intros [l1 l1_size] [l2 l2_size] eq.
            apply set_type_eq; cbn.
            symmetry in l1_size, l2_size.
            destruct l1; [>|contradiction (nat_zero_suc l1_size)].
            destruct l2; [>|contradiction (nat_zero_suc l2_size)].
            reflexivity.
        +   intros y.
            exists [[] | list_size_end U].
            apply singleton_type_eq.
    -   rewrite from_nat_suc.
        rewrite card_pow_plus.
        rewrite card_pow_one.
        rewrite <- IHn.
        symmetry.
        unfold mult; equiv_simpl.
        assert (∀ xl : U * set_type (λ l : list U, list_size l = n),
            list_size (fst xl ꞉ [snd xl|]) = nat_suc n) as xl_in.
        {
            intros xl.
            rewrite list_size_add.
            apply f_equal.
            exact [|snd xl].
        }
        exists (λ xl, [fst xl ꞉ [snd xl|] | xl_in xl]).
        split; split.
        +   intros [a [al al_n]] [b [bl bl_n]]; cbn.
            intros eq.
            apply set_type_eq in eq; cbn in eq.
            apply list_inversion in eq as [eq1 eq2]; subst b bl.
            rewrite (proof_irrelevance al_n bl_n).
            reflexivity.
        +   intros [l l_size].
            destruct l as [|x l]; [>contradiction (nat_zero_suc l_size)|].
            pose proof l_size as l_size2.
            rewrite list_size_add in l_size2.
            rewrite nat_suc_eq in l_size2.
            exists (x, [l|l_size2]).
            apply set_type_eq; cbn.
            reflexivity.
Qed.

Theorem finite_list_card {U} (x : U) : |U| < |nat| → |list U| = |nat|.
Proof.
    intros ltq.
    apply antisym.
    -   pose (SS := image (λ n : nat, λ l : list U, list_size l = n)).
        rewrite card_all.
        replace all with (⋃ SS).
        2: {
            apply all_eq.
            intros l.
            exists (λ l', list_size l' = list_size l).
            split; [>|reflexivity].
            exists (list_size l).
            reflexivity.
        }
        apply countable_union_countable.
        +   unfold le; equiv_simpl.
            exists (λ (x : set_type SS), ex_val [|x]).
            split.
            intros [S S_in] [T T_in]; cbn.
            intros eq.
            apply set_type_eq; cbn.
            rewrite_ex_val m m_eq.
            rewrite_ex_val n n_eq.
            subst.
            reflexivity.
        +   intros S [n S_eq]; subst S.
            rewrite list_size_card.
            apply card_lt_nat in ltq as [m m_eq].
            rewrite m_eq.
            replace (from_nat m ^ from_nat n) with (from_nat (m^n)).
            2: {
                nat_induction n.
                -   rewrite nat_pow_zero.
                    rewrite homo_zero.
                    rewrite card_pow_zero.
                    apply homo_one.
                -   rewrite nat_pow_suc.
                    rewrite homo_mult.
                    rewrite from_nat_suc.
                    rewrite plus_comm.
                    rewrite card_pow_plus, card_pow_one.
                    rewrite IHn.
                    reflexivity.
            }
            apply nat_lt_card.
    -   apply list_infinite.
        exact x.
Qed.

Theorem infinite_list_card {U} : |nat| ≤ |U| → |list U| = |U|.
Proof.
    intros leq.
    apply antisym.
    -   pose (SS := image (λ n : nat, λ l : list U, list_size l = n)).
        rewrite card_all.
        replace all with (⋃ SS).
        2: {
            apply all_eq.
            intros l.
            exists (λ l', list_size l' = list_size l).
            split; [>|reflexivity].
            exists (list_size l).
            reflexivity.
        }
        pose proof (card_mult_max (|nat|) (|U|) (refl _) leq) as eq.
        rewrite (max_req _ _ leq) in eq.
        rewrite <- eq.
        apply union_size_mult.
        +   unfold le; equiv_simpl.
            exists (λ (x : set_type SS), ex_val [|x]).
            split.
            intros [S S_in] [T T_in]; cbn.
            intros eq2.
            apply set_type_eq; cbn.
            rewrite_ex_val m m_eq.
            rewrite_ex_val n n_eq.
            subst.
            reflexivity.
        +   intros S [n]; subst S.
            rewrite list_size_card.
            nat_induction n.
            *   rewrite homo_zero.
                rewrite card_pow_zero.
                apply (trans2 leq).
                rewrite <- (homo_one (f := from_nat)).
                apply nat_lt_card.
            *   rewrite from_nat_suc.
                rewrite card_pow_plus, card_pow_one.
                apply (le_lmult (|U|)) in IHn.
                apply (trans IHn).
                rewrite card_mult_idemp by exact leq.
                apply refl.
    -   apply list_card_le.
Qed.
