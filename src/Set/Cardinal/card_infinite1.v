Require Import init.

Require Export card_base.
Require Import card_order.
Require Import card_plus.
Require Import card_mult.
Require Import card_nat.
Require Import set.
Require Import function.
Require Import nat.
Require Import mult_div.
Require Import nat_domain.

(* begin hide *)
Open Scope card_scope.
(* end hide *)
Definition finite κ := κ < |nat|.
Definition countable κ := κ ≤ |nat|.
Definition denumerable κ := κ = |nat|.
Definition infinite κ := |nat| ≤ κ.
Definition uncountable κ := |nat| < κ.

Theorem finite_is_countable : ∀ κ, finite κ → countable κ.
Proof.
    intros κ H.
    apply H.
Qed.
Theorem denumerable_is_countable : ∀ κ, denumerable κ → countable κ.
Proof.
    intros κ H.
    unfold denumerable, countable in *.
    rewrite H.
    apply refl.
Qed.
Theorem denumerable_is_infinite : ∀ κ, denumerable κ → infinite κ.
Proof.
    intros κ H.
    unfold denumerable, infinite in *.
    rewrite H.
    apply refl.
Qed.
Theorem uncountable_is_infinite : ∀ κ, uncountable κ → infinite κ.
Proof.
    intros κ H.
    apply H.
Qed.

Theorem nat_is_finite : ∀ n, finite (nat_to_card n).
Proof.
    assert (∀ n, nat_to_card n ≤ |nat|) as n_countable.
    {
        intros n.
        unfold nat_to_card, le; equiv_simpl.
        exists (λ x, [x|]).
        intros a b eq.
        apply set_type_eq.
        exact eq.
    }
    intros n.
    split; try apply n_countable.
    nat_induction n.
    -   intro contr.
        unfold nat_to_card in contr; equiv_simpl in contr.
        destruct contr as [f f_bij].
        pose proof (rand f_bij 0) as [x x_eq].
        exact (nat_lt_0_false x).
    -   intro eq.
        apply IHn; clear IHn.
        apply antisym.
        1: apply n_countable.
        symmetry in eq.
        unfold nat_to_card in eq; unfold nat_to_card, le.
        equiv_simpl; equiv_simpl in eq.
        destruct eq as [f f_bij].
        pose proof (rand f_bij [n|nat_lt_suc n]) as [m m_eq].
        pose (g x := If x < m then f x else f (nat_suc x)).
        assert (∀ x, [g x|] < n) as g_lt.
        {
            intros x.
            unfold g.
            case_if.
            -   pose proof [|f x] as fx_lt.
                cbn in fx_lt.
                rewrite nat_lt_suc_le in fx_lt.
                split; try exact fx_lt.
                intro contr.
                assert (f x = [n|nat_lt_suc n]) as eq
                    by (apply set_type_eq; exact contr).
                rewrite <- eq in m_eq.
                apply f_bij in m_eq.
                symmetry in m_eq.
                destruct s; contradiction.
            -   pose proof [|f (nat_suc x)] as fx_lt.
                cbn in fx_lt.
                rewrite nat_lt_suc_le in fx_lt.
                split; try exact fx_lt.
                intro contr.
                assert (f (nat_suc x) = [n|nat_lt_suc n]) as eq
                    by (apply set_type_eq; exact contr).
                rewrite <- eq in m_eq.
                apply f_bij in m_eq.
                rewrite m_eq in n0.
                pose proof (nat_lt_suc x).
                contradiction.
        }
        exists (λ x, [[g x|] | g_lt x]).
        intros a b eq.
        unfold g in eq.
        inversion eq as [eq2].
        apply set_type_eq in eq2.
        clear eq.
        do 2 case_if.
        all: apply f_bij in eq2.
        +   exact eq2.
        +   rewrite eq2 in s.
            rewrite nlt_le in n0.
            pose proof (trans (le_lt_trans n0 (nat_lt_suc b)) s) as [eq neq].
            contradiction.
        +   rewrite <- eq2 in s.
            rewrite nlt_le in n0.
            pose proof (trans (le_lt_trans n0 (nat_lt_suc a)) s) as [eq neq].
            contradiction.
        +   inversion eq2.
            reflexivity.
Qed.

Theorem greater_all_nat_inf : ∀ κ, (∀ a, nat_to_card a < κ) → infinite κ.
Proof.
    intros A A_gt.
    equiv_get_value A.
    assert A as c.
    {
        classic_contradiction contr.
        specialize (A_gt 0) as [A_ge A_neq].
        unfold le, nat_to_card in *; equiv_simpl in A_ge; equiv_simpl in A_neq.
        destruct A_ge as [f f_inj].
        rewrite not_ex in A_neq.
        specialize (A_neq f).
        unfold bijective in A_neq.
        rewrite not_and in A_neq.
        destruct A_neq as [f_inj'|f_sur]; try contradiction.
        unfold surjective in f_sur.
        rewrite not_all in f_sur.
        destruct f_sur as [a f_sur].
        contradiction.
    }
    assert (∀ f : nat_strong_recursion_domain A,
        ∃ a, ∀ n, nat_sr_f A f n ≠ a) as h_ex.
    {
        intros [fp ff]; cbn.
        classic_case (surjective ff).
        -   assert (|A| ≤ nat_to_card (nat_suc fp)) as leq.
            {
                unfold nat_to_card, le; equiv_simpl.
                apply (partition_principle ff s).
            }
            pose proof (lt_le_trans (A_gt (nat_suc fp)) leq) as [C0 C1].
            contradiction.
        -   unfold surjective in n.
            rewrite not_all in n.
            destruct n as [a A_nsur].
            exists a.
            intros n.
            rewrite not_ex in A_nsur.
            apply A_nsur.
    }
    pose proof (strong_recursion A c (λ f, ex_val (h_ex f))) as [f [f0 f_rec]].
    unfold infinite.
    unfold le; equiv_simpl.
    exists f.

    assert (∀ m n, m < n → f m ≠ f n) as wlog.
    {
        intros m n ltq.
        nat_destruct n.
        -   apply nat_neg2 in ltq.
            contradiction.
        -   specialize (f_rec n).
            rewrite_ex_val a a_eq; cbn in *.
            specialize (a_eq [m|ltq]).
            cbn in a_eq.
            rewrite <- f_rec in a_eq.
            exact a_eq.
    }
    intros m n eq.
    classic_contradiction contr.
    destruct (trichotomy m n) as [[ltq|eq2]|ltq]; try contradiction.
    -   specialize (wlog _ _ ltq).
        contradiction.
    -   specialize (wlog _ _ ltq).
        symmetry in eq.
        contradiction.
Qed.

Theorem fin_nat_ex : ∀ κ, finite κ → ∃ n, nat_to_card n = κ.
Proof.
    intros κ κ_fin.
    assert (∃ n, κ ≤ nat_to_card n) as κ_le.
    {
        classic_contradiction contr.
        rewrite not_ex in contr.
        unfold finite in κ_fin.
        rewrite <- nle_lt in κ_fin.
        apply κ_fin; clear κ_fin.
        apply greater_all_nat_inf.
        intros a.
        rewrite <- nle_lt.
        apply contr.
    }
    pose proof (well_ordered _ κ_le) as [m [κ_le_m m_min]]; clear κ_le.
    exists m.
    classic_contradiction contr.
    rewrite neq_sym in contr.
    nat_destruct m.
    -   pose proof (antisym κ_le_m (card_le_zero κ)).
        contradiction.
    -   assert (κ ≤ nat_to_card m) as κ_le_m2.
        {
            equiv_get_value κ.
            rename κ into A.
            unfold le, nat_to_card; equiv_simpl.
            unfold le, nat_to_card in κ_le_m; equiv_simpl in κ_le_m.
            destruct κ_le_m as [f f_inj].
            unfold nat_to_card in contr; equiv_simpl in contr.
            rewrite not_ex in contr.
            specialize (contr f).
            unfold bijective in contr.
            rewrite not_and in contr.
            destruct contr as [contr|contr]; try contradiction.
            unfold surjective in contr.
            rewrite not_all in contr.
            destruct contr as [y no_x].
            rewrite not_ex in no_x.
            classic_case ([y|] = m) as [eq|neq].
            -   assert (∀ x, [f x|] < m) as f_lt.
                {
                    intros x.
                    pose proof [|f x] as fx_lt; cbn in fx_lt.
                    rewrite nat_lt_suc_le in fx_lt.
                    split; try exact fx_lt.
                    intro contr.
                    rewrite <- eq in contr.
                    apply set_type_eq in contr.
                    exact (no_x _ contr).
                }
                exists (λ x, [[f x|]|f_lt x]).
                intros a b eq2.
                inversion eq2 as [eq3].
                apply set_type_eq in eq3.
                apply f_inj in eq3.
                exact eq3.
            -   pose (g x := If [f x|] = m then [y|] else [f x|]).
                assert (∀ x, g x < m) as g_lt.
                {
                    intros x; unfold g.
                    case_if.
                    -   destruct y as [y y_lt]; cbn in *.
                        pose proof y_lt as y_lt2.
                        rewrite nat_lt_suc_le in y_lt2.
                        split; assumption.
                    -   split; try exact n.
                        pose proof [|f x] as fx_lt; cbn in fx_lt.
                        rewrite nat_lt_suc_le in fx_lt.
                        exact fx_lt.
                }
                exists (λ x, [g x|g_lt x]).
                intros a b eq.
                inversion eq as [eq2].
                unfold g in eq2.
                do 2 case_if; apply set_type_eq in eq2.
                +   rewrite <- e0 in e; clear e0.
                    apply set_type_eq in e.
                    apply f_inj in e.
                    exact e.
                +   specialize (no_x b).
                    symmetry in eq2; contradiction.
                +   specialize (no_x a).
                    contradiction.
                +   apply f_inj in eq2.
                    exact eq2.
        }
        specialize (m_min _ κ_le_m2).
        rewrite <- nlt_le in m_min.
        apply m_min.
        apply nat_lt_suc.
Qed.

Theorem inf_not_nat : ∀ κ, infinite κ → ∀ n, nat_to_card n ≠ κ.
Proof.
    intros κ κ_inf n eq.
    subst.
    pose proof (nat_is_finite n) as fin.
    unfold infinite, finite in *.
    pose proof (lt_le_trans fin κ_inf) as [C0 C1]; contradiction.
Qed.

Theorem inf_plus_fin : ∀ κ μ, infinite κ → finite μ → κ + μ = κ.
Proof.
    intros A B A_inf B_fin.
    pose proof (fin_nat_ex B B_fin) as [n n_eq].
    subst; clear B_fin.
    equiv_get_value A.
    unfold nat_to_card, plus; equiv_simpl.
    unfold infinite, le in A_inf; equiv_simpl in A_inf.
    destruct A_inf as [f f_inj].
    exists (λ x, match x with
        | inl a =>
            match (strong_excluded_middle (∃ n, f n = a)) with
                | strong_or_left H => f (ex_val H + n)
                | strong_or_right _ => a
                end
        | inr n => f [n|]
        end
    ).
    split.
    -   intros [a|[a a_lt]] [b|[b b_lt]] eq.
        +   do 2 destruct (strong_excluded_middle _).
            *   apply f_inj in eq.
                apply plus_rcancel in eq.
                rewrite_ex_val aa aaa.
                rewrite_ex_val bb bbb.
                subst.
                reflexivity.
            *   rewrite_ex_val x xH.
                subst.
                rewrite not_ex in n0.
                specialize (n0 (x + n)).
                contradiction.
            *   rewrite_ex_val x xH.
                subst.
                rewrite not_ex in n0.
                specialize (n0 (x + n)).
                contradiction.
            *   rewrite eq; reflexivity.
        +   destruct (strong_excluded_middle _).
            *   cbn in eq.
                apply f_inj in eq.
                exfalso.
                rewrite <- eq in b_lt.
                rewrite <- (plus_lid n) in b_lt at 2.
                apply lt_plus_rcancel in b_lt.
                contradiction (nat_neg2 b_lt).
            *   cbn in eq.
                rewrite not_ex in n0.
                specialize (n0 b).
                symmetry in eq; contradiction.
        +   cbn in eq.
            destruct (strong_excluded_middle _).
            *   apply f_inj in eq.
                exfalso.
                rewrite eq in a_lt.
                rewrite <- (plus_lid n) in a_lt at 2.
                apply lt_plus_rcancel in a_lt.
                contradiction (nat_neg2 a_lt).
            *   rewrite not_ex in n0.
                specialize (n0 a).
                contradiction.
        +   cbn in eq.
            apply f_inj in eq.
            apply f_equal.
            apply set_type_eq; cbn.
            exact eq.
    -   intros y.
        classic_case (∃ m, f m = y) as [ex|not_ex].
        +   destruct ex as [m m_eq].
            classic_case (m < n) as [ltq|nltq].
            *   exists (inr [m|ltq]).
                exact m_eq.
            *   rewrite nlt_le in nltq.
                apply nat_le_ex in nltq as [c c_eq].
                exists (inl (f c)).
                destruct (strong_excluded_middle _) as [ex|nex].
                --  rewrite_ex_val x xH.
                    apply f_inj in xH.
                    subst.
                    rewrite plus_comm.
                    reflexivity.
                --  rewrite not_ex in nex.
                    subst.
                    specialize (nex c).
                    contradiction.
        +   exists (inl y).
            destruct (strong_excluded_middle _) as [ex|nex]; try contradiction.
            reflexivity.
Qed.

Theorem nat_mult_nat : |nat| * |nat| = |nat|.
Proof.
    assert (|nat| = |set_type (λ n, 0 ≠ n)|) as eq.
    {
        assert (∀ n, 0 ≠ nat_suc n) as suc_neq by (intros n c; inversion c).
        equiv_simpl.
        exists (λ n, [nat_suc n | suc_neq n]).
        split.
        -   intros a b eq.
            inversion eq.
            reflexivity.
        -   intros [y y_neq].
            nat_destruct y; try contradiction.
            exists y.
            apply set_type_eq; reflexivity.
    }
    rewrite eq at 3; clear eq.
    unfold mult; equiv_simpl.
    pose (f (x : nat * nat) := (2 ^ (fst x) * (2 * snd x + 1))%nat).
    assert (∀ x, 0 ≠ f x) as f_in.
    {
        intros [x1 x2] eq.
        unfold f in eq; cbn in eq.
        apply mult_zero in eq.
        destruct eq as [eq|eq].
        -   apply nat_pow_not_zero in eq; try contradiction.
            intro contr; inversion contr.
        -   apply nat_plus_zero in eq.
            destruct eq as [C0 C1]; inversion C1.
    }
    exists (λ x, [f x|f_in x]).
    assert ((zero (U := nat)) ≠ 2) as two_nz by (intro C; inversion C).
    split.
    -   intros [a1 a2] [b1 b2] eq.
        unfold f in eq; cbn in eq.
        inversion eq as [eq2].
        clear eq.
        revert b1 eq2.
        nat_induction a1.
        +   intros b1 eq.
            rewrite nat_pow_zero, mult_lid in eq.
            nat_destruct b1.
            *   rewrite nat_pow_zero, mult_lid in eq.
                apply plus_rcancel in eq.
                apply nat_mult_lcancel in eq; try exact two_nz.
                rewrite eq; reflexivity.
            *   rewrite nat_pow_suc in eq.
                rewrite (mult_comm _ 2) in eq.
                rewrite <- mult_assoc in eq.
                do 2 rewrite (mult_comm 2) in eq.
                symmetry in eq.
                apply nat_even_neq_odd in eq.
                contradiction.
        +   intros b1 eq.
            nat_destruct b1.
            *   rewrite nat_pow_zero, mult_lid in eq.
                rewrite nat_pow_suc in eq.
                rewrite (mult_comm _ 2) in eq.
                rewrite <- mult_assoc in eq.
                do 3 rewrite (mult_comm 2) in eq.
                apply nat_even_neq_odd in eq.
                contradiction.
            *   do 2 rewrite nat_pow_suc in eq.
                do 2 rewrite (mult_comm _ 2) in eq.
                do 2 rewrite <- mult_assoc in eq.
                apply mult_lcancel in eq; try exact two_nz.
                specialize (IHa1 _ eq).
                inversion IHa1.
                reflexivity.
    -   intros [y y_nz].
        pose (S n := ¬((2 ^ n)%nat ∣ y)).
        assert (∃ n, S n) as S_ex.
        {
            exists y.
            unfold S.
            intros div.
            apply nat_div_le in div; try exact y_nz.
            assert (∀ n, nat_suc n < (2^(nat_suc n))%nat) as ltq.
            {
                clear.
                nat_induction n.
                -   rewrite nat_pow_one.
                    split.
                    +   unfold le, one, plus; cbn.
                        exact true.
                    +   intro contr; inversion contr.
                -   rewrite nat_pow_suc.
                    apply lt_lplus with 1 in IHn.
                    change (1 + nat_suc n) with (nat_suc (nat_suc n)) in IHn.
                    apply (trans IHn).
                    rewrite ldist.
                    rewrite mult_rid.
                    apply lt_rplus.
                    clear IHn.
                    nat_induction n.
                    +   rewrite nat_pow_one.
                        split.
                        *   unfold one, plus, le; cbn.
                            exact true.
                        *   intro contr; inversion contr.
                    +   apply (trans IHn).
                        rewrite (nat_pow_suc _ (nat_suc n)).
                        rewrite ldist.
                        rewrite mult_rid.
                        rewrite <- plus_lid at 1.
                        apply lt_rplus.
                        split; try apply nat_pos.
                        intro contr.
                        rewrite <- contr in IHn.
                        pose proof (lt_le_trans IHn (nat_pos 1))
                            as [C0 C1]; contradiction.
            }
            nat_destruct y.
            -   rewrite nat_pow_zero in div.
                pose proof (le_lt_trans div (make_and (nat_pos 1) not_trivial_one))
                    as [C0 C1]; contradiction.
            -   specialize (ltq y).
                pose proof (lt_le_trans ltq div) as [C0 C1]; contradiction.
        }
        pose proof (well_ordered S S_ex) as [x1 [Sx1 x1_min]].
        nat_destruct x1.
        {
            unfold S in Sx1.
            rewrite nat_pow_zero in Sx1.
            pose proof (one_divides y).
            contradiction.
        }
        unfold S in Sx1.
        assert ((2^x1)%nat ∣ y) as x1_div.
        {
            classic_contradiction contr.
            specialize (x1_min _ contr).
            rewrite <- nlt_le in x1_min.
            pose proof (nat_lt_suc x1).
            contradiction.
        }
        destruct x1_div as [c c_eq].
        assert (odd c) as c_odd.
        {
            intros [d d_eq].
            subst c.
            rewrite <- (nat_pow_one 2) in c_eq at 1.
            rewrite <- mult_assoc in c_eq.
            rewrite <- nat_pow_plus in c_eq.
            change (1 + x1) with (nat_suc x1) in c_eq.
            unfold divides in Sx1.
            rewrite not_ex in Sx1.
            specialize (Sx1 d).
            contradiction.
        }
        apply nat_odd_plus_one in c_odd as [x2 x2_eq].
        exists (x1, x2).
        apply set_type_eq; cbn.
        unfold f; cbn.
        rewrite <- c_eq.
        rewrite x2_eq.
        apply mult_comm.
Qed.
(* begin hide *)
Close Scope card_scope.
(* end hide *)
