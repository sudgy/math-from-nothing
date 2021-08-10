Require Import init.

Require Import nat0.
Require Export card_base.
Require Import card_order.
Require Import card_plus.
Require Import card_mult.
Require Import card_pow.
Require Import set.
Require Import function.
Require Import ord_basic.
Require Import mult_div.

Theorem nat0_to_card_plus :
        ∀ a b, nat0_to_card a + nat0_to_card b = nat0_to_card (a + b).
    intros a b.
    unfold plus at 1, nat0_to_card; equiv_simpl.
    pose (dom := sum (set_type (λ x, x < a)) (set_type (λ x, x < b))).
    pose (f (x : dom) := match x with
                         | inl y => [y|]
                         | inr y => a + [y|]
                         end).
    assert (∀ x, f x < a + b) as f_in.
    {
        intros [[x x_lt]|[x x_lt]]; cbn.
        -   pose proof (nat0_le_zero b) as leq.
            apply le_lplus with a in leq.
            rewrite plus_rid in leq.
            exact (lt_le_trans x_lt leq).
        -   apply lt_lplus.
            exact x_lt.
    }
    exists (λ x, [f x|f_in x]).
    split.
    -   intros [[m m_lt]|[m m_lt]] [[n n_lt]|[n n_lt]] eq'.
        all: inversion eq' as [eq]; clear eq'.
        all: subst.
        +   apply f_equal.
            apply set_type_eq; reflexivity.
        +   exfalso.
            rewrite <- (plus_rid a) in m_lt at 2.
            apply lt_plus_lcancel in m_lt.
            exact (nat0_lt_zero _ m_lt).
        +   exfalso.
            rewrite <- (plus_rid a) in n_lt at 2.
            apply lt_plus_lcancel in n_lt.
            exact (nat0_lt_zero _ n_lt).
        +   apply plus_lcancel in eq.
            subst.
            apply f_equal.
            apply set_type_eq; reflexivity.
    -   intros [y y_lt].
        classic_case (y < a) as [ltq|leq].
        +   exists (inl [y|ltq]).
            cbn.
            apply set_type_eq; reflexivity.
        +   rewrite nlt_le in leq.
            apply nat0_le_ex in leq as [c c_eq].
            pose proof y_lt as y_lt2.
            rewrite <- c_eq in y_lt2.
            apply lt_plus_lcancel in y_lt2.
            exists (inr [c|y_lt2]).
            cbn.
            apply set_type_eq; cbn.
            exact c_eq.
Qed.
Corollary nat0_suc_to_card :
        ∀ n, nat0_to_card (nat0_suc n) = nat0_to_card n + 1.
    intros n.
    change (nat0_suc n) with (1 + n).
    rewrite <- nat0_to_card_plus.
    apply comm.
Qed.
Theorem nat0_to_card_sucs_le :
        ∀ a b, nat0_to_card (nat0_suc a) <= nat0_to_card (nat0_suc b) →
        nat0_to_card a <= nat0_to_card b.
    intros a b leq.
    unfold nat0_to_card, le in *; equiv_simpl; equiv_simpl in leq.
    destruct leq as [f f_inj].
    pose (g (x : set_type (λ x, x < a)) :=
        let x' := [[x|] | trans [|x] (nat0_lt_suc a)] in
        If [f x'|] = b then f [a|nat0_lt_suc a] else f x').
    assert (∀ x, [g x|] < b) as g_lt.
    {
        intros [x x_lt].
        unfold g; cbn.
        case_if; cbn in *.
        -   remember (f [a | nat0_lt_suc a]) as fa.
            pose proof [|fa] as fa_lt; cbn in fa_lt.
            rewrite nat0_lt_suc_le in fa_lt.
            split; try exact fa_lt.
            intro eq.
            rewrite <- eq in e.
            apply set_type_eq in e.
            rewrite Heqfa in e.
            apply f_inj in e.
            inversion e.
            destruct x_lt; contradiction.
        -   split; try exact n.
            rewrite <- nat0_lt_suc_le.
            exact [|f [x | trans x_lt (nat0_lt_suc a)]].
    }
    exists (λ x, [[g x|] | g_lt x]).
    intros [m m_lt] [n n_lt] eq.
    unfold g in eq; cbn in eq.
    inversion eq as [eq2].
    apply set_type_eq in eq2.
    clear eq.
    repeat case_if.
    -   rewrite <- e in e0.
        apply set_type_eq in e0.
        apply f_inj in e0.
        apply set_type_eq; cbn.
        inversion e0.
        reflexivity.
    -   exfalso.
        apply f_inj in eq2.
        inversion eq2.
        subst.
        destruct n_lt; contradiction.
    -   exfalso.
        apply f_inj in eq2.
        inversion eq2.
        subst.
        destruct m_lt; contradiction.
    -   apply set_type_eq; cbn.
        apply f_inj in eq2.
        inversion eq2.
        reflexivity.
Qed.
Theorem nat0_to_card_eq : ∀ a b, nat0_to_card a = nat0_to_card b → a = b.
    nat0_induction a.
    -   intros b eq.
        nat0_destruct b; try reflexivity.
        unfold nat0_to_card in eq; equiv_simpl in eq.
        destruct eq as [f f_bij].
        pose proof (rand f_bij [b|nat0_lt_suc b]) as [x x_eq].
        contradiction (nat0_lt_0_false x).
    -   nat0_destruct b.
        +   intros eq.
            unfold nat0_to_card in eq; equiv_simpl in eq.
            destruct eq as [f f_bij].
            contradiction (nat0_lt_0_false (f [a|nat0_lt_suc a])).
        +   intros eq.
            apply f_equal.
            apply IHa.
            apply antisym.
            *   apply nat0_to_card_sucs_le.
                rewrite eq.
                apply refl.
            *   apply nat0_to_card_sucs_le.
                rewrite eq.
                apply refl.
Qed.

Theorem nat0_to_card_plus_lcancel : ∀ {a b} c,
        nat0_to_card c + nat0_to_card a = nat0_to_card c + nat0_to_card b →
        nat0_to_card a = nat0_to_card b.
    intros a b c eq.
    do 2 rewrite nat0_to_card_plus in eq.
    apply nat0_to_card_eq in eq.
    apply plus_lcancel in eq.
    rewrite eq; reflexivity.
Qed.
Theorem nat0_to_card_plus_rcancel : ∀ {a b} c,
        nat0_to_card a + nat0_to_card c = nat0_to_card b + nat0_to_card c →
        nat0_to_card a = nat0_to_card b.
    intros a b c eq.
    do 2 rewrite (plus_comm _ (nat0_to_card c)) in eq.
    apply (nat0_to_card_plus_lcancel _ eq).
Qed.
Theorem nat0_to_card_lt_lplus : ∀ {a b} c,
        nat0_to_card a < nat0_to_card b →
        nat0_to_card c + nat0_to_card a < nat0_to_card c + nat0_to_card b.
    intros a b c [leq neq].
    split.
    -   apply le_lplus.
        exact leq.
    -   intros eq.
        apply nat0_to_card_plus_lcancel in eq.
        contradiction.
Qed.
Theorem nat0_to_card_lt_rplus : ∀ {a b} c,
        nat0_to_card a < nat0_to_card b →
        nat0_to_card a + nat0_to_card c < nat0_to_card b + nat0_to_card c.
    intros a b c ltq.
    do 2 rewrite (plus_comm _ (nat0_to_card c)).
    apply nat0_to_card_lt_lplus.
    exact ltq.
Qed.
Theorem nat0_to_card_le_plus_lcancel : ∀ {a b} c,
        nat0_to_card c + nat0_to_card a <= nat0_to_card c + nat0_to_card b →
        nat0_to_card a <= nat0_to_card b.
    intros a b c leq.
    nat0_induction c.
    -   change (nat0_to_card 0) with 0 in leq.
        do 2 rewrite plus_lid in leq.
        exact leq.
    -   apply IHc; clear IHc.
        do 2 rewrite nat0_to_card_plus in *.
        apply nat0_to_card_sucs_le.
        do 2 rewrite <- nat0_plus_lsuc.
        exact leq.
Qed.
Theorem nat0_to_card_le_plus_rcancel : ∀ {a b} c,
        nat0_to_card a + nat0_to_card c <= nat0_to_card b + nat0_to_card c →
        nat0_to_card a <= nat0_to_card b.
    intros a b c leq.
    do 2 rewrite (plus_comm _ (nat0_to_card c)) in leq.
    exact (nat0_to_card_le_plus_lcancel _ leq).
Qed.

Theorem nat0_to_card_le : ∀ a b, (a <= b) = (nat0_to_card a <= nat0_to_card b).
    intros a b.
    apply propositional_ext; split.
    -   revert b; nat0_induction a.
        +   intros; apply card_le_zero.
        +   nat0_destruct b.
            *   intros contr.
                pose proof (antisym contr (nat0_le_zero _)) as eq.
                inversion eq.
            *   intros leq.
                do 2 rewrite nat0_suc_to_card.
                apply le_rplus.
                apply IHa.
                rewrite nat0_sucs_le in leq.
                exact leq.
    -   revert b; nat0_induction a.
        +   intros; apply nat0_le_zero.
        +   nat0_destruct b.
            *   intros contr.
                pose proof (antisym contr (card_le_zero _)) as eq.
                apply nat0_to_card_eq in eq.
                inversion eq.
            *   intros leq.
                rewrite nat0_sucs_le.
                apply IHa.
                do 2 rewrite nat0_suc_to_card in leq.
                apply nat0_to_card_le_plus_rcancel in leq.
                exact leq.
Qed.

Theorem nat0_to_card_lt : ∀ a b, (a < b) = (nat0_to_card a < nat0_to_card b).
    intros a b.
    apply propositional_ext; split; intro leq; split.
    -   rewrite <- nat0_to_card_le.
        apply leq.
    -   intro contr.
        apply nat0_to_card_eq in contr.
        destruct leq; contradiction.
    -   rewrite nat0_to_card_le.
        apply leq.
    -   intro contr.
        rewrite contr in leq.
        destruct leq; contradiction.
Qed.

Theorem nat0_to_card_ord_lt : ∀ a b,
        (nat0_to_card a < nat0_to_card b) = (nat0_to_ord a < nat0_to_ord b).
    intros a b.
    rewrite <- nat0_to_card_lt.
    rewrite nat0_to_ord_lt.
    reflexivity.
Qed.

Theorem nat0_to_ord_to_card : ∀ n, ord_to_card (nat0_to_ord n) = nat0_to_card n.
    intros n.
    unfold ord_to_card, nat0_to_ord, nat0_to_card; equiv_simpl.
    exists (λ x, x).
    exact identity_bijective.
Qed.

Theorem nat0_to_card_mult :
        ∀ a b, nat0_to_card a * nat0_to_card b = nat0_to_card (a * b).
    intros a b.
    unfold mult at 1, nat0_to_card; equiv_simpl.
    pose (dom := prod (set_type (λ m, m < a)) (set_type (λ m, m < b))).
    pose (f (n : dom) := [fst n|] * b + [snd n|]).
    assert (∀ n : dom, f n < a * b) as f_in.
    {
        intros [[m m_lt] [n n_lt]].
        unfold f; cbn.
        clear dom f.
        destruct a.
        -   apply nat0_lt_zero in m_lt.
            contradiction.
        -   rewrite nat0_mult_lsuc.
            rewrite nat0_lt_suc_le in m_lt.
            apply nat0_le_rmult with b in m_lt.
            apply le_rplus with n in m_lt.
            apply lt_lplus with (a * b) in n_lt.
            rewrite (plus_comm b).
            exact (le_lt_trans m_lt n_lt).
    }
    exists (λ x, [f x|f_in x]).
    split.
    -   intros [[m1 m1_lt] [n1 n1_lt]] [[m2 m2_lt] [n2 n2_lt]] eq.
        inversion eq as [eq2]; clear eq.
        unfold f in eq2; cbn in eq2.
        destruct (trichotomy m1 m2) as [[leq|eq]|leq].
        +   exfalso.
            apply nat0_lt_ex in leq as [c [c_nz c_eq]].
            rewrite <- c_eq in eq2.
            rewrite rdist in eq2.
            rewrite <- assoc in eq2.
            apply plus_lcancel in eq2.
            rewrite eq2 in n1_lt.
            pose proof (nat0_le_self_rplus (c * b) n2) as eq3.
            pose proof (nat0_le_self_lmult b c c_nz) as eq4.
            pose proof (trans eq4 eq3) as eq5.
            pose proof (le_lt_trans eq5 n1_lt) as eq6.
            destruct eq6; contradiction.
        +   subst.
            apply plus_lcancel in eq2.
            subst.
            apply f_equal2; apply set_type_eq; reflexivity.
        +   exfalso.
            apply nat0_lt_ex in leq as [c [c_nz c_eq]].
            rewrite <- c_eq in eq2.
            rewrite rdist in eq2.
            rewrite <- assoc in eq2.
            apply plus_lcancel in eq2.
            rewrite <- eq2 in n2_lt.
            pose proof (nat0_le_self_rplus (c * b) n1) as eq3.
            pose proof (nat0_le_self_lmult b c c_nz) as eq4.
            pose proof (trans eq4 eq3) as eq5.
            pose proof (le_lt_trans eq5 n2_lt) as eq6.
            destruct eq6; contradiction.
    -   intros [n n_lt].
        nat0_destruct b.
        {
            exfalso.
            rewrite mult_ranni in n_lt.
            contradiction (nat0_lt_zero _ n_lt).
        }
        assert (0 ≠ nat0_suc b) as b_nz by (intro contr; inversion contr).
        pose proof (euclidean_division n (nat0_suc b) b_nz)
            as [q [r [eq r_lt]]]; cbn in *.
        assert (q < a) as q_lt.
        {
            rewrite eq in n_lt.
            classic_contradiction contr.
            rewrite nlt_le in contr.
            apply nat0_le_rmult with (nat0_suc b) in contr.
            pose proof (lt_le_trans n_lt contr) as ltq.
            rewrite mult_comm in ltq.
            rewrite <- (plus_rid (q * nat0_suc b)) in ltq at 2.
            apply lt_plus_lcancel in ltq.
            contradiction (nat0_lt_zero _ ltq).
        }
        exists ([q|q_lt], [r|r_lt]).
        apply set_type_eq; cbn.
        unfold f; cbn.
        symmetry; rewrite mult_comm.
        exact eq.
Qed.
