Require Import init.

Require Import nat.
Require Export card_base.
Require Import card_order.
Require Import card_plus.
Require Import card_mult.
Require Import card_pow.
Require Import set.
Require Import function.
Require Import ord_basic.
Require Import nat_domain.

Theorem nat_to_card_plus :
    ∀ a b, nat_to_card a + nat_to_card b = nat_to_card (a + b).
Proof.
    intros a b.
    unfold plus at 1, nat_to_card; equiv_simpl.
    pose (dom := sum_type (set_type (λ x, x < a)) (set_type (λ x, x < b))).
    pose (f (x : dom) := match x with
                         | inl y => [y|]
                         | inr y => a + [y|]
                         end).
    assert (∀ x, f x < a + b) as f_in.
    {
        intros [[x x_lt]|[x x_lt]]; cbn.
        -   pose proof (nat_pos b) as leq.
            apply le_lplus with a in leq.
            rewrite plus_rid in leq.
            exact (lt_le_trans x_lt leq).
        -   apply lt_lplus.
            exact x_lt.
    }
    exists (λ x, [f x|f_in x]).
    split; split.
    -   intros [[m m_lt]|[m m_lt]] [[n n_lt]|[n n_lt]] eq'.
        all: inversion eq' as [eq]; clear eq'.
        all: subst.
        +   apply f_equal.
            apply set_type_eq; reflexivity.
        +   exfalso.
            rewrite <- (plus_rid a) in m_lt at 2.
            apply lt_plus_lcancel in m_lt.
            exact (nat_neg2 m_lt).
        +   exfalso.
            rewrite <- (plus_rid a) in n_lt at 2.
            apply lt_plus_lcancel in n_lt.
            exact (nat_neg2 n_lt).
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
            apply nat_le_ex in leq as [c c_eq].
            pose proof y_lt as y_lt2.
            rewrite <- c_eq in y_lt2.
            apply lt_plus_lcancel in y_lt2.
            exists (inr [c|y_lt2]).
            cbn.
            apply set_type_eq; cbn.
            exact c_eq.
Qed.
Corollary nat_suc_to_card :
    ∀ n, nat_to_card (nat_suc n) = nat_to_card n + 1.
Proof.
    intros n.
    change (nat_suc n) with (1 + n).
    rewrite <- nat_to_card_plus.
    apply plus_comm.
Qed.
Theorem nat_to_card_sucs_le :
    ∀ a b, nat_to_card (nat_suc a) ≤ nat_to_card (nat_suc b) →
    nat_to_card a ≤ nat_to_card b.
Proof.
    intros a b leq.
    unfold nat_to_card, le in *; equiv_simpl; equiv_simpl in leq.
    destruct leq as [f f_inj].
    pose (g (x : set_type (λ x, x < a)) :=
        let x' := [[x|] | trans [|x] (nat_lt_suc a)] in
        If [f x'|] = b then f [a|nat_lt_suc a] else f x').
    assert (∀ x, [g x|] < b) as g_lt.
    {
        intros [x x_lt].
        unfold g; cbn.
        case_if; cbn in *.
        -   remember (f [a | nat_lt_suc a]) as fa.
            pose proof [|fa] as fa_lt; cbn in fa_lt.
            rewrite nat_lt_suc_le in fa_lt.
            split; try exact fa_lt.
            intro eq.
            rewrite <- eq in e.
            apply set_type_eq in e.
            rewrite Heqfa in e.
            apply f_inj in e.
            inversion e.
            destruct x_lt; contradiction.
        -   split; try exact n.
            rewrite <- nat_lt_suc_le.
            exact [|f [x | trans x_lt (nat_lt_suc a)]].
    }
    exists (λ x, [[g x|] | g_lt x]).
    split.
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
Theorem nat_to_card_eq : ∀ a b, nat_to_card a = nat_to_card b → a = b.
Proof.
    nat_induction a.
    -   intros b eq.
        nat_destruct b; try reflexivity.
        unfold nat_to_card in eq; equiv_simpl in eq.
        destruct eq as [f f_bij].
        pose proof (sur f [b|nat_lt_suc b]) as [x x_eq].
        contradiction (nat_lt_0_false x).
    -   nat_destruct b.
        +   intros eq.
            unfold nat_to_card in eq; equiv_simpl in eq.
            destruct eq as [f f_bij].
            contradiction (nat_lt_0_false (f [a|nat_lt_suc a])).
        +   intros eq.
            apply f_equal.
            apply IHa.
            apply antisym.
            *   apply nat_to_card_sucs_le.
                rewrite eq.
                apply refl.
            *   apply nat_to_card_sucs_le.
                rewrite eq.
                apply refl.
Qed.

Theorem nat_to_card_plus_lcancel : ∀ {a b} c,
    nat_to_card c + nat_to_card a = nat_to_card c + nat_to_card b →
    nat_to_card a = nat_to_card b.
Proof.
    intros a b c eq.
    do 2 rewrite nat_to_card_plus in eq.
    apply nat_to_card_eq in eq.
    apply plus_lcancel in eq.
    rewrite eq; reflexivity.
Qed.
Theorem nat_to_card_plus_rcancel : ∀ {a b} c,
    nat_to_card a + nat_to_card c = nat_to_card b + nat_to_card c →
    nat_to_card a = nat_to_card b.
Proof.
    intros a b c eq.
    do 2 rewrite (plus_comm _ (nat_to_card c)) in eq.
    apply (nat_to_card_plus_lcancel _ eq).
Qed.
Theorem nat_to_card_lt_lplus : ∀ {a b} c,
    nat_to_card a < nat_to_card b →
    nat_to_card c + nat_to_card a < nat_to_card c + nat_to_card b.
Proof.
    intros a b c [leq neq].
    split.
    -   apply le_lplus.
        exact leq.
    -   intros eq.
        apply nat_to_card_plus_lcancel in eq.
        contradiction.
Qed.
Theorem nat_to_card_lt_rplus : ∀ {a b} c,
    nat_to_card a < nat_to_card b →
    nat_to_card a + nat_to_card c < nat_to_card b + nat_to_card c.
Proof.
    intros a b c ltq.
    do 2 rewrite (plus_comm _ (nat_to_card c)).
    apply nat_to_card_lt_lplus.
    exact ltq.
Qed.
Theorem nat_to_card_le_plus_lcancel : ∀ {a b} c,
    nat_to_card c + nat_to_card a ≤ nat_to_card c + nat_to_card b →
    nat_to_card a ≤ nat_to_card b.
Proof.
    intros a b c leq.
    nat_induction c.
    -   change (nat_to_card 0) with (zero (U := card)) in leq.
        do 2 rewrite plus_lid in leq.
        exact leq.
    -   apply IHc; clear IHc.
        do 2 rewrite nat_to_card_plus in *.
        apply nat_to_card_sucs_le.
        do 2 rewrite <- nat_plus_lsuc.
        exact leq.
Qed.
Theorem nat_to_card_le_plus_rcancel : ∀ {a b} c,
    nat_to_card a + nat_to_card c ≤ nat_to_card b + nat_to_card c →
    nat_to_card a ≤ nat_to_card b.
Proof.
    intros a b c leq.
    do 2 rewrite (plus_comm _ (nat_to_card c)) in leq.
    exact (nat_to_card_le_plus_lcancel _ leq).
Qed.

Theorem nat_to_card_le : ∀ a b, (a ≤ b) = (nat_to_card a ≤ nat_to_card b).
Proof.
    intros a b.
    apply propositional_ext; split.
    -   revert b; nat_induction a.
        +   intros; apply card_le_zero.
        +   nat_destruct b.
            *   intros contr.
                pose proof (antisym contr (nat_pos _)) as eq.
                inversion eq.
            *   intros leq.
                do 2 rewrite nat_suc_to_card.
                apply le_rplus.
                apply IHa.
                rewrite nat_sucs_le in leq.
                exact leq.
    -   revert b; nat_induction a.
        +   intros; apply nat_pos.
        +   nat_destruct b.
            *   intros contr.
                pose proof (antisym contr (card_le_zero _)) as eq.
                apply nat_to_card_eq in eq.
                inversion eq.
            *   intros leq.
                rewrite nat_sucs_le.
                apply IHa.
                do 2 rewrite nat_suc_to_card in leq.
                apply nat_to_card_le_plus_rcancel in leq.
                exact leq.
Qed.

Theorem nat_to_card_lt : ∀ a b, (a < b) = (nat_to_card a < nat_to_card b).
Proof.
    intros a b.
    apply propositional_ext; split; intro leq; split.
    -   rewrite <- nat_to_card_le.
        apply leq.
    -   intro contr.
        apply nat_to_card_eq in contr.
        destruct leq; contradiction.
    -   rewrite nat_to_card_le.
        apply leq.
    -   intro contr.
        rewrite contr in leq.
        destruct leq; contradiction.
Qed.

Theorem nat_to_card_ord_lt : ∀ a b,
    (nat_to_card a < nat_to_card b) = (nat_to_ord a < nat_to_ord b).
Proof.
    intros a b.
    rewrite <- nat_to_card_lt.
    rewrite nat_to_ord_lt.
    reflexivity.
Qed.

Theorem nat_to_ord_to_card : ∀ n, ord_to_card (nat_to_ord n) = nat_to_card n.
Proof.
    intros n.
    unfold ord_to_card, nat_to_ord, nat_to_card; equiv_simpl.
    exists (λ x, x).
    exact identity_bijective.
Qed.

Theorem nat_to_card_mult :
    ∀ a b, nat_to_card a * nat_to_card b = nat_to_card (a * b).
Proof.
    intros a b.
    unfold mult at 1, nat_to_card; equiv_simpl.
    pose (dom := prod_type (set_type (λ m, m < a)) (set_type (λ m, m < b))).
    pose (f (n : dom) := [fst n|] * b + [snd n|]).
    assert (∀ n : dom, f n < a * b) as f_in.
    {
        intros [[m m_lt] [n n_lt]].
        unfold f; cbn.
        clear dom f.
        destruct a.
        -   apply nat_neg2 in m_lt.
            contradiction.
        -   rewrite nat_mult_lsuc.
            rewrite nat_lt_suc_le in m_lt.
            apply nat_le_rmult with b in m_lt.
            apply le_rplus with n in m_lt.
            apply lt_lplus with (a * b) in n_lt.
            rewrite (plus_comm b).
            exact (le_lt_trans m_lt n_lt).
    }
    exists (λ x, [f x|f_in x]).
    split; split.
    -   intros [[m1 m1_lt] [n1 n1_lt]] [[m2 m2_lt] [n2 n2_lt]] eq.
        inversion eq as [eq2]; clear eq.
        unfold f in eq2; cbn in eq2.
        destruct (trichotomy m1 m2) as [[leq|eq]|leq].
        +   exfalso.
            apply nat_lt_ex in leq as [c c_eq].
            rewrite <- c_eq in eq2.
            rewrite rdist in eq2.
            rewrite <- plus_assoc in eq2.
            apply plus_lcancel in eq2.
            rewrite eq2 in n1_lt.
            rewrite nat_mult_lsuc in n1_lt.
            rewrite <- plus_assoc in n1_lt.
            rewrite <- (plus_rid b) in n1_lt at 3.
            apply lt_plus_lcancel in n1_lt.
            contradiction (nat_neg2 n1_lt).
        +   subst.
            apply plus_lcancel in eq2.
            subst.
            apply f_equal2; apply set_type_eq; reflexivity.
        +   exfalso.
            apply nat_lt_ex in leq as [c c_eq].
            rewrite <- c_eq in eq2.
            rewrite rdist in eq2.
            rewrite <- plus_assoc in eq2.
            apply plus_lcancel in eq2.
            rewrite <- eq2 in n2_lt.
            rewrite nat_mult_lsuc in n2_lt.
            rewrite <- plus_assoc in n2_lt.
            rewrite <- (plus_rid b) in n2_lt at 3.
            apply lt_plus_lcancel in n2_lt.
            contradiction (nat_neg2 n2_lt).
    -   intros [n n_lt].
        nat_destruct b.
        {
            exfalso.
            rewrite mult_ranni in n_lt.
            contradiction (nat_neg2 n_lt).
        }
        assert (0 ≠ nat_suc b) as b_nz by (intro contr; inversion contr).
        pose proof (euclidean_division n (nat_suc b) b_nz)
            as [q [r [eq r_lt]]]; cbn in *.
        assert (q < a) as q_lt.
        {
            rewrite eq in n_lt.
            classic_contradiction contr.
            rewrite nlt_le in contr.
            apply nat_le_rmult with (nat_suc b) in contr.
            pose proof (lt_le_trans n_lt contr) as ltq.
            rewrite mult_comm in ltq.
            rewrite <- (plus_rid (q * nat_suc b)) in ltq at 2.
            apply lt_plus_lcancel in ltq.
            contradiction (nat_neg2 ltq).
        }
        rename r_lt into r_lt'.
        assert (r < nat_suc b) as r_lt.
        {
            destruct r_lt' as [r_z|r_lt]; [>|exact r_lt].
            rewrite <- r_z.
            apply nat_pos2.
        }
        exists ([q|q_lt], [r|r_lt]).
        apply set_type_eq; cbn.
        unfold f; cbn.
        symmetry; rewrite mult_comm.
        exact eq.
Qed.
