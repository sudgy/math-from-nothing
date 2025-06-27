Require Import init.

Require Export card2_pow.
Require Export nat.
Require Import ord2_nat.
Require Import set_finite.

Open Scope card_scope.

Theorem ord_to_card_nat : ∀ n : nat,
    ord_to_card (from_nat n) = from_nat n.
Proof.
    nat_induction n.
    -   do 2 rewrite homo_zero.
        symmetry; apply homo_zero.
    -   do 2 rewrite from_nat_suc.
        rewrite (homo_plus (f := ord_to_card)).
        rewrite IHn.
        rewrite homo_one.
        reflexivity.
Qed.

Theorem from_nat_card : ∀ n : nat,
    from_nat n = |nat_to_set_type n|.
Proof.
    intros n.
    rewrite <- ord_to_card_nat.
    rewrite from_nat_ord.
    unfold ord_to_card; cbn.
    rewrite unary_op_eq.
    reflexivity.
Qed.

Global Instance card_char_zero : CharacteristicZero card.
Proof.
    split.
    intros n.
    rewrite from_nat_card.
    intros contr.
    symmetry in contr.
    unfold zero in contr; equiv_simpl in contr.
    destruct contr as [f f_bij].
    contradiction (empty_false (f [n | nat_lt_suc n])).
Qed.

Lemma from_nat_card_inj_lemma :
    ∀ a b, from_nat (nat_suc a) ≤ from_nat (nat_suc b)
    → from_nat a ≤ from_nat b.
Proof.
    intros a b.
    do 4 rewrite from_nat_card.
    unfold le; equiv_simpl.
    intros [f f_inj].
    pose (g (x : set_type (λ x, x < a)) :=
        let x' := [[x|] | trans [|x] (nat_lt_suc a)] in
        If [f x'|] = b then f [a|nat_lt_suc a] else f x').
    assert (∀ x, [g x|] < b) as g_lt.
    {
        intros [x x_lt].
        unfold g; cbn.
        destruct (sem _) as [eq|neq].
        -   split.
            +   rewrite <- nat_lt_suc_le.
                exact [|f _].
            +   intros contr.
                rewrite <- eq in contr.
                apply set_type_eq in contr.
                apply inj in contr.
                apply set_type_eq in contr; cbn in contr.
                subst.
                contradiction (irrefl _ x_lt).
        -   split; [>|exact neq].
            rewrite <- nat_lt_suc_le.
            exact [|f _].
    }
    exists (λ a, [[g a|]|g_lt a]).
    split.
    intros [m m_lt] [n n_lt] eq.
    apply set_type_eq2.
    apply set_type_eq in eq; cbn in eq.
    apply set_type_eq in eq; cbn in eq.
    unfold g in eq.
    unfold initial_segment in *.
    destruct (sem _) as [m_eq|m_neq].
    all: destruct (sem _) as [n_eq|n_neq].
    all: cbn in *.
    -   rewrite <- n_eq in m_eq.
        apply set_type_eq in m_eq; cbn in m_eq.
        apply inj in m_eq.
        apply set_type_eq in m_eq; cbn in m_eq.
        exact m_eq.
    -   apply inj in eq.
        apply set_type_eq in eq; cbn in eq.
        subst.
        contradiction (irrefl _ n_lt).
    -   apply inj in eq.
        apply set_type_eq in eq; cbn in eq.
        subst.
        contradiction (irrefl _ m_lt).
    -   apply inj in eq.
        apply set_type_eq in eq; cbn in eq.
        exact eq.
Qed.

Lemma from_nat_card_zero_eq : ∀ n, (0 : card) = from_nat n → 0 = n.
Proof.
    intros n n_eq.
    symmetry in n_eq.
    rewrite from_nat_card in n_eq.
    unfold zero in n_eq; equiv_simpl in n_eq.
    classic_contradiction contr.
    destruct n_eq as [f f_bij].
    contradiction (empty_false (f [0|all_pos2 contr])).
Qed.

Global Instance from_nat_card_inj : Injective (from_nat (U := card)).
Proof.
    split.
    intros a b eq.
    revert b eq.
    nat_induction a; intros b eq.
    -   rewrite homo_zero in eq.
        exact (from_nat_card_zero_eq b eq).
    -   nat_destruct b.
        +   rewrite homo_zero in eq.
            symmetry in eq.
            apply from_nat_card_zero_eq in eq.
            contradiction (nat_zero_suc eq).
        +   apply f_equal.
            apply IHa; clear IHa.
            apply antisym.
            *   apply from_nat_card_inj_lemma.
                rewrite eq.
                apply refl.
            *   apply from_nat_card_inj_lemma.
                rewrite eq.
                apply refl.
Qed.

Theorem card_to_initial_ord_nat : ∀ n : nat,
    card_to_initial_ord (from_nat n) = from_nat n.
Proof.
    intros n.
    rewrite <- ord_to_card_nat.
    apply card_to_initial_ord_other_eq.
    intros β β_lt.
    pose proof (ord_lt_ω β (trans β_lt (nat_lt_ω n))) as [m m_eq]; subst.
    apply homo_lt2 in β_lt.
    split.
    -   apply ord_to_card_le.
        apply (homo_le2 (f := from_nat)).
        apply β_lt.
    -   do 2 rewrite ord_to_card_nat.
        intros contr.
        apply inj in contr.
        subst.
        contradiction (irrefl _ β_lt).
Qed.

Global Instance from_nat_card_le : HomomorphismLe (from_nat (U := card)).
Proof.
    split.
    intros a b leq.
    apply (homo_le2 (f := card_to_initial_ord)).
    do 2 rewrite card_to_initial_ord_nat.
    apply homo_le.
    exact leq.
Qed.

Theorem card_omega : ord_to_card ω = |nat|.
Proof.
    unfold ord_to_card, ω; cbn.
    rewrite unary_op_eq.
    reflexivity.
Qed.

Theorem nat_lt_card : ∀ n, from_nat n < |nat|.
Proof.
    intros n.
    order_contradiction leq.
    apply nat_not_finite.
    unfold simple_finite.
    exists n.
    rewrite from_nat_card in leq.
    unfold le in leq; equiv_simpl in leq.
    exact leq.
Qed.

Theorem card_omega_initial : card_to_initial_ord (|nat|) = ω.
Proof.
    rewrite <- card_omega.
    apply card_to_initial_ord_other_eq.
    intros β β_lt.
    apply ord_lt_ω in β_lt as [n n_eq]; subst.
    rewrite ord_to_card_nat.
    rewrite card_omega.
    apply nat_lt_card.
Qed.

Theorem card_lt_nat : ∀ κ : card, κ < |nat| → ∃ n, κ = from_nat n.
Proof.
    intros κ κ_lt.
    apply (homo_lt2 (f := card_to_initial_ord)) in κ_lt.
    rewrite card_omega_initial in κ_lt.
    apply ord_lt_ω in κ_lt as [n n_eq].
    exists n.
    rewrite <- ord_to_card_nat.
    rewrite <- n_eq.
    symmetry; apply card_to_initial_ord_to_card_eq.
Qed.

Theorem card_lt_one_eq : ∀ κ, κ < 1 → 0 = κ.
Proof.
    intros κ κ_lt.
    rewrite <- (homo_one (f := from_nat)) in κ_lt.
    pose proof κ_lt as κ_fin.
    apply (trans2 (nat_lt_card _)) in κ_fin.
    apply card_lt_nat in κ_fin as [n eq]; subst.
    apply homo_lt2 in κ_lt.
    apply nat_lt_one_eq in κ_lt.
    subst.
    symmetry; apply homo_zero.
Qed.

Theorem card_pos_one : ∀ κ, 0 ≠ κ ↔ 1 ≤ κ.
Proof.
    intros κ.
    split.
    -   intros κ_nz.
        order_contradiction ltq.
        apply card_lt_one_eq in ltq.
        contradiction.
    -   intros κ_ge eq; subst.
        rewrite <- nlt_le in κ_ge.
        apply κ_ge.
        exact card_one_pos.
Qed.

Theorem aleph'_nat : ∀ n, aleph' (from_nat n) = from_nat n.
Proof.
    intros n.
    induction n as [n IHn] using strong_induction.
    apply antisym.
    -   apply aleph'_least.
        intros β β_lt.
        pose proof (ord_lt_ω _ (trans β_lt (nat_lt_ω _))) as [m m_eq].
        subst β.
        apply homo_lt2 in β_lt.
        specialize (IHn _ β_lt).
        rewrite IHn.
        apply homo_lt.
        exact β_lt.
    -   order_contradiction ltq.
        pose proof (card_lt_nat _ (trans ltq (nat_lt_card _))) as [m m_eq].
        rewrite m_eq in ltq.
        apply homo_lt2 in ltq.
        specialize (IHn _ ltq).
        rewrite <- IHn in m_eq.
        do 2 apply inj in m_eq.
        subst.
        contradiction (irrefl _ ltq).
Qed.

Theorem aleph_0 : aleph 0 = |nat|.
Proof.
    unfold aleph.
    rewrite plus_rid.
    apply antisym.
    -   apply aleph'_least.
        intros β β_lt.
        apply ord_lt_ω in β_lt as [n n_eq]; subst β.
        rewrite aleph'_nat.
        apply nat_lt_card.
    -   order_contradiction ltq.
        apply card_lt_nat in ltq as [n n_eq].
        rewrite <- aleph'_nat in n_eq.
        apply inj in n_eq.
        pose proof (nat_lt_ω n) as ltq.
        rewrite n_eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

Close Scope card_scope.
