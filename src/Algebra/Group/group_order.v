Require Import init.

Require Export group_category.
Require Export group_subgroup.

Require Import set.
Require Export card.
Require Import card_types.
Require Export int.
Require Export nat.

Require Import mult_div.
Require Import int_domain.
Require Import order_self_abs.

Section CyclicGroup.

Local Open Scope int_scope.

Context {G : Group} (a : G).

Definition cyclic_set (x : G) := ∃ n : int, x = n × a.

Program Definition cyclic_Subgroup := {|subgroup_set := cyclic_set|}.
Next Obligation.
    exists 0.
    rewrite int_mult_lanni.
    reflexivity.
Qed.
Next Obligation.
    destruct H as [m m_eq], H0 as [n n_eq].
    exists (m + n).
    rewrite int_mult_rdist.
    rewrite m_eq, n_eq.
    reflexivity.
Qed.
Next Obligation.
    destruct H as [n n_eq].
    exists (-n).
    rewrite n_eq.
    apply int_mult_lneg.
Qed.

Definition cyclic_subgroup := subgroup cyclic_Subgroup : Group.

Local Open Scope card_scope.
Local Open Scope nat_scope.
Local Close Scope int_scope.

Definition group_order := |cyclic_subgroup|.

Theorem group_order_countable : group_order ≤ |nat|.
Proof.
    unfold group_order.
    rewrite <- int_size.
    unfold le; equiv_simpl.
    exists (λ (x : set_type cyclic_set), ex_val [|x]).
    split.
    intros [x x'] [y y']; cbn.
    rewrite_ex_val m m_eq.
    rewrite_ex_val n n_eq.
    subst x y.
    intro; subst.
    apply set_type_refl.
Qed.

Theorem group_order_nz : 0 ≠ group_order.
Proof.
    intros contr.
    unfold group_order in contr.
    assert cyclic_subgroup as x.
    {
        cbn.
        exists a, 1.
        symmetry; apply int_mult_lid.
    }
    exact (card_0_false cyclic_subgroup contr x).
Qed.

Let K (m : nat) := 0 ≠ m ∧ 0 = m × a.

Section UsesAbs.

Local Notation "| a |" := (abs a) (at level 30).

Lemma group_order_fin1 : ∀ n : nat, is_least le K n → group_order = from_nat n.
Proof.
    intros n [[n_nz n_eq] n_least].
    symmetry.
    rewrite from_nat_card.
    unfold group_order.
    equiv_simpl.
    assert (∀ m : nat_to_set_type n, cyclic_set ([m|] × a)) as f_in.
    {
        intros m.
        exists (from_nat [m|]).
        apply int_mult_nat.
    }
    exists (λ m, [_|f_in m]).
    split; split.
    -   intros [x x_lt] [y y_lt]; cbn.
        rewrite set_type_eq2.
        rewrite (@set_type_eq2 _ _ x y x_lt y_lt).
        intros eq.
        assert (∀ x y, x × a = y × a → y < n → x ≤ y → x = y) as wlog.
        {
            clear x y x_lt y_lt eq.
            intros x y eq y_lt leq.
            apply nat_le_ex in leq as [c]; subst.
            rewrite <- (plus_rid x) at 1.
            apply lplus.
            rewrite nat_mult_rdist in eq.
            rewrite <- (plus_rid (x × a)) in eq at 1.
            apply plus_lcancel in eq.
            classic_contradiction c_nz.
            specialize (n_least c (make_and c_nz eq)).
            pose proof (lt_le_trans y_lt n_least) as ltq.
            rewrite <- (plus_lid c) in ltq at 2.
            apply lt_plus_rcancel in ltq.
            contradiction (not_neg ltq).
        }
        destruct (connex x y) as [leq|leq].
        +   exact (wlog x y eq y_lt leq).
        +   symmetry.
            symmetry in eq.
            exact (wlog y x eq x_lt leq).
    -   intros [b [m b_eq]]; subst b.
        apply (inj_zero (from_nat (U := int))) in n_nz.
        pose proof (int_div m _ n_nz) as [q [r' [m_eq [r_pos r_lt]]]].
        apply int_pos_nat_ex in r_pos as [r]; subst r'.
        rewrite (abs_pos_eq _ (from_nat_pos2 _)) in r_lt.
        rewrite <- homo_lt2 in r_lt.
        exists [r|r_lt]; cbn.
        rewrite set_type_eq2.
        rewrite m_eq.
        rewrite int_mult_rdist.
        rewrite (mult_comm _ q).
        rewrite <- int_mult_mult.
        do 2 rewrite <- int_mult_nat.
        rewrite <- n_eq.
        rewrite int_mult_ranni.
        symmetry; apply plus_lid.
Qed.

End UsesAbs.

Theorem group_order_inf : group_order = |nat| ↔ (∀ n, 0 ≠ n → 0 ≠ n × a).
Proof.
    split.
    -   intros inf n n_nz contr.
        pose proof (well_ordered K) as m_ex.
        prove_parts m_ex.
        {
            exists n.
            split; assumption.
        }
        destruct m_ex as [m m_least].
        pose proof (group_order_fin1 m m_least) as m_eq.
        rewrite m_eq in inf.
        apply nat_lt_card in inf.
        contradiction inf.
    -   intros never_eq.
        apply antisym; [>apply group_order_countable|].
        unfold group_order.
        unfold le; equiv_simpl.
        assert (∀ n, cyclic_set (n × a)) as f_in.
        {
            intros n.
            exists (from_nat n).
            apply int_mult_nat.
        }
        exists (λ m, [_|f_in m]).
        split.
        intros x y eq.
        rewrite set_type_eq2 in eq.
        destruct (connex x y) as [leq|leq].
        +   apply nat_le_ex in leq as [c]; subst.
            rewrite nat_mult_rdist in eq.
            rewrite <- (plus_rid (x × a)) in eq at 1.
            apply plus_lcancel in eq.
            classic_case (0 = c) as [c_z|c_nz].
            *   subst.
                symmetry; apply plus_rid.
            *   contradiction (never_eq c c_nz eq).
        +   apply nat_le_ex in leq as [c]; subst.
            rewrite nat_mult_rdist in eq.
            rewrite <- (plus_rid (y × a)) in eq at 2.
            apply plus_lcancel in eq.
            classic_case (0 = c) as [c_z|c_nz].
            *   subst.
                apply plus_rid.
            *   symmetry in eq.
                contradiction (never_eq c c_nz eq).
Qed.

Theorem group_order_fin : ∀ n : nat, group_order = from_nat n ↔ is_least le K n.
Proof.
    intros n.
    split; [>|apply group_order_fin1].
    intros n_order.
    split; [>split|].
    -   intros contr; subst.
        rewrite homo_zero in n_order.
        symmetry in n_order.
        contradiction (group_order_nz n_order).
    -   classic_case (∃ m, K m) as [m_ex|m_neq].
        +   pose proof (well_ordered _ m_ex) as [m m_least].
            pose proof (group_order_fin1 m m_least) as eq.
            rewrite n_order in eq.
            apply inj in eq.
            subst.
            apply m_least.
        +   assert (∀ m, 0 ≠ m → 0 ≠ m × a) as inf.
            {
                intros m.
                rewrite not_ex in m_neq.
                specialize (m_neq m).
                unfold K in m_neq.
                rewrite not_and_impl in m_neq.
                exact m_neq.
            }
            rewrite <- group_order_inf in inf.
            rewrite n_order in inf.
            apply nat_lt_card in inf.
            contradiction inf.
    -   intros y y_in.
        order_contradiction y_lt.
        pose proof (well_ordered K (ex_intro _ y y_in)) as [m m_least].
        pose proof (group_order_fin1 m m_least) as m_eq.
        rewrite n_order in m_eq.
        apply inj in m_eq.
        subst m.
        pose proof (rand m_least y y_in) as leq.
        contradiction (irrefl _ (lt_le_trans y_lt leq)).
Qed.

End CyclicGroup.
