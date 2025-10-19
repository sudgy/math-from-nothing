Require Import init.

Require Export ord_pow.
Require Import set_induction.
Require Export card_large.

Require Export nat.

Open Scope ord_scope.

Definition nat_ord_type : ord_type := make_ord_type nat _ _ _.

Theorem nat_ord_suc : ∀ n, from_nat (nat_suc n) = ord_suc (from_nat n).
Proof.
    intros n.
    change (nat_suc n) with (1 + n).
    rewrite plus_comm.
    rewrite homo_plus.
    rewrite homo_one.
    symmetry; apply ord_suc_plus_one.
Qed.

Theorem from_nat_ord : ∀ n : nat,
    from_nat n = to_ord (sub_ord_type (initial_segment (n : nat_ord_type))).
Proof.
    nat_induction n.
    {
        rewrite homo_zero.
        apply ord_false_0.
        intros [a a_z].
        contradiction (not_neg a_z).
    }
    change (nat_suc n) with (1 + n) at 1.
    rewrite plus_comm.
    rewrite homo_plus.
    rewrite IHn; clear IHn.
    rewrite homo_one.
    rewrite <- ord_suc_plus_one.
    rewrite ord_suc_type.
    equiv_simpl.
    split.
    exists (λ x, match x with
        | inl m => [[m|] | trans ([|m] : [m|] < n) (nat_lt_suc n)]
        | inr _ => [n | nat_lt_suc n]
        end).
    1: split.
    all: split.
    -   intros [a|s1] [b|s2] eq.
        +   apply set_type_eq in eq; cbn in eq.
            apply set_type_eq in eq.
            rewrite eq; reflexivity.
        +   apply set_type_eq in eq; cbn in eq.
            pose proof [|a] as ltq.
            unfold initial_segment in ltq.
            rewrite eq in ltq.
            contradiction (irrefl _ ltq).
        +   apply set_type_eq in eq; cbn in eq.
            pose proof [|b] as ltq.
            unfold initial_segment in ltq.
            rewrite eq in ltq.
            contradiction (irrefl _ ltq).
        +   apply f_equal.
            apply singleton_type_eq.
    -   intros [y y_lt].
        unfold initial_segment in *.
        classic_case (y = n) as [eq|neq].
        +   subst y.
            exists (inr Single).
            apply set_type_eq; reflexivity.
        +   pose proof y_lt as y_le.
            rewrite nat_lt_suc_le in y_le.
            exists (inl [y|make_and y_le neq]).
            apply set_type_eq; reflexivity.
    -   intros [a|s1] [b|s2] leq.
        +   unfold le in leq; cbn in leq.
            unfold le; cbn.
            exact leq.
        +   unfold le; cbn.
            apply [|a].
        +   unfold le in leq; cbn in leq.
            contradiction.
        +   apply refl.
Qed.

Global Instance ord_char_zero : CharacteristicZero ord.
Proof.
    split.
    intros n.
    rewrite nat_ord_suc.
    apply ord_zero_suc.
Qed.

Global Instance from_nat_ord_le : HomomorphismLe (from_nat (U := ord)).
Proof.
    split.
    intros a b leq.
    apply nat_le_ex in leq as [c b_eq]; subst b.
    rewrite homo_plus.
    rewrite <- le_plus_0_a_b_ba.
    apply all_pos.
Qed.

Theorem from_nat_ord_pow : ∀ a b, from_nat (a ^ b) = from_nat a ^ from_nat b.
Proof.
    intros a b.
    nat_induction b.
    -   rewrite nat_pow_zero.
        rewrite homo_zero.
        rewrite ord_pow_zero.
        apply homo_one.
    -   rewrite nat_pow_suc.
        change (nat_suc b) with (1 + b).
        rewrite plus_comm.
        rewrite homo_plus.
        rewrite ord_pow_plus.
        rewrite homo_one.
        rewrite ord_pow_one.
        rewrite (homo_mult _ a).
        rewrite IHb.
        reflexivity.
Qed.

Definition ω := to_ord nat_ord_type.

Theorem nat_lt_ω : ∀ n : nat, from_nat n < ω.
Proof.
    intros n.
    rewrite from_nat_ord.
    unfold ω.
    rewrite ord_lt_simpl.
    exists n.
    apply refl.
Qed.

Theorem ord_lt_ω : ∀ α : ord, α < ω → ∃ n, α = from_nat n.
Proof.
    intros A A_lt.
    equiv_get_value A.
    unfold ω in A_lt.
    rewrite ord_lt_simpl in A_lt.
    destruct A_lt as [n [n_eq]].
    exists n.
    rewrite from_nat_ord.
    equiv_simpl.
    split.
    exact n_eq.
Qed.

Theorem ω_nz : 0 ≠ ω.
Proof.
    pose proof (nat_lt_ω 0) as ltq.
    rewrite homo_zero in ltq.
    apply ltq.
Qed.

Theorem ω_lim : lim_ord ω.
Proof.
    split; [>exact ω_nz|].
    intros [n n_eq].
    pose proof (ord_lt_suc n) as n_lt.
    rewrite <- n_eq in n_lt.
    apply ord_lt_ω in n_lt as [m m_eq]; subst n.
    rewrite <- nat_ord_suc in n_eq.
    symmetry in n_eq.
    apply nat_lt_ω in n_eq.
    exact n_eq.
Qed.

Theorem nat_plus_omega : ∀ n : nat, from_nat n + ω = ω.
Proof.
    intros n.
    apply antisym.
    2: apply ord_le_self_lplus.
    rewrite ord_plus_lim by exact ω_lim.
    apply ord_sup_least.
    intros [α α_lt]; cbn.
    apply ord_lt_ω in α_lt as [m eq]; subst.
    rewrite <- homo_plus.
    apply nat_lt_ω.
Qed.

Theorem nat_mult_omega : ∀ n : nat, 0 ≠ n → from_nat n * ω = ω.
Proof.
    intros n n_nz.
    apply antisym.
    2: {
        apply ord_le_self_lmult.
        apply (inj_zero from_nat).
        exact n_nz.
    }
    rewrite ord_mult_lim by exact ω_lim.
    apply ord_sup_least.
    intros [α α_lt]; cbn.
    apply ord_lt_ω in α_lt as [m eq]; subst.
    rewrite <- homo_mult.
    apply nat_lt_ω.
Qed.

Theorem nat_pow_omega : ∀ n : nat, 1 < n → from_nat n ^ ω = ω.
Proof.
    intros n n_gt.
    apply antisym.
    2: {
        apply ord_pow_le_pow.
        rewrite <- homo_one.
        apply (homo_lt2 (f := from_nat)).
        exact n_gt.
    }
    rewrite ord_pow_lim; [>| |exact ω_lim].
    2: {
        apply (trans nat_one_pos) in n_gt.
        destruct n_gt as [n_ge n_nz].
        apply (inj_zero from_nat).
        exact n_nz.
    }
    apply ord_sup_least.
    intros [α α_lt]; cbn.
    apply ord_lt_ω in α_lt as [m eq]; subst.
    rewrite <- from_nat_ord_pow.
    apply nat_lt_ω.
Qed.

Definition aleph (α : ord) := aleph' (ω + α).

Theorem aleph_aleph' : ∀ α, ω*ω ≤ α → aleph α = aleph' α.
Proof.
    intros α α_le.
    unfold aleph.
    apply ord_le_ex in α_le as [γ eq]; subst.
    rewrite plus_assoc.
    rewrite <- (mult_rid ω) at 1.
    rewrite <- ldist.
    rewrite <- (homo_one (f := from_nat)).
    rewrite nat_plus_omega.
    reflexivity.
Qed.

Global Instance aleph_inj : Injective aleph.
Proof.
    split.
    intros a b eq.
    unfold aleph in eq.
    apply inj in eq.
    apply plus_lcancel in eq.
    exact eq.
Qed.

Global Instance aleph_le : HomomorphismLe aleph.
Proof.
    split.
    intros a b leq.
    unfold aleph.
    apply homo_le.
    apply le_lplus.
    exact leq.
Qed.

Theorem aleph_sur : ∀ μ : card, aleph 0 ≤ μ → ∃ α, aleph α = μ.
Proof.
    intros μ μ_ge.
    unfold aleph in *.
    pose proof (sur aleph' μ) as [β β_eq]; subst.
    apply homo_le2 in μ_ge.
    rewrite plus_rid in μ_ge.
    apply ord_le_ex in μ_ge as [α eq]; subst.
    exists α.
    reflexivity.
Qed.

Theorem aleph_least : ∀ α μ, 0 ≠ α → (∀ β, β < α → aleph β < μ) → aleph α ≤ μ.
Proof.
    intros α μ α_nz μ_gt.
    apply aleph'_least.
    intros β β_lt.
    classic_case (β < ω) as [β_lt'|β_ge].
    -   apply ord_lt_ω in β_lt' as [n n_eq]; subst β.
        specialize (μ_gt 0 (all_pos2 α_nz)).
        unfold aleph in μ_gt.
        rewrite plus_rid in μ_gt.
        apply (le_lt_trans2 μ_gt).
        apply homo_le.
        apply nat_lt_ω.
    -   rewrite nlt_le in β_ge.
        apply ord_le_ex in β_ge as [γ eq]; subst β.
        apply lt_plus_lcancel in β_lt.
        apply μ_gt.
        exact β_lt.
Qed.

Theorem ord_normal_fixed : ∀ f, ord_normal f → ∀ α, ∃ β, α ≤ β ∧ f β = β.
Proof.
    intros f f_norm α.
    pose proof f_norm as [f_inj [f_le f_lim]].
    pose (a n := iterate_func f n α).
    pose (β := ord_sup ω (λ n, a (ex_val (ord_lt_ω _ [|n])))).
    exists β.
    split.
    -   unfold β.
        pose (z := [0|nat_lt_ω 0] : set_type (λ α, α < ω)).
        apply (trans2 (ord_sup_ge ω _ z)).
        rewrite_ex_val n n_eq.
        cbn in n_eq.
        rewrite <- homo_zero in n_eq.
        apply inj in n_eq.
        subst n.
        apply refl.
    -   unfold β.
        rewrite (ord_normal_sup f f_norm ω).
        2: {
            rewrite <- homo_zero.
            apply nat_lt_ω.
        }
        apply antisym.
        +   apply ord_sup_least.
            intros [n n_lt].
            pose proof n_lt as n_lt'.
            apply ord_lt_ω in n_lt' as [m n_eq].
            cbn.
            apply ord_sup_other_leq.
            intros ε ε_ge.
            rewrite_ex_val n1 n1_eq.
            specialize (ε_ge [from_nat (nat_suc n1)|nat_lt_ω (nat_suc n1)]).
            rewrite_ex_val n2 n2_eq; cbn in *.
            apply inj in n2_eq.
            subst n2.
            rewrite n_eq in n1_eq.
            apply inj in n1_eq.
            subst n1.
            exact ε_ge.
        +   apply ord_sup_least.
            intros [n n_lt]; cbn.
            apply ord_sup_other_leq.
            intros ε ε_ge.
            rewrite_ex_val n1 n1_eq.
            apply (trans2 (ε_ge [from_nat n1|nat_lt_ω n1])).
            rewrite_ex_val n2 n2_eq; cbn in *.
            apply inj in n2_eq; subst n2.
            apply (ord_normal_le f f_norm).
Qed.


Theorem ord_plus_comm_false : ¬PlusComm ord.
Proof.
    intros contr.
    pose proof (plus_comm (from_nat 1) ω) as eq.
    rewrite nat_plus_omega in eq.
    rewrite <- (plus_rid ω) in eq at 1.
    apply plus_lcancel in eq.
    rewrite <- (homo_zero (f := from_nat)) in eq.
    apply inj in eq.
    contradiction (nat_zero_suc eq).
Qed.

Theorem ord_mult_comm_false : ¬MultComm ord.
Proof.
    intros contr.
    pose proof (mult_comm (from_nat 2) ω) as eq.
    rewrite nat_mult_omega in eq by apply nat_zero_suc.
    rewrite <- (mult_rid ω) in eq at 1.
    apply (mult_lcancel _ ω_nz) in eq.
    rewrite <- (homo_one (f := from_nat)) in eq.
    apply inj in eq.
    contradiction (nat_neq_suc _ eq).
Qed.

Theorem ord_rdist_false : ¬Rdist ord.
Proof.
    intros contr.
    pose proof (rdist (from_nat 1) (from_nat 1) ω) as eq.
    rewrite <- homo_plus in eq.
    rewrite nat_mult_omega in eq by apply nat_zero_suc.
    rewrite nat_mult_omega in eq by apply nat_zero_suc.
    rewrite <- (plus_rid ω) in eq at 1.
    apply plus_lcancel in eq.
    exact (ω_nz eq).
Qed.

Theorem ord_plus_rcancel_false : ¬PlusRcancel ord.
Proof.
    intros contr.
    pose proof (plus_rcancel (a := from_nat 0) (b := from_nat 1) ω) as eq.
    prove_parts eq.
    {
        do 2 rewrite nat_plus_omega.
        reflexivity.
    }
    apply inj in eq.
    contradiction (nat_zero_suc eq).
Qed.

Theorem ord_mult_rcancel_false : ¬MultRcancel ord.
Proof.
    intros contr.
    pose proof (mult_rcancel (a := from_nat 1) (b := from_nat 2) ω ω_nz) as eq.
    prove_parts eq.
    {
        do 2 rewrite nat_mult_omega by apply nat_zero_suc.
        reflexivity.
    }
    apply inj in eq.
    inversion eq.
Qed.

Theorem ord_le_rplus2_false : ¬OrderRplus2 ord.
Proof.
    intros contr.
    pose proof (lt_rplus (a := from_nat 0) (b := from_nat 1) ω) as ltq.
    prove_parts ltq.
    {
        apply homo_lt.
        apply nat_one_pos.
    }
    do 2 rewrite nat_plus_omega in ltq.
    contradiction (irrefl _ ltq).
Qed.

Theorem ord_le_plus_rcancel_false : ¬OrderPlusRcancel ord.
Proof.
    intros contr.
    pose proof (le_plus_rcancel (a := from_nat 1) (b := from_nat 0) ω) as leq.
    prove_parts leq.
    {
        do 2 rewrite nat_plus_omega.
        apply refl.
    }
    apply homo_le2 in leq.
    rewrite <- nlt_le in leq.
    apply leq.
    exact nat_one_pos.
Qed.

Theorem ord_le_rmult2_false : ¬OrderRmult2 ord.
Proof.
    intros contr.
    pose proof (lt_rmult (a := from_nat 1) (b := from_nat 2) ω ω_nz) as ltq.
    prove_parts ltq.
    {
        apply homo_lt.
        apply lt_plus_0_a_b_ab.
        apply nat_one_pos.
    }
    do 2 rewrite nat_mult_omega in ltq by apply nat_zero_suc.
    contradiction (irrefl _ ltq).
Qed.

Theorem ord_le_mult_rcancel_false : ¬OrderMultRcancel ord.
Proof.
    intros contr.
    pose proof (le_mult_rcancel (a:=from_nat 2) (b:=from_nat 1) ω ω_nz) as leq.
    prove_parts leq.
    {
        do 2 rewrite nat_mult_omega by apply nat_zero_suc.
        apply refl.
    }
    apply homo_le2 in leq.
    rewrite <- nlt_le in leq.
    apply leq.
    apply nat_sucs_lt.
    exact nat_one_pos.
Qed.

Close Scope ord_scope.
