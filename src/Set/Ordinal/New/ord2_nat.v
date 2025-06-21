Require Import init.

Require Export ord2_pow.
Require Import set_induction.
Require Import ord2_bounds.
Require Export card2_large.

Require Export nat.

Open Scope ord_scope.

Definition nat_ord_type : ord_type := make_ord_type nat _ _ _.

Theorem nat_to_ord_lt : ∀ a b : nat_ord_type, a < b →
    to_ord (sub_ord_type (initial_segment a)) <
    to_ord (sub_ord_type (initial_segment b)).
Proof.
    intros a b ltq.
    apply ord_lt_simpl.
    unfold initial_segment.
    exists [a|ltq].
    split.
    pose (f (x : set_type (λ m, m < a))
        := [[x|] | trans [|x] ltq] : set_type (λ m, m < b)).
    assert (∀ x, f x < [a|ltq]) as f_in.
    {
        intros [x x_lt]; cbn.
        unfold f; cbn.
        apply set_type_lt.
        exact x_lt.
    }
    exists (λ x, [f x|f_in x]).
    1: split.
    all: split.
    -   intros m n eq.
        unfold f in eq.
        apply set_type_eq in eq; cbn in eq.
        apply set_type_eq in eq; cbn in eq.
        apply set_type_eq; exact eq.
    -   intros [[y y_lt1] y_lt2].
        unfold initial_segment in y_lt2.
        assert (y < a) as y_lt3 by (apply set_type_lt in y_lt2; exact y_lt2).
        exists [y|y_lt3].
        unfold f; cbn.
        apply set_type_eq; cbn.
        apply set_type_eq; reflexivity.
    -   intros m n leq.
        exact leq.
Qed.

Theorem from_nat_ord : ∀ n : nat,
    from_nat n = to_ord (sub_ord_type (initial_segment (n : nat_ord_type))).
Proof.
    nat_induction n.
    {
        rewrite homo_zero.
        apply ord_false_0.
        intros [a a_z].
        contradiction (nat_neg2 a_z).
    }
    change (nat_suc n) with (1 + n) at 1.
    rewrite plus_comm.
    rewrite homo_plus.
    rewrite IHn; clear IHn.
    rewrite homo_one.
    rewrite ord_plus_lsub by exact not_trivial.
    apply ord_lsub_eq.
    -   intros [α α_lt]; cbn.
        apply ord_lt_one_eq in α_lt.
        subst.
        rewrite plus_rid.
        apply nat_to_ord_lt.
        apply nat_lt_suc.
    -   intros ε ε_ge.
        specialize (ε_ge [0|ord_one_pos]); cbn in ε_ge.
        rewrite plus_rid in ε_ge.
        equiv_get_value ε.
        rewrite ord_lt_simpl in ε_ge.
        apply ord_le_simpl.
        destruct ε_ge as [x [f]].
        exists (λ m, IfH [m|] < n
            then λ H, [f [[m|] | H]|]
            else λ _, x).
        split; split; cbn.
        +   intros [a a_lt] [b b_lt]; cbn.
            classic_case (a < n) as [an|an]; classic_case (b < n) as [bn|bn].
            pose proof (ord_iso_bij _ _ f).
            all: intros eq.
            *   apply set_type_eq in eq.
                apply set_type_eq2.
                apply inj in eq.
                apply set_type_eq in eq; cbn in eq.
                exact eq.
            *   pose proof [|f[a|an]] as ltq.
                rewrite eq in ltq.
                unfold initial_segment in ltq.
                contradiction (irrefl _ ltq).
            *   pose proof [|f[b|bn]] as ltq.
                rewrite <- eq in ltq.
                unfold initial_segment in ltq.
                contradiction (irrefl _ ltq).
            *   rewrite nlt_le in an, bn.
                unfold initial_segment in a_lt, b_lt.
                apply set_type_eq2.
                rewrite nat_lt_suc_le in a_lt.
                rewrite nat_lt_suc_le in b_lt.
                rewrite (antisym a_lt an).
                rewrite (antisym b_lt bn).
                reflexivity.
        +   intros [a a_lt] [b b_lt] leq; cbn.
            unfold le in leq; cbn in leq.
            classic_case (a < n) as [an|an]; classic_case (b < n) as [bn|bn].
            *   change ([f[a|an]|] ≤ [f[b|bn]|]) with (f[a|an] ≤ f[b|bn]).
                apply homo_le.
                exact leq.
            *   apply [|f [a|an]].
            *   rewrite nlt_le in an.
                exfalso.
                unfold initial_segment in *.
                rewrite nat_lt_suc_le in a_lt.
                rewrite nat_lt_suc_le in b_lt.
                rewrite (antisym a_lt an) in leq.
                rewrite (antisym b_lt leq) in bn.
                contradiction (irrefl _ bn).
            *   apply refl.
Qed.

Global Instance ord_char_zero : CharacteristicZero ord.
Proof.
    split.
    intros n.
    rewrite from_nat_ord.
    intros contr.
    symmetry in contr.
    unfold zero in contr; equiv_simpl in contr.
    destruct contr as [f].
    contradiction (empty_false (f [n | nat_lt_suc n])).
Qed.

Global Instance from_nat_ord_le : HomomorphismLe (from_nat (U := ord)).
Proof.
    split.
    intros a b leq.
    do 2 rewrite from_nat_ord.
    classic_case (a = b) as [eq|neq].
    -   subst; apply refl.
    -   apply (nat_to_ord_lt _ _ (make_and leq neq)).
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

Theorem nat_plus_omega : ∀ n : nat, from_nat n + ω = ω.
Proof.
    intros n.
    apply antisym.
    2: apply ord_le_self_lplus.
    rewrite ord_plus_lsub by exact ω_nz.
    apply ord_lsub_least.
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
    rewrite ord_mult_lub.
    apply ord_lub_least.
    intros [α α_lt]; cbn.
    apply ord_lt_ω in α_lt as [m eq]; subst.
    rewrite <- homo_mult.
    rewrite <- homo_plus.
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
    rewrite ord_pow_lub by exact ω_nz.
    apply ord_lub_least.
    intros [α α_lt]; cbn.
    apply ord_lt_ω in α_lt as [m eq]; subst.
    rewrite <- from_nat_ord_pow.
    rewrite <- homo_mult.
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

Close Scope ord_scope.
