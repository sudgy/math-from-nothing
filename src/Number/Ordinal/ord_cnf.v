Require Import init.

Require Export ord_nat.
Require Import set_induction.
Require Export list.

Definition cnf_type := (ord * nat)%type.

Open Scope ord_scope.

Definition cnf_eval (l : list cnf_type)
    := list_sum (list_image (λ x, ω ^ fst x * from_nat (nat_suc (snd x))) l).

Theorem cnf_eval_end : cnf_eval [] = 0.
Proof.
    reflexivity.
Qed.

Theorem cnf_eval_add : ∀ x l,
    cnf_eval (x ꞉ l) = ω ^ fst x * from_nat (nat_suc (snd x)) + cnf_eval l.
Proof.
    intros x l.
    reflexivity.
Qed.

Theorem cnf_eval_single : ∀ x,
    cnf_eval [x] = ω ^ fst x * from_nat (nat_suc (snd x)).
Proof.
    intros x.
    rewrite cnf_eval_add, cnf_eval_end.
    apply plus_rid.
Qed.

Theorem cnf_eval_plus : ∀ l1 l2, cnf_eval (l1 + l2) = cnf_eval l1 + cnf_eval l2.
Proof.
    intros l1 l2.
    induction l1 as [|[α n] l1 IHl1].
    -   rewrite cnf_eval_end.
        rewrite plus_lid, list_conc_lid.
        reflexivity.
    -   rewrite list_conc_add.
        do 2 rewrite cnf_eval_add.
        rewrite IHl1.
        apply plus_assoc.
Qed.

Theorem cnf_lt_omega_le : ∀ α β m n,
    α < β → ω ^ α * from_nat (nat_suc m) * ω ≤ ω ^ β * from_nat (nat_suc n).
Proof.
    intros α β m n ltq.
    rewrite <- mult_assoc.
    rewrite nat_mult_omega by apply nat_zero_suc.
    rewrite <- ord_pow_suc.
    rewrite <- (mult_rid (ω ^ ord_suc α)).
    apply le_lrmult.
    -   apply ord_pow_le.
        +   apply ω_lim.
        +   rewrite ord_le_suc_lt.
            exact ltq.
    -   rewrite nat_ord_suc.
        rewrite <- ord_suc_zero_one.
        apply ord_sucs_le.
        apply all_pos.
Qed.

Theorem ord_plus_omega_eat : ∀ α β m n, α < β →
    ω ^ α * from_nat (nat_suc m) + ω ^ β * from_nat (nat_suc n) =
    ω ^ β * from_nat (nat_suc n).
Proof.
    intros α β m n ltq.
    apply ord_plus_eat.
    apply cnf_lt_omega_le.
    exact ltq.
Qed.

Theorem cnf_plus_base : ∀ (l : list cnf_type) (α : ord),
    cnf_eval l + ω ^ α = cnf_eval (list_filter (λ x, α ≤ fst x) l) + ω ^ α.
Proof.
    intros l α.
    induction l as [|[β m] l IHl] using list_backwards_induction.
    -   rewrite list_filter_end.
        reflexivity.
    -   rewrite cnf_eval_plus.
        rewrite cnf_eval_single; cbn.
        rewrite list_filter_conc.
        classic_case (α ≤ β) as [leq|nleq].
        +   rewrite list_filter_single_in by exact leq.
            rewrite cnf_eval_plus.
            rewrite cnf_eval_single; cbn.
            classic_case (α = β) as [eq|neq].
            *   subst β.
                do 2 rewrite <- plus_assoc.
                rewrite <- ord_mult_suc.
                rewrite from_nat_suc.
                rewrite <- ord_plus_suc.
                rewrite ldist.
                rewrite mult_rid, plus_assoc.
                rewrite IHl.
                symmetry; apply plus_assoc.
            *   rewrite <- (ord_plus_omega_eat α β 0 m (make_and leq neq)).
                change (nat_suc 0) with (1 : nat).
                rewrite homo_one.
                rewrite mult_rid.
                do 2 rewrite plus_assoc.
                rewrite IHl.
                reflexivity.
        +   rewrite list_filter_add_nin by exact nleq.
            rewrite list_filter_end.
            rewrite list_conc_rid.
            rewrite <- IHl.
            rewrite <- plus_assoc.
            apply lplus.
            rewrite nle_lt in nleq.
            rewrite <- (mult_rid (ω ^ α)).
            rewrite <- homo_one.
            change 1 with (nat_suc 0).
            apply ord_plus_omega_eat.
            exact nleq.
Qed.

Theorem cnf_plus : ∀ (l : list cnf_type) (α : ord) (n : nat),
    cnf_eval l + ω ^ α * from_nat (nat_suc n) =
    cnf_eval (list_filter (λ x, α ≤ fst x) l) + ω ^ α * from_nat (nat_suc n).
Proof.
    intros l α n.
    rewrite from_nat_suc.
    rewrite ldist.
    rewrite mult_rid.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply cnf_plus_base.
Qed.

Lemma lt_omega_pow_two : ∀ δ β, δ < ω ^ β → 2 * δ < ω ^ β.
Proof.
    intros δ β δ_lt.
    classic_case (0 = β) as [β_z|β_nz].
    -   subst β.
        rewrite ord_pow_zero in *.
        rewrite <- ord_suc_zero_one in δ_lt.
        rewrite ord_lt_suc_le in δ_lt.
        apply all_neg_eq in δ_lt.
        subst δ.
        rewrite mult_ranni.
        apply ord_one_pos.
    -   pose proof (ord_nz_one_plus β β_nz) as [β' β_eq]; subst β.
        rewrite ord_pow_plus.
        rewrite ord_pow_one.
        rewrite <- (nat_mult_omega 2) at 1 by apply nat_zero_suc.
        rewrite (homo_two from_nat).
        rewrite <- mult_assoc.
        apply lt_lmult.
        +   apply ord_nz_lplus.
            apply ord_not_trivial.
        +   rewrite ord_pow_plus, ord_pow_one in δ_lt.
            exact δ_lt.
Qed.

Lemma cnf_eval_le : ∀ l α, list_prop (λ γ, fst γ < α) l →
    cnf_eval l ≤ ω ^ α * ω.
Proof.
    intros l α l_lt.
    list_prop_induction l l_lt as [γ m] γ_lt IHl.
    -   rewrite cnf_eval_end.
        apply all_pos.
    -   rewrite cnf_eval_add; cbn.
        cbn in γ_lt.
        assert (ω ^ γ * from_nat (nat_suc m) ≤ ω ^ α) as leq.
        {
            apply (cnf_lt_omega_le _ _ m 0) in γ_lt.
            change (nat_suc 0) with (1 : nat) in γ_lt.
            rewrite homo_one, mult_rid in γ_lt.
            apply (trans2 γ_lt).
            apply ord_le_self_rmult.
            apply ω_lim.
        }
        apply (trans (le_lrplus leq IHl)).
        rewrite <- (mult_rid (ω ^ α)) at 1.
        rewrite <- ldist.
        rewrite <- homo_one.
        rewrite nat_plus_omega.
        apply refl.
Qed.

Theorem cnf_mult_omega : ∀ α n l β, 0 ≠ β → list_prop (λ γ, fst γ < α) l →
    cnf_eval ((α, n) ꞉ l) * ω ^ β = ω ^ (α + β).
Proof.
    intros α n l β β_nz l_lt.
    rewrite cnf_eval_add; cbn.
    assert (lim_ord (ω ^ β)) as ωβ_lim.
    {
        apply ord_lim_pow_lim.
        -   exact β_nz.
        -   exact ω_lim.
    }
    induction l as [|[γ m] l IHl] using list_backwards_induction.
    {
        rewrite cnf_eval_end, plus_rid.
        rewrite <- mult_assoc.
        rewrite ord_nat_mult_limit.
        2: apply nat_zero_suc.
        2: exact ωβ_lim.
        symmetry; apply ord_pow_plus.
    }
    apply list_prop_conc in l_lt as [l_lt γ_lt].
    rewrite list_prop_single in γ_lt; cbn in γ_lt.
    specialize (IHl l_lt).
    rewrite cnf_eval_plus.
    rewrite cnf_eval_single; cbn.
    rewrite <- IHl.
    rewrite plus_assoc.
    do 2 rewrite (ord_mult_lim _ _ ωβ_lim).
    apply antisym; apply ord_sup_leq_sup.
    -   intros [δ δ_lt]; cbn.
        pose proof (lt_omega_pow_two δ β δ_lt) as δ2_lt.
        exists [2 * δ|δ2_lt]; cbn.
        rewrite mult_assoc.
        apply le_rmult.
        rewrite ldist, mult_rid.
        apply le_lplus.
        apply (trans2 (ord_le_self_rplus _ _)).
        apply (trans2 (cnf_lt_omega_le _ _ m n γ_lt)).
        apply ord_le_self_rmult.
        apply ω_nz.
    -   intros [δ δ_lt]; cbn.
        exists [δ|δ_lt]; cbn.
        apply le_rmult.
        apply ord_le_self_rplus.
Qed.

Theorem cnf_mult_nat : ∀ α n l m, list_prop (λ γ, fst γ < α) l →
    cnf_eval ((α, n) ꞉ l) * from_nat (nat_suc m) =
    cnf_eval ((α, n * nat_suc m + m) ꞉ l).
Proof.
    intros α n l m l_lt.
    nat_induction m.
    -   rewrite homo_one.
        do 2 rewrite mult_rid.
        rewrite plus_rid.
        reflexivity.
    -   rewrite from_nat_suc.
        rewrite ldist.
        rewrite IHm.
        rewrite mult_rid.
        do 3 rewrite cnf_eval_add; cbn.
        rewrite plus_assoc.
        apply rplus.
        rewrite <- plus_assoc.
        rewrite cnf_plus.
        pose proof (list_prop_filter_empty l (λ x, α ≤ fst x)) as l_eq.
        assert ((λ x, ¬α ≤ fst x) = (λ x : cnf_type, fst x < α)) as S_eq.
        {
            functional_intros x.
            rewrite nle_lt.
            reflexivity.
        }
        cbn in l_eq.
        rewrite S_eq in l_eq.
        specialize (l_eq l_lt).
        rewrite l_eq.
        rewrite cnf_eval_end, plus_lid.
        rewrite <- ldist.
        apply lmult.
        rewrite <- homo_plus.
        apply f_equal.
        rewrite nat_plus_lsuc.
        do 3 rewrite nat_mult_rsuc.
        rewrite <- (nat_plus_rsuc (n + n * m)).
        rewrite plus_assoc.
        reflexivity.
Qed.

Theorem cnf_pow_omega : ∀ α n l β, 0 ≠ α → 0 ≠ β →
    list_prop (λ γ, fst γ < α) l →
    cnf_eval ((α, n) ꞉ l) ^ (ω ^ β) = ω ^ (α * ω ^ β).
Proof.
    intros α n l β α_nz β_nz l_lt.
    rewrite cnf_eval_add; cbn.

    rewrite <- ord_pow_pow.
    apply antisym.
    -   assert (ω ^ α * from_nat (nat_suc n) + cnf_eval l ≤
            (ω ^ α * from_nat (nat_suc n))^2) as leq.
        {
            rewrite ord_pow_2.
            assert (ω ^ α * from_nat (nat_suc n)
                = 1 + ω ^ α * from_nat (nat_suc n)) as eq.
            {
                symmetry; apply ord_plus_eat.
                rewrite mult_lid.
                rewrite from_nat_suc.
                rewrite ldist, mult_rid.
                apply (trans2 (ord_le_self_rplus _ _)).
                rewrite <- (ord_pow_one ω) at 1.
                pose proof (ord_pow_homo_le ω (land ω_lim)).
                apply homo_le.
                rewrite <- ord_suc_zero_one.
                rewrite ord_le_suc_lt.
                apply all_pos2.
                exact α_nz.
            }
            rewrite eq at 3; clear eq.
            rewrite ldist, mult_rid.
            apply le_lplus.
            rewrite <- mult_assoc.
            pose proof (cnf_eval_le _ _ l_lt) as leq.
            apply (trans leq).
            apply le_lmult.
            apply ord_lim_omega.
            apply ord_mult_lim_lim.
            1: rewrite nat_ord_suc; apply ord_zero_suc.
            apply ord_lim_mult_lim.
            1: rewrite nat_ord_suc; apply ord_zero_suc.
            apply ord_lim_pow_lim.
            -   exact α_nz.
            -   exact ω_lim.
        }
        apply (ord_le_rpow _ _ (ω ^ β)) in leq.
        apply (trans leq); clear leq.
        rewrite ord_pow_2.
        rewrite mult_assoc.
        rewrite <- (mult_assoc (ω ^ α)).
        rewrite nat_mult_omega_pow by exact α_nz.
        rewrite <- ord_pow_2.
        assert (from_nat (nat_suc n) ≤ ω ^ α) as leq.
        {
            apply (lt_le_trans (nat_lt_ω _)).
            apply ord_pow_self_le.
            exact α_nz.
        }
        apply (le_lmult ((ω ^ α) ^2)) in leq.
        apply (ord_le_rpow _ _ (ω ^ β)) in leq.
        apply (trans leq).
        rewrite <- ord_pow_suc.
        rewrite ord_suc_plus_one.
        rewrite <- plus_assoc.
        do 3 rewrite ord_pow_pow.
        rewrite <- (homo_three from_nat).
        rewrite nat_mult_omega_pow by exact β_nz.
        apply refl.
    -   apply ord_le_rpow.
        apply (trans2 (ord_le_self_rplus _ _)).
        apply ord_le_self_rmult.
        rewrite nat_ord_suc.
        apply ord_zero_suc.
Qed.

Close Scope ord_scope.
