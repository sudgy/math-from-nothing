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
        rewrite list_filter_conc, cnf_eval_plus.
        classic_case (α ≤ β) as [leq|nleq].
        +   rewrite list_filter_single_in by exact leq.
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
            rewrite cnf_eval_end, plus_rid.
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

Lemma cnf_eval_le1 : ∀ l α, list_prop (λ γ, fst γ < α) l →
    ∃ N, cnf_eval l ≤ ω ^ α * from_nat (nat_suc N).
Proof.
    intros l α l_lt.
    list_prop_induction l l_lt as [β n] β_lt IHl.
    -   exists 0.
        rewrite cnf_eval_end.
        apply all_pos.
    -   cbn in β_lt.
        destruct IHl as [N leq].
        exists (nat_suc n + N).
        rewrite cnf_eval_add; cbn.
        apply (le_lplus ((ω ^ β) * from_nat (nat_suc n))) in leq.
        apply (trans leq).
        rewrite <- nat_plus_rsuc.
        rewrite (homo_plus (f := from_nat)).
        rewrite ldist.
        apply le_rplus.
        apply le_rmult.
        apply ord_pow_le.
        +   apply ω_lim.
        +   apply β_lt.
Qed.

Lemma cnf_eval_le2 : ∀ l α, list_prop (λ γ, fst γ < α) l →
    cnf_eval l ≤ ω ^ α * ω.
Proof.
    intros l α l_lt.
    apply cnf_eval_le1 in l_lt as [N leq].
    apply (trans leq).
    apply le_lmult.
    apply nat_lt_ω.
Qed.

Theorem cnf_mult_omega : ∀ α n l β, 0 ≠ β → list_prop (λ γ, fst γ < α) l →
    cnf_eval ((α, n) ꞉ l) * ω ^ β = ω ^ (α + β).
Proof.
    intros α n l β β_nz l_lt.
    apply antisym.
    -   rewrite ord_pow_plus.
        apply cnf_eval_le1 in l_lt as [N N_geq].
        apply (le_lplus (ω ^ α * from_nat (nat_suc n))) in N_geq.
        rewrite <- ldist in N_geq.
        rewrite <- homo_plus in N_geq.
        rewrite nat_plus_lsuc in N_geq.
        apply (le_rmult (ω ^ β)) in N_geq.
        rewrite <- mult_assoc in N_geq.
        rewrite nat_mult_omega_pow in N_geq by exact β_nz.
        exact N_geq.
    -   rewrite cnf_eval_add; cbn.
        rewrite ord_pow_plus.
        apply le_rmult.
        apply (trans2 (ord_le_self_rplus _ _)).
        apply ord_le_self_rmult.
        rewrite nat_ord_suc.
        apply ord_zero_suc.
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
    -   pose proof (cnf_eval_le2 l _ l_lt) as leq.
        apply (le_lplus (ω ^ α * from_nat (nat_suc n))) in leq.
        apply (ord_le_rpow _ _ (ω ^ β)) in leq.
        apply (trans leq).
        rewrite <- ldist.
        rewrite nat_plus_omega.
        rewrite <- ord_pow_suc.
        do 2 rewrite ord_pow_pow.
        rewrite ord_suc_plus_one.
        rewrite <- homo_one.
        rewrite (ord_plus_nat_mult_lim _ _ _ α_nz).
        2: apply (ord_lim_pow_lim _ _ β_nz ω_lim).
        apply refl.
    -   apply ord_le_rpow.
        apply (trans2 (ord_le_self_rplus _ _)).
        apply ord_le_self_rmult.
        rewrite nat_ord_suc.
        apply ord_zero_suc.
Qed.

Close Scope ord_scope.
