Require Import init.

Require Export ord_mult.
Require Import set_induction.

Open Scope ord_scope.

Definition ord_pow α :=
    If 0 = α
    then λ β, If 0 = β then 1 else 0
    else make_ord_normal 1 (λ _ β, β * α).
Infix "^" := ord_pow : ord_scope.

Theorem zero_ord_pow : ∀ α : ord, 0 ≠ α → 0 ^ α = 0.
Proof.
    intros α α_nz.
    unfold ord_pow.
    rewrite (if_true Logic.eq_refl).
    rewrite (if_false α_nz).
    reflexivity.
Qed.

Theorem ord_pow_zero : ∀ α : ord, α ^ 0 = 1.
Proof.
    intros α.
    unfold ord_pow.
    case_if [α_z|α_nz].
    -   rewrite (if_true Logic.eq_refl).
        reflexivity.
    -   apply make_ord_normal_zero.
Qed.

Theorem ord_pow_suc : ∀ α β : ord, α ^ ord_suc β = α ^ β * α.
Proof.
    intros α β.
    unfold ord_pow.
    case_if [α_z|α_nz].
    -   subst α.
        rewrite mult_ranni.
        case_if [β_z|β_nz].
        +   contradiction (ord_zero_suc _ β_z).
        +   reflexivity.
    -   apply make_ord_normal_suc.
Qed.

Theorem ord_pow_lim : ∀ α β, 0 ≠ α → lim_ord β →
    α ^ β = ord_f_sup β (λ δ, α ^ [δ|]).
Proof.
    intros α β α_nz β_lim.
    unfold ord_pow.
    rewrite (if_false α_nz).
    apply make_ord_normal_lim.
    exact β_lim.
Qed.

Theorem ord_pow_nz : ∀ α β, 0 ≠ α → 0 ≠ α ^ β.
Proof.
    intros α β α_nz.
    induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
    -   rewrite ord_pow_zero.
        apply ord_not_trivial.
    -   rewrite ord_pow_suc.
        apply mult_nz; assumption.
    -   rewrite (ord_pow_lim _ β α_nz β_lim).
        pose proof (ord_f_sup_ge β (λ δ, α ^ [δ|]) [0|all_pos2 (land β_lim)])
            as leq; cbn in leq.
        rewrite ord_pow_zero in leq.
        rewrite <- ord_suc_zero_one in leq.
        rewrite ord_le_suc_lt in leq.
        apply leq.
Qed.

Theorem ord_gt_one : ∀ α, 0 ≠ α → 1 ≠ α → 1 < α.
Proof.
    intros α α_nz α_none.
    order_contradiction leq.
    apply all_pos2 in α_nz.
    rewrite <- ord_le_suc_lt in α_nz.
    rewrite ord_suc_zero_one in α_nz.
    pose proof (antisym α_nz leq).
    contradiction.
Qed.

Theorem ord_pow_normal : ∀ α, 0 ≠ α → OrdNormal (ord_pow α).
Proof.
    intros α α_nz.
    unfold ord_pow.
    rewrite (if_false α_nz).
    apply make_ord_normal_lim.
Qed.

Lemma ord_pow_le_suc : ∀ α β, 0 ≠ α → α ^ β ≤ α ^ ord_suc β.
Proof.
    intros α β α_nz.
    unfold ord_pow.
    rewrite (if_false α_nz).
    rewrite make_ord_normal_suc.
    apply ord_le_self_rmult.
    exact α_nz.
Qed.

Lemma ord_pow_lt_suc : ∀ α β, 1 < α → α ^ β < α ^ ord_suc β.
Proof.
    intros α β α_gt.
    assert (0 ≠ α) as α_nz.
    {
        apply (trans ord_one_pos) in α_gt.
        apply α_gt.
    }
    unfold ord_pow.
    rewrite (if_false α_nz).
    rewrite make_ord_normal_suc.
    pose (αβ := make_ord_normal 1 (λ _ β0, β0 * α) β).
    fold αβ.
    apply (lt_lmult αβ) in α_gt.
    -   rewrite mult_rid in α_gt.
        exact α_gt.
    -   pose proof (ord_pow_nz α β α_nz) as neq.
        unfold ord_pow in neq.
        rewrite (if_false α_nz) in neq.
        exact neq.
Qed.

Theorem ord_pow_homo_le : ∀ α, 0 ≠ α → HomomorphismLe (ord_pow α).
Proof.
    intros α α_nz.
    unfold ord_pow.
    rewrite (if_false α_nz).
    apply make_ord_normal_le.
    intros β.
    pose proof (ord_pow_le_suc α β α_nz) as leq.
    unfold ord_pow in leq.
    rewrite (if_false α_nz) in leq.
    exact leq.
Qed.

Theorem ord_pow_homo_inj : ∀ α, 1 < α → Injective (ord_pow α).
Proof.
    intros α α_gt.
    unfold ord_pow.
    assert (0 ≠ α) as α_nz.
    {
        apply (trans ord_one_pos) in α_gt.
        apply α_gt.
    }
    rewrite (if_false α_nz).
    apply make_ord_normal_inj.
    intros β.
    pose proof (ord_pow_lt_suc α β α_gt) as ltq.
    unfold ord_pow in ltq.
    rewrite (if_false α_nz) in ltq.
    exact ltq.
Qed.

Theorem ord_pow_sup : ∀ α, 0 ≠ α →
    ∀ β (g : set_type (λ α, α < β) → ord), 0 ≠ β →
    α ^ (ord_f_sup β g) = ord_f_sup β (λ δ, α ^ g δ).
Proof.
    intros α α_nz.
    unfold ord_pow.
    rewrite (if_false α_nz).
    apply ord_normal_f_sup.
    -   pose proof (ord_pow_homo_le α α_nz) as pow_le.
        unfold ord_pow in pow_le.
        rewrite (if_false α_nz) in pow_le.
        exact pow_le.
    -   pose proof (ord_pow_normal α α_nz) as normal.
        unfold ord_pow in normal.
        rewrite (if_false α_nz) in normal.
        exact normal.
Qed.

Theorem ord_pow_one : ∀ α : ord, α ^ 1 = α.
Proof.
    intros α.
    rewrite <- ord_suc_zero_one.
    rewrite ord_pow_suc.
    rewrite ord_pow_zero.
    apply mult_lid.
Qed.

Theorem one_ord_pow : ∀ α : ord, 1 ^ α = 1.
Proof.
    intros α.
    induction α as [|α IHα|α α_lim IHα] using ord_induction.
    -   apply ord_pow_zero.
    -   rewrite ord_pow_suc.
        rewrite IHα.
        apply mult_lid.
    -   rewrite (ord_pow_lim _ α ord_not_trivial α_lim).
        apply ord_f_sup_eq.
        +   intros [δ δ_lt]; cbn.
            rewrite IHα by exact δ_lt.
            apply refl.
        +   intros ε ε_ge.
            specialize (ε_ge [0|all_pos2 (land α_lim)]); cbn in ε_ge.
            rewrite ord_pow_zero in ε_ge.
            exact ε_ge.
Qed.

Theorem ord_pow_2 : ∀ α, α ^ 2 = α * α.
Proof.
    intros α.
    rewrite <- ord_suc_zero_one at 2.
    rewrite ord_plus_suc, plus_rid.
    rewrite ord_pow_suc, ord_pow_one.
    reflexivity.
Qed.

Theorem ord_pow_le : ∀ α β γ : ord, 0 ≠ α → β ≤ γ → α ^ β ≤ α ^ γ.
Proof.
    intros α β γ α_nz leq.
    pose proof (ord_pow_homo_le α α_nz).
    apply homo_le.
    exact leq.
Qed.

Theorem ord_pow_plus : ∀ α β γ : ord, α ^ (β + γ) = α ^ β * α ^ γ.
Proof.
    intros α β γ.
    induction γ as [|γ IHγ|γ γ_lim IHγ] using ord_induction.
    -   rewrite plus_rid.
        rewrite ord_pow_zero.
        rewrite mult_rid.
        reflexivity.
    -   rewrite ord_plus_suc.
        do 2 rewrite ord_pow_suc.
        rewrite IHγ.
        rewrite mult_assoc.
        reflexivity.
    -   classic_case (0 = α) as [α_z|α_nz].
        {
            subst.
            rewrite (zero_ord_pow γ (land γ_lim)).
            rewrite mult_ranni.
            apply zero_ord_pow.
            apply ord_nz_rplus.
            apply γ_lim.
        }
        rewrite (ord_plus_lim β γ γ_lim).
        rewrite (ord_pow_lim α γ α_nz γ_lim).
        rewrite (ord_pow_sup _ α_nz) by apply γ_lim.
        rewrite ord_mult_sup by apply γ_lim.
        apply ord_f_sup_f_eq.
        intros [δ δ_lt]; cbn.
        exact (IHγ δ δ_lt).
Qed.

Theorem ord_pow_pow : ∀ α β γ : ord, (α ^ β) ^ γ = α ^ (β * γ).
Proof.
    intros α β γ.
    induction γ as [|γ IHγ|γ γ_lim IHγ] using ord_induction.
    -   rewrite mult_ranni.
        do 2 rewrite ord_pow_zero.
        reflexivity.
    -   rewrite ord_pow_suc.
        rewrite ord_mult_suc.
        rewrite ord_pow_plus.
        rewrite IHγ.
        reflexivity.
    -   classic_case (0 = β) as [β_z|β_nz].
        {
            subst β.
            rewrite mult_lanni.
            rewrite ord_pow_zero.
            apply one_ord_pow.
        }
        classic_case (0 = α) as [α_z|α_nz].
        {
            subst α.
            rewrite zero_ord_pow by exact β_nz.
            rewrite zero_ord_pow by apply γ_lim.
            symmetry; apply zero_ord_pow.
            apply mult_nz; [>exact β_nz|apply γ_lim].
        }
        rewrite (ord_pow_lim _ γ (ord_pow_nz α β α_nz) γ_lim).
        rewrite (ord_mult_lim _ γ γ_lim).
        rewrite (ord_pow_sup _ α_nz) by apply γ_lim.
        apply ord_f_sup_f_eq.
        intros [δ δ_lt]; cbn.
        exact (IHγ δ δ_lt).
Qed.

Theorem ord_pow_lt : ∀ α β γ : ord, 1 < α → β < γ → α ^ β < α ^ γ.
Proof.
    intros α β γ α_gt ltq.
    assert (0 ≠ α) as α_nz.
    {
        apply (trans ord_one_pos) in α_gt.
        apply α_gt.
    }
    pose proof (ord_pow_homo_le α α_nz).
    pose proof (ord_pow_homo_inj α α_gt).
    apply homo_lt.
    exact ltq.
Qed.

Theorem ord_pow_lcancel : ∀ α β γ : ord, 1 < α → α ^ β = α ^ γ → β = γ.
Proof.
    intros α β γ α_gt eq.
    pose proof (ord_pow_homo_inj α α_gt).
    apply inj in eq.
    exact eq.
Qed.

Theorem ord_le_rpow : ∀ α β γ : ord, α ≤ β → α ^ γ ≤ β ^ γ.
Proof.
    intros α β γ leq.
    induction γ as [|γ IHγ|γ γ_lim IHγ] using ord_induction.
    -   do 2 rewrite ord_pow_zero.
        apply refl.
    -   do 2 rewrite ord_pow_suc.
        apply le_lrmult; assumption.
    -   classic_case (0 = α) as [α_z|α_nz].
        {
            subst.
            rewrite zero_ord_pow by apply γ_lim.
            apply all_pos.
        }
        classic_case (0 = β) as [β_z|β_nz].
        {
            subst.
            apply all_neg_eq in leq; subst.
            apply refl.
        }
        rewrite (ord_pow_lim α γ α_nz γ_lim).
        rewrite (ord_pow_lim β γ β_nz γ_lim).
        apply ord_f_sup_least.
        intros [δ δ_lt]; cbn.
        apply ord_f_sup_other_leq.
        intros ε ε_ge.
        specialize (ε_ge [δ|δ_lt]); cbn in ε_ge.
        specialize (IHγ δ δ_lt).
        exact (trans IHγ ε_ge).
Qed.

Theorem ord_pow_le_pow : ∀ α β, 1 < β → α ≤ β ^ α.
Proof.
    intros α β β_gt.
    apply ord_normal_le.
    -   apply ord_pow_homo_le.
        apply (trans ord_one_pos) in β_gt.
        apply β_gt.
    -   apply ord_pow_homo_inj.
        exact β_gt.
Qed.

Theorem ord_pow_lim_lim : ∀ α β, 1 < α → lim_ord β → lim_ord (α ^ β).
Proof.
    intros α β α_gt β_lim.
    pose proof α_gt as α_nz.
    apply (trans ord_one_pos) in α_nz.
    apply rand in α_nz.
    pose proof (ord_pow_normal α α_nz).
    pose proof (ord_pow_homo_le α α_nz).
    pose proof (ord_pow_homo_inj α α_gt).
    apply (ord_normal_lim_ord (ord_pow α)).
    exact β_lim.
Qed.

Theorem ord_pow_self_le : ∀ α β, 0 ≠ β → α ≤ α ^ β.
Proof.
    intros α β β_nz.
    classic_case (0 = α) as [α_z|α_nz].
    -   subst α.
        rewrite zero_ord_pow by exact β_nz.
        apply refl.
    -   rewrite <- (ord_pow_one α) at 1.
        apply ord_pow_le.
        +   exact α_nz.
        +   rewrite <- ord_suc_zero_one.
            rewrite ord_le_suc_lt.
            apply all_pos2.
            exact β_nz.
Qed.

Close Scope ord_scope.
