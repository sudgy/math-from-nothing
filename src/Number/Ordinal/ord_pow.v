Require Import init.

Require Export ord_mult.
Require Import set_induction.
Require Import ord_bounds.

Open Scope ord_scope.

Module OrdPowDef.
Section OrdPowDef.

Context (α : ord).

Definition f (β : ord) (g : set_type (λ x, x < β) → ord) :=
    If 0 = β then 1 else (ord_lub β (λ x, g x * α)).

Definition g := ex_val (transfinite_recursion _ f).
Lemma g_eq : ∀ β : ord, g β = f β (λ δ : set_type (λ δ, δ < β), g [δ|]).
Proof.
    exact (ex_proof (transfinite_recursion _ f)).
Qed.

End OrdPowDef.
End OrdPowDef.

Definition ord_pow α β := OrdPowDef.g α β.
Infix "^" := ord_pow : ord_scope.

Theorem ord_pow_zero : ∀ α : ord, α ^ 0 = 1.
Proof.
    intros α.
    unfold ord_pow.
    rewrite OrdPowDef.g_eq.
    unfold OrdPowDef.f.
    rewrite (if_true Logic.eq_refl).
    reflexivity.
Qed.

Theorem ord_pow_lub : ∀ α β, 0 ≠ β → α ^ β = ord_lub β (λ δ, α ^ [δ|] * α).
Proof.
    intros α β β_nz.
    unfold ord_pow; cbn.
    rewrite OrdPowDef.g_eq at 1.
    unfold OrdPowDef.f.
    rewrite (if_false β_nz).
    reflexivity.
Qed.

Theorem zero_ord_pow : ∀ α : ord, 0 ≠ α → 0 ^ α = 0.
Proof.
    intros α α_nz.
    rewrite ord_pow_lub by exact α_nz.
    apply ord_lub_eq.
    -   intros x.
        rewrite mult_ranni.
        apply refl.
    -   intros ε ε_ge.
        apply ord_pos.
Qed.

Theorem ord_pow_one : ∀ α : ord, α ^ 1 = α.
Proof.
    intros α.
    rewrite ord_pow_lub by exact ord_not_trivial.
    apply ord_lub_eq.
    -   intros [δ δ_lt]; cbn.
        apply ord_lt_one_eq in δ_lt.
        subst.
        rewrite ord_pow_zero, mult_lid.
        apply refl.
    -   intros ε ε_ge.
        specialize (ε_ge [0|ord_one_pos]); cbn in ε_ge.
        rewrite ord_pow_zero, mult_lid in ε_ge.
        exact ε_ge.
Qed.

Theorem one_ord_pow : ∀ α : ord, 1 ^ α = 1.
Proof.
    intros α.
    induction α as [α IHα] using transfinite_induction.
    classic_case (0 = α) as [α_z|α_nz].
    1: subst; apply ord_pow_zero.
    rewrite ord_pow_lub by exact α_nz.
    apply ord_lub_eq.
    -   intros [δ δ_lt]; cbn.
        rewrite IHα by exact δ_lt.
        rewrite mult_lid.
        apply refl.
    -   intros ε ε_ge.
        specialize (ε_ge [0|all_pos2 α_nz]); cbn in ε_ge.
        rewrite ord_pow_zero, mult_lid  in ε_ge.
        exact ε_ge.
Qed.

Theorem ord_pow_nz : ∀ α β, 0 ≠ α → 0 ≠ α ^ β.
Proof.
    intros α β α_nz.
    classic_case (0 = β) as [β_z|β_nz].
    {
        subst.
        rewrite ord_pow_zero.
        exact ord_not_trivial.
    }
    intros eq.
    rewrite ord_pow_lub in eq by exact β_nz.
    pose proof (ord_lub_ge β (λ δ, α ^ [δ|] * α)) as leq.
    rewrite <- eq in leq.
    specialize (leq [0|all_pos2 β_nz]); cbn in leq.
    rewrite ord_pow_zero, mult_lid in leq.
    apply all_neg_eq in leq.
    contradiction.
Qed.

Theorem ord_pow_le : ∀ α β γ : ord, 0 ≠ α → β ≤ γ → α ^ β ≤ α ^ γ.
Proof.
    intros α β γ α_nz leq.
    classic_case (0 = γ) as [γ_z|γ_nz].
    {
        subst.
        rewrite (all_neg_eq leq).
        apply refl.
    }
    classic_case (0 = β) as [β_z|β_nz].
    {
        subst.
        rewrite ord_pow_zero.
        apply ord_pos_one.
        apply ord_pow_nz.
        exact α_nz.
    }
    rewrite (ord_pow_lub α β) by exact β_nz.
    apply ord_lub_least.
    intros [δ δ_lt]; cbn.
    rewrite (ord_pow_lub α γ) by exact γ_nz.
    apply ord_lub_other_leq.
    intros ε ε_ge.
    exact (ε_ge [δ|lt_le_trans δ_lt leq]).
Qed.

Theorem ord_pow_plus_one : ∀ α β, α ^ (β + 1) = α ^ β * α.
Proof.
    intros α β.
    assert (0 ≠ β + 1) as β_nz by (apply ord_nz_rplus; exact ord_not_trivial).
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst.
        rewrite zero_ord_pow by exact β_nz.
        rewrite mult_ranni.
        reflexivity.
    }
    rewrite ord_pow_lub by exact β_nz.
    apply ord_lub_eq.
    -   intros [δ δ_lt]; cbn.
        rewrite ord_lt_suc_le in δ_lt.
        apply le_rmult.
        apply ord_pow_le; assumption.
    -   intros ε ε_ge.
        exact (ε_ge [β|ord_lt_suc _]).
Qed.

Theorem ord_lub_pow : ∀ α β f, 0 ≠ α → 0 ≠ β →
    α ^ ord_lub β f = ord_lub β (λ x, α ^ f x).
Proof.
    intros α β f α_nz β_nz.
    classic_case (0 = ord_lub β f) as [f_z|f_nz].
    {
        rewrite <- f_z.
        rewrite ord_pow_zero.
        rewrite <- (ord_lub_constant 1 β) by exact β_nz.
        apply ord_lub_f_eq.
        intros x.
        rewrite <- (ord_lub_f_zero _ _ f_z).
        rewrite ord_pow_zero.
        reflexivity.
    }
    apply antisym.
    -   rewrite ord_pow_lub by exact f_nz.
        apply ord_lub_least.
        intros [δ δ_lt]; cbn.
        pose proof (ord_lub_in _ _ _ δ_lt) as [γ γ_ge].
        rewrite <- ord_le_suc_lt in γ_ge.
        rewrite <- ord_pow_plus_one.
        apply (ord_pow_le α _ _ α_nz) in γ_ge.
        apply (trans γ_ge).
        exact (ord_lub_ge β (λ x, α ^ f x) γ).
    -   apply ord_lub_least.
        intros δ.
        apply (ord_pow_le _ _ _ α_nz).
        apply ord_lub_ge.
Qed.

Theorem ord_pow_plus : ∀ α β γ : ord, α ^ (β + γ) = α ^ β * α ^ γ.
Proof.
    intros α β γ.
    induction γ as [γ IHγ] using transfinite_induction.
    classic_case (0 = γ) as [γ_z|γ_nz].
    {
        subst.
        rewrite ord_pow_zero.
        rewrite plus_rid, mult_rid.
        reflexivity.
    }
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst.
        rewrite (zero_ord_pow γ γ_nz).
        rewrite mult_ranni.
        apply zero_ord_pow.
        apply ord_nz_rplus.
        exact γ_nz.
    }
    rewrite ord_plus_lsub by exact γ_nz.
    rewrite (ord_pow_lub α γ) by exact γ_nz.
    rewrite ord_lub_mult.
    rewrite ord_lsub_lub.
    rewrite ord_lub_pow; [>|exact α_nz|exact γ_nz].
    apply ord_lub_f_eq.
    intros [x x_lt]; cbn.
    rewrite ord_pow_plus_one.
    rewrite IHγ by exact x_lt.
    rewrite mult_assoc.
    reflexivity.
Qed.

Theorem ord_pow_pow : ∀ α β γ : ord, (α ^ β) ^ γ = α ^ (β * γ).
Proof.
    intros α β γ.
    induction γ as [γ IHγ] using transfinite_induction.
    classic_case (0 = γ) as [γ_z|γ_nz].
    {
        subst.
        rewrite mult_ranni.
        do 2 rewrite ord_pow_zero.
        reflexivity.
    }
    classic_case (0 = β) as [β_z|β_nz].
    {
        subst.
        rewrite mult_lanni.
        rewrite ord_pow_zero.
        apply one_ord_pow.
    }
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst.
        rewrite zero_ord_pow by exact β_nz.
        rewrite zero_ord_pow by exact γ_nz.
        symmetry; apply zero_ord_pow.
        apply mult_nz; assumption.
    }
    rewrite (ord_pow_lub (α ^ β) γ) by exact γ_nz.
    rewrite ord_mult_lub.
    rewrite ord_lub_pow; [>|exact α_nz|exact γ_nz].
    apply ord_lub_f_eq.
    intros [δ δ_lt]; cbn.
    rewrite IHγ by exact δ_lt.
    rewrite ord_pow_plus.
    reflexivity.
Qed.

Theorem ord_pow_gt_one : ∀ α β, 0 ≠ β → 1 < α → 1 < α ^ β.
Proof.
    intros α β β_nz α_gt.
    pose proof (ord_lub_ge β (λ δ, α ^ [δ|] * α) [0|all_pos2 β_nz]) as leq.
    cbn in leq.
    rewrite <- ord_pow_lub in leq by exact β_nz.
    rewrite ord_pow_zero, mult_lid in leq.
    exact (lt_le_trans α_gt leq).
Qed.

Theorem ord_pow_lt : ∀ α β γ : ord, 1 < α → β < γ → α ^ β < α ^ γ.
Proof.
    intros α β γ α_gt ltq.
    apply ord_lt_ex in ltq as [δ [δ_nz δ_lt]]; subst γ.
    rewrite ord_pow_plus.
    rewrite <- (mult_rid (α ^ β)) at 1.
    apply lt_lmult.
    1: {
        apply ord_pow_nz.
        apply ord_pos_one.
        apply α_gt.
    }
    apply ord_pow_gt_one; assumption.
Qed.

Theorem ord_pow_lcancel : ∀ α β γ : ord, 1 < α → α ^ β = α ^ γ → β = γ.
Proof.
    intros α β γ α_gt eq.
    destruct (trichotomy β γ) as [[ltq|eq']|ltq].
    -   apply (ord_pow_lt _ _ _ α_gt) in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply (ord_pow_lt _ _ _ α_gt) in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

Theorem ord_le_rpow : ∀ α β γ : ord, α ≤ β → α ^ γ ≤ β ^ γ.
Proof.
    intros α β γ leq.
    induction γ as [γ IHγ] using transfinite_induction.
    classic_case (0 = γ) as [γ_z|γ_nz].
    {
        subst.
        do 2 rewrite ord_pow_zero.
        apply refl.
    }
    classic_case (0 = β) as [β_z|β_nz].
    {
        subst.
        apply all_neg_eq in leq; subst.
        apply refl.
    }
    rewrite (ord_pow_lub α γ) by exact γ_nz.
    apply ord_lub_least.
    intros [δ δ_lt]; cbn.
    rewrite (ord_pow_lub β γ) by exact γ_nz.
    apply ord_lub_other_leq.
    intros ε ε_ge.
    specialize (ε_ge [δ|δ_lt]); cbn in ε_ge.
    specialize (IHγ δ δ_lt).
    apply (le_rmult α) in IHγ.
    apply (trans IHγ).
    apply (le_lmult (β ^ δ)) in leq.
    apply (trans leq).
    exact ε_ge.
Qed.

Theorem ord_pow_le_pow : ∀ α β, 1 < β → α ≤ β ^ α.
Proof.
    intros α β β_gt.
    induction α as [α IHα] using transfinite_induction.
    classic_case (0 = α) as [α_z | α_nz].
    {
        subst.
        apply ord_pos.
    }
    rewrite ord_pow_lub by exact α_nz.
    apply ord_lub_other_leq.
    intros ε ε_ge.
    assert (0 ≠ ε) as ε_nz.
    {
        intro; subst.
        specialize (ε_ge [0|all_pos2 α_nz]); cbn in ε_ge.
        rewrite ord_pow_zero, mult_lid in ε_ge.
        apply all_neg_eq in ε_ge; subst.
        contradiction (not_neg β_gt).
    }
    order_contradiction ltq.
    specialize (ε_ge [ε|ltq]); cbn in ε_ge.
    specialize (IHα ε ltq).
    apply (le_rmult β) in IHα.
    pose proof (trans IHα ε_ge) as leq.
    assert (0 ≠ β) as β_nz by (apply ord_pos_one; apply β_gt).
    pose proof (ord_le_self_rmult ε β β_nz) as leq2.
    pose proof (antisym leq leq2) as eq; clear - eq β_gt ε_nz.
    rewrite <- (mult_rid ε) in eq at 2.
    apply (mult_lcancel _ ε_nz) in eq.
    subst.
    contradiction (irrefl _ β_gt).
Qed.

Close Scope ord_scope.
