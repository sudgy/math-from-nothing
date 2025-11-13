Require Import init.

Require Export ord_order.
Require Export ord_normal.
Require Import set_induction.

Open Scope ord_scope.

Global Instance ord_plus : Plus ord := {
    plus α := make_ord_normal α (λ α β, ord_suc β)
}.

Global Instance ord_plus_rid : PlusRid ord.
Proof.
    split.
    intros α.
    unfold plus; cbn.
    apply make_ord_normal_zero.
Qed.

Theorem ord_plus_suc : ∀ α β, α + ord_suc β = ord_suc (α + β).
Proof.
    intros α β.
    unfold plus; cbn.
    apply make_ord_normal_suc.
Qed.

Theorem ord_plus_lim : ∀ α β, lim_ord β → α + β = ord_f_sup β (λ δ, α + [δ|]).
Proof.
    intros α β β_lim.
    unfold plus; cbn.
    apply make_ord_normal_lim.
    exact β_lim.
Qed.

Theorem ord_plus_normal : ∀ α, OrdNormal (plus α).
Proof.
    intros α.
    apply make_ord_normal_lim.
Qed.

Lemma ord_plus_lt_suc : ∀ α β, α + β < α + ord_suc β.
Proof.
    intros α β.
    rewrite ord_plus_suc.
    apply ord_lt_suc.
Qed.

Theorem ord_plus_homo_le : ∀ α, HomomorphismLe (plus α).
Proof.
    intros α.
    apply make_ord_normal_le.
    apply ord_plus_lt_suc.
Qed.

Theorem ord_plus_homo_inj : ∀ α, Injective (plus α).
Proof.
    intros α.
    apply make_ord_normal_inj.
    apply ord_plus_lt_suc.
Qed.

Theorem ord_plus_sup : ∀ α,
    ∀ β (g : set_type (λ α, α < β) → ord), 0 ≠ β →
    α + (ord_f_sup β g) = ord_f_sup β (λ δ, α + g δ).
Proof.
    intros α.
    apply ord_normal_f_sup.
    -   apply ord_plus_homo_le.
    -   apply ord_plus_normal.
Qed.

Global Instance ord_plus_lid : PlusLid ord.
Proof.
    split.
    intros α.
    induction α as [|α IHα|α α_lim IHα] using ord_induction.
    -   apply plus_rid.
    -   rewrite ord_plus_suc.
        rewrite IHα.
        reflexivity.
    -   rewrite (ord_plus_lim _ _ α_lim).
        rewrite <- (ord_f_sup_lim_eq α α_lim) at 2.
        apply ord_f_sup_f_eq.
        intros [δ δ_lt]; cbn.
        exact (IHα δ δ_lt).
Qed.

Global Instance ord_lt_lplus : OrderLplus2 ord.
Proof.
    split.
    intros α β γ ltq.
    pose proof (ord_plus_homo_le γ).
    pose proof (ord_plus_homo_inj γ).
    rewrite <- homo_lt2.
    exact ltq.
Qed.

Definition ord_plus_lcancel := plus_lcancel1 : PlusLcancel ord.
Definition ord_le_lplus := le_lplus2 : OrderLplus ord.
Global Existing Instances ord_plus_lcancel ord_le_lplus.

Theorem ord_le_self_rplus : ∀ α β, α ≤ α + β.
Proof.
    intros α β.
    rewrite <- plus_rid at 1.
    apply le_lplus.
    apply all_pos.
Qed.

Theorem ord_le_self_lplus : ∀ α β, α ≤ β + α.
Proof.
    intros α β.
    apply ord_normal_le.
    -   apply ord_plus_homo_le.
    -   apply ord_plus_homo_inj.
Qed.

Theorem ord_le_ex : ∀ α β, α ≤ β → ∃ γ, α + γ = β.
Proof.
    intros α β leq.
    pose proof (well_ordered (λ γ, β ≤ α + γ)) as γ_ex.
    prove_parts γ_ex.
    {
        exists β.
        apply ord_le_self_lplus.
    }
    destruct γ_ex as [γ [γ_lt γ_least]].
    exists γ.
    apply antisym; [>|exact γ_lt].
    induction γ as [|γ|γ γ_lim] using ord_destruct.
    -   rewrite plus_rid.
        exact leq.
    -   order_contradiction ltq.
        rewrite ord_plus_suc in ltq.
        rewrite ord_lt_suc_le in ltq.
        specialize (γ_least _ ltq).
        rewrite <- nlt_le in γ_least.
        apply γ_least.
        apply ord_lt_suc.
    -   rewrite ord_plus_lim by exact γ_lim.
        apply ord_f_sup_least.
        intros [δ δ_lt]; cbn.
        order_contradiction contr.
        specialize (γ_least _ (land contr)).
        contradiction (irrefl _ (le_lt_trans γ_least δ_lt)).
Qed.

Theorem ord_lt_ex : ∀ α β, α < β → ∃ γ, 0 ≠ γ ∧ α + γ = β.
Proof.
    intros α β ltq.
    pose proof (ord_le_ex _ _ (land ltq)) as [γ eq].
    exists γ.
    split; [>|exact eq].
    intros contr; subst.
    rewrite plus_rid in ltq.
    contradiction (irrefl _ ltq).
Qed.

Theorem ord_nz_rplus : ∀ α β, 0 ≠ β → 0 ≠ α + β.
Proof.
    intros α β β_nz contr.
    pose proof (ord_le_self_lplus β α) as leq.
    rewrite <- contr in leq.
    apply all_neg_eq in leq.
    contradiction.
Qed.

Theorem ord_nz_lplus : ∀ α β, 0 ≠ α → 0 ≠ α + β.
Proof.
    intros α β α_nz.
    classic_case (0 = β) as [eq|neq].
    -   subst.
        rewrite plus_rid.
        exact α_nz.
    -   apply ord_nz_rplus.
        exact neq.
Qed.

Global Instance ord_plus_assoc : PlusAssoc ord.
Proof.
    split.
    intros α β γ.
    induction γ as [|γ IHγ|γ γ_lim IHγ] using ord_induction.
    -   do 2 rewrite plus_rid.
        reflexivity.
    -   do 3 rewrite ord_plus_suc.
        rewrite IHγ.
        reflexivity.
    -   do 2 rewrite (ord_plus_lim _ γ γ_lim).
        rewrite (ord_plus_sup _ _ _ (land γ_lim)).
        apply ord_f_sup_f_eq.
        intros [δ δ_lt]; cbn.
        apply IHγ.
        exact δ_lt.
Qed.

Global Instance ord_le_rplus : OrderRplus ord.
Proof.
    split.
    intros α β γ leq.
    apply ord_le_ex in leq as [δ eq].
    rewrite <- eq.
    rewrite <- plus_assoc.
    apply le_lplus.
    apply ord_le_self_lplus.
Qed.

Theorem ord_lt_self_rplus : ∀ α β, 0 ≠ β → α < α + β.
Proof.
    intros α β β_nz.
    split.
    -   apply ord_le_self_rplus.
    -   intros contr.
        rewrite <- plus_rid in contr at 1.
        apply plus_lcancel in contr.
        contradiction.
Qed.

Theorem ord_plus_zero : ∀ α β, 0 = α + β → 0 = α ∧ 0 = β.
Proof.
    intros α β eq.
    split.
    -   classic_contradiction neq.
        apply (ord_nz_lplus _ _ neq) in eq.
        exact eq.
    -   classic_contradiction neq.
        apply (ord_nz_rplus _ _ neq) in eq.
        exact eq.
Qed.

Theorem ord_plus_lim_lim : ∀ α β, lim_ord β → lim_ord (α + β).
Proof.
    intros α β β_lim.
    pose proof (ord_plus_normal α).
    pose proof (ord_plus_homo_le α).
    pose proof (ord_plus_homo_inj α).
    apply (ord_normal_lim_ord (plus α)).
    exact β_lim.
Qed.

Close Scope ord_scope.
