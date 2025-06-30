Require Import init.

Require Export ord_plus.
Require Import ord_bounds.
Require Import set_induction.

Open Scope ord_scope.

Module OrdMultDef.
Section OrdMultDef.

Context (α : ord).

Definition f (β : ord) (g : set_type (λ x, x < β) → ord) :=
    ord_lub β (λ δ, g δ + α).

Definition g := ex_val (transfinite_recursion _ f).
Lemma g_eq : ∀ β : ord, g β = f β (λ δ : set_type (λ δ, δ < β), g [δ|]).
Proof.
    exact (ex_proof (transfinite_recursion _ f)).
Qed.

End OrdMultDef.
End OrdMultDef.

Global Instance ord_mult : Mult ord := {
    mult α β := OrdMultDef.g α β
}.

Theorem ord_mult_lub : ∀ α β, α * β = ord_lub β (λ δ, α * [δ|] + α).
Proof.
    intros α β.
    unfold mult; cbn.
    rewrite OrdMultDef.g_eq at 1.
    unfold OrdMultDef.f.
    reflexivity.
Qed.

Global Instance ord_mult_lanni : MultLanni ord.
Proof.
    split.
    intros α.
    induction α as [α IHα] using transfinite_induction.
    rewrite ord_mult_lub.
    apply ord_lub_eq.
    -   intros [β β_lt]; cbn.
        rewrite IHα by exact β_lt.
        rewrite plus_rid.
        apply refl.
    -   intros ε ε_ge.
        apply ord_pos.
Qed.

Global Instance ord_mult_ranni : MultRanni ord.
Proof.
    split.
    intros α.
    rewrite ord_mult_lub.
    apply ord_lub_eq.
    -   intros [δ δ_lt]; cbn.
        contradiction (not_neg δ_lt).
    -   intros ε ε_ge.
        apply ord_pos.
Qed.

Global Instance ord_one : One ord := {
    one := to_ord (make_ord_type singleton_type _ _ _)
}.

Theorem ord_not_trivial : 0 ≠ 1.
Proof.
    intros contr.
    symmetry in contr.
    unfold one, zero in contr; equiv_simpl in contr.
    destruct contr as [f].
    contradiction (empty_false (f Single)).
Qed.

Global Instance ord_not_trivial_class : NotTrivial ord := {
    not_trivial_a := 0;
    not_trivial_b := 1;
    not_trivial := ord_not_trivial;
}.

Theorem ord_one_pos : 0 < 1.
Proof.
    apply all_pos2.
    exact ord_not_trivial.
Qed.

Theorem ord_lt_one_eq : ∀ α, α < 1 → 0 = α.
Proof.
    intros A ltq.
    equiv_get_value A.
    unfold one in ltq; equiv_simpl in ltq.
    rewrite ord_lt_simpl in ltq.
    destruct ltq as [x [f]]; cbn in x.
    apply ord_false_0.
    intros a.
    pose proof [|f a] as ltq.
    unfold initial_segment in ltq.
    destruct ltq as [leq neq].
    apply neq.
    apply singleton_type_eq.
Qed.

Theorem ord_pos_one : ∀ α, 0 ≠ α ↔ 1 ≤ α.
Proof.
    intros α.
    split.
    -   intros neq.
        order_contradiction leq.
        apply ord_lt_one_eq in leq.
        contradiction.
    -   intros leq eq.
        subst.
        rewrite <- nlt_le in leq.
        contradiction (leq ord_one_pos).
Qed.

Theorem ord_lt_suc_le : ∀ α β, α < β + 1 ↔ α ≤ β.
Proof.
    intros α β.
    split.
    -   intros ltq.
        rewrite ord_plus_lsub in ltq by exact ord_not_trivial.
        pose proof (ord_lsub_least 1 (λ δ, β + [δ|])) as least.
        order_contradiction contr.
        specialize (least α).
        prove_parts least.
        {
            intros [δ δ_lt]; cbn.
            apply ord_lt_one_eq in δ_lt.
            subst.
            rewrite plus_rid.
            exact contr.
        }
        contradiction (irrefl _ (le_lt_trans least ltq)).
    -   intros leq.
        apply ord_le_ex in leq as [γ γ_eq].
        subst β.
        rewrite <- (plus_rid α) at 1.
        rewrite <- plus_assoc.
        apply lt_lplus.
        apply all_pos2.
        apply ord_nz_rplus.
        exact ord_not_trivial.
Qed.

Theorem ord_le_suc_lt : ∀ α β, α + 1 ≤ β ↔ α < β.
Proof.
    intros α β.
    split.
    -   intros leq.
        rewrite <- ord_lt_suc_le in leq.
        apply lt_plus_rcancel in leq.
        exact leq.
    -   intros ltq.
        apply ord_lt_ex in ltq as [γ [γ_nz γ_eq]].
        subst β.
        apply le_lplus.
        apply ord_pos_one.
        exact γ_nz.
Qed.

Theorem ord_le_suc : ∀ α, α ≤ α + 1.
Proof.
    intros α.
    apply ord_le_self_rplus.
Qed.

Theorem ord_lt_suc : ∀ α, α < α + 1.
Proof.
    intros α.
    rewrite ord_lt_suc_le.
    apply refl.
Qed.

Theorem ord_lsub_lub : ∀ β f, ord_lsub β f = ord_lub β (λ x, f x + 1).
Proof.
    intros β f.
    symmetry; apply ord_lub_eq.
    -   intros α.
        apply ord_lsub_other_leq.
        intros ε ε_ge.
        rewrite ord_le_suc_lt.
        apply ε_ge.
    -   intros ε ε_ge.
        apply ord_lsub_least.
        intros α.
        rewrite <- ord_le_suc_lt.
        apply ε_ge.
Qed.

Theorem ord_lub_one : ∀ α : ord, ord_lub 1 (λ _, α) = α.
Proof.
    intros α.
    apply ord_lub_eq.
    -   intros x.
        apply refl.
    -   intros ε ε_ge.
        exact (ε_ge [0|ord_one_pos]).
Qed.

Global Instance ord_mult_lid : MultLid ord.
Proof.
    split.
    intros α.
    induction α as [α IHα] using transfinite_induction.
    rewrite ord_mult_lub.
    rewrite <- (ord_lsub_self_eq α) at 2.
    rewrite ord_lsub_lub.
    apply ord_lub_f_eq.
    intros [δ δ_lt]; cbn.
    rewrite IHα by exact δ_lt.
    reflexivity.
Qed.

Global Instance ord_mult_rid : MultRid ord.
Proof.
    split.
    intros α.
    rewrite ord_mult_lub.
    rewrite <- (ord_lub_one α) at 1.
    apply ord_lub_f_eq.
    intros [δ δ_lt]; cbn.
    apply ord_lt_one_eq in δ_lt; subst.
    rewrite mult_ranni, plus_lid.
    reflexivity.
Qed.

Global Instance ord_mult_zero : MultZero ord.
Proof.
    split.
    intros α β eq.
    rewrite <- not_not, not_or.
    intros [α_nz β_nz].
    rewrite ord_mult_lub in eq.
    pose proof (ord_lub_ge β (λ δ, α * [δ|] + α)) as leq.
    rewrite <- eq in leq.
    specialize (leq [0|all_pos2 β_nz]); cbn in leq.
    rewrite mult_ranni, plus_lid in leq.
    apply all_neg_eq in leq.
    contradiction.
Qed.

Global Instance ord_le_lmult : OrderLmult ord.
Proof.
    split.
    intros α β γ γ_pos leq.
    rewrite (ord_mult_lub γ α).
    apply ord_lub_least.
    intros [δ δ_lt]; cbn.
    rewrite (ord_mult_lub γ β).
    apply ord_lub_other_leq.
    intros ε ε_ge.
    exact (ε_ge [δ|lt_le_trans δ_lt leq]).
Qed.

Theorem ord_ldist_one : ∀ α β, α * (β + 1) = α * β + α.
Proof.
    intros α β.
    rewrite ord_mult_lub.
    apply ord_lub_eq.
    -   intros [δ δ_lt]; cbn.
        rewrite ord_lt_suc_le in δ_lt.
        apply ord_le_rplus.
        apply le_lmult.
        exact δ_lt.
    -   intros ε ε_ge.
        exact (ε_ge [β|ord_lt_suc β]).
Qed.

Theorem ord_lub_mult : ∀ α β f,
    α * ord_lub β f = ord_lub β (λ x, α * f x).
Proof.
    intros α β f.
    apply antisym.
    -   rewrite ord_mult_lub.
        apply ord_lub_least.
        intros [δ δ_lt]; cbn.
        pose proof (ord_lub_in _ _ _ δ_lt) as [γ γ_ge].
        rewrite <- ord_le_suc_lt in γ_ge.
        rewrite <- ord_ldist_one.
        apply (le_lmult α) in γ_ge.
        apply (trans γ_ge).
        apply (ord_lub_ge β (λ x, α * f x)).
    -   apply ord_lub_least.
        intros δ.
        apply le_lmult.
        apply ord_lub_ge.
Qed.

Global Instance ord_ldist : Ldist ord.
Proof.
    split.
    intros α β γ.
    induction γ as [γ IHγ] using transfinite_induction.
    classic_case (0 = γ) as [γ_z|γ_nz].
    {
        subst γ.
        rewrite mult_ranni.
        do 2 rewrite plus_rid.
        reflexivity.
    }
    rewrite (ord_plus_lsub β γ) by exact γ_nz.
    rewrite (ord_mult_lub α γ).
    rewrite ord_lsub_lub.
    rewrite ord_lub_mult.
    rewrite ord_lub_plus by exact γ_nz.
    apply ord_lub_f_eq.
    intros [x x_lt]; cbn.
    rewrite plus_assoc.
    rewrite ord_ldist_one.
    rewrite IHγ by exact x_lt.
    reflexivity.
Qed.

Global Instance ord_mult_assoc : MultAssoc ord.
Proof.
    split.
    intros α β γ.
    induction γ as [γ IHγ] using transfinite_induction.
    rewrite (ord_mult_lub β γ).
    rewrite ord_lub_mult.
    rewrite ord_mult_lub.
    apply ord_lub_f_eq.
    intros [δ δ_lt]; cbn.
    rewrite ldist.
    rewrite IHγ by exact δ_lt.
    reflexivity.
Qed.

Global Instance ord_lt_lmult : OrderLmult2 ord.
Proof.
    split.
    intros α β γ [γ_pos γ_nz] ltq.
    apply ord_lt_ex in ltq as [δ [δ_nz δ_eq]].
    subst β.
    rewrite ldist.
    rewrite <- (plus_rid (γ * α)) at 1.
    apply lt_lplus.
    apply all_pos2.
    apply mult_nz; assumption.
Qed.

Definition ord_mult_lcancel := mult_lcancel1 : MultLcancel ord.
Global Existing Instances ord_mult_lcancel.

Global Instance ord_le_rmult : OrderRmult ord.
Proof.
    split.
    intros α β γ γ_pos leq.
    clear γ_pos.
    induction γ as [γ IHγ] using transfinite_induction.
    rewrite (ord_mult_lub β γ).
    apply ord_lub_other_leq.
    intros ε ε_ge.
    rewrite (ord_mult_lub α γ).
    apply ord_lub_least.
    intros [δ δ_lt]; cbn.
    specialize (ε_ge [δ|δ_lt]); cbn in ε_ge.
    specialize (IHγ δ δ_lt).
    pose proof (le_lrplus IHγ leq) as leq2.
    exact (trans leq2 ε_ge).
Qed.

Theorem ord_le_self_lmult : ∀ α β, 0 ≠ β → α ≤ β * α.
Proof.
    intros α β β_nz.
    apply ord_pos_one in β_nz.
    apply (le_rmult α) in β_nz.
    rewrite mult_lid in β_nz.
    exact β_nz.
Qed.

Theorem ord_le_self_rmult : ∀ α β, 0 ≠ β → α ≤ α * β.
Proof.
    intros α β β_nz.
    apply ord_pos_one in β_nz.
    apply (le_lmult α) in β_nz.
    rewrite mult_rid in β_nz.
    exact β_nz.
Qed.

Theorem ord_div : ∀ α β, 0 ≠ β → ∃ γ δ, α = β * γ + δ ∧ δ < β.
Proof.
    intros α β β_nz.
    pose (S η := α < β * η).
    pose proof (well_ordered S) as ε_ex.
    prove_parts ε_ex.
    {
        exists (α + 1).
        unfold S.
        rewrite <- ord_le_suc_lt.
        apply ord_le_self_lmult.
        exact β_nz.
    }
    destruct ε_ex as [ε [ε_ltq ε_least]].
    unfold S in *.
    classic_case (0 = ε) as [ε_z|ε_nz].
    {
        subst.
        rewrite mult_ranni in ε_ltq.
        contradiction (not_neg ε_ltq).
    }
    assert (∃ γ, γ + 1 = ε) as [γ γ_eq].
    {
        classic_contradiction contr.
        assert (β * ε ≤ α) as α_ge.
        {
            rewrite ord_mult_lub.
            apply ord_lub_least.
            intros [ζ ζ_lt]; cbn.
            rewrite <- ord_le_suc_lt in ζ_lt.
            rewrite <- ord_ldist_one.
            order_contradiction ltq.
            specialize (ε_least _ ltq).
            apply contr.
            exists ζ.
            apply antisym; assumption.
        }
        contradiction (irrefl _ (le_lt_trans α_ge ε_ltq)).
    }
    subst ε.
    assert (β * γ ≤ α) as leq.
    {
        order_contradiction ltq.
        specialize (ε_least _ ltq).
        rewrite <- nlt_le in ε_least.
        contradiction (ε_least (ord_lt_suc _)).
    }
    apply ord_le_ex in leq as [δ δ_eq].
    exists γ, δ.
    split; [>subst; reflexivity|].
    subst.
    rewrite ord_ldist_one in ε_ltq.
    apply lt_plus_lcancel in ε_ltq.
    exact ε_ltq.
Qed.

Close Scope ord_scope.
