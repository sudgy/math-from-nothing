Require Import init.

Require Export ord_plus.
Require Import set_induction.

Open Scope ord_scope.

Global Instance ord_mult : Mult ord := {
    mult α := make_ord_normal 0 (λ _ β, β + α)
}.

Global Instance ord_mult_ranni : MultRanni ord.
Proof.
    split.
    intros α.
    unfold mult; cbn.
    apply make_ord_normal_zero.
Qed.

Theorem ord_mult_suc : ∀ α β, α * ord_suc β = α * β + α.
Proof.
    intros α β.
    unfold mult; cbn.
    apply make_ord_normal_suc.
Qed.

Theorem ord_mult_lim : ∀ α β, lim_ord β → α * β = ord_f_sup β (λ δ, α * [δ|]).
Proof.
    intros α β β_lim.
    unfold mult; cbn.
    apply make_ord_normal_lim.
    exact β_lim.
Qed.

Theorem ord_mult_normal : ∀ α, OrdNormal (mult α).
Proof.
    intros α.
    apply make_ord_normal_lim.
Qed.

Lemma ord_mult_le_suc : ∀ α β, α * β ≤ α * ord_suc β.
Proof.
    intros α β.
    rewrite ord_mult_suc.
    apply ord_le_self_rplus.
Qed.

Lemma ord_mult_lt_suc : ∀ α β, 0 ≠ α → α * β < α * ord_suc β.
Proof.
    intros α β α_nz.
    rewrite ord_mult_suc.
    apply ord_lt_self_rplus.
    exact α_nz.
Qed.

Theorem ord_mult_homo_le : ∀ α, HomomorphismLe (mult α).
Proof.
    intros α.
    apply make_ord_normal_le.
    apply ord_mult_le_suc.
Qed.

Theorem ord_mult_homo_inj : ∀ α, 0 ≠ α → Injective (mult α).
Proof.
    intros α α_nz.
    apply make_ord_normal_inj.
    intros β.
    apply ord_mult_lt_suc.
    exact α_nz.
Qed.

Theorem ord_mult_sup : ∀ α,
    ∀ β (g : set_type (λ α, α < β) → ord), 0 ≠ β →
    α * (ord_f_sup β g) = ord_f_sup β (λ δ, α * g δ).
Proof.
    intros α.
    apply ord_normal_f_sup.
    -   apply ord_mult_homo_le.
    -   apply ord_mult_normal.
Qed.

Global Instance ord_mult_lanni : MultLanni ord.
Proof.
    split.
    intros α.
    induction α as [|α IHα|α α_lim IHα] using ord_induction.
    -   apply mult_ranni.
    -   rewrite ord_mult_suc.
        rewrite IHα.
        apply plus_lid.
    -   rewrite (ord_mult_lim _ α α_lim).
        apply ord_f_sup_eq.
        +   intros [β β_lt]; cbn.
            rewrite IHα by exact β_lt.
            apply refl.
        +   intros ε ε_ge.
            apply all_pos.
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

Theorem ord_suc_zero_one : ord_suc 0 = 1.
Proof.
    apply antisym.
    -   rewrite ord_le_suc_lt.
        apply ord_one_pos.
    -   apply ord_pos_one.
        apply ord_zero_suc.
Qed.

Theorem ord_suc_plus_one : ∀ α, ord_suc α = α + 1.
Proof.
    intros α.
    rewrite <- ord_suc_zero_one.
    rewrite ord_plus_suc.
    rewrite plus_rid.
    reflexivity.
Qed.

Global Instance ord_mult_lid : MultLid ord.
Proof.
    split.
    intros α.
    induction α as [|α IHα|α α_lim IHα] using ord_induction.
    -   apply mult_ranni.
    -   rewrite ord_mult_suc.
        rewrite IHα.
        rewrite ord_suc_plus_one.
        reflexivity.
    -   rewrite (ord_mult_lim _ α α_lim).
        rewrite <- (ord_f_sup_lim_eq α α_lim) at 2.
        apply ord_f_sup_f_eq.
        intros [δ δ_lt]; cbn.
        exact (IHα _ δ_lt).
Qed.

Global Instance ord_mult_rid : MultRid ord.
Proof.
    split.
    intros α.
    rewrite <- ord_suc_zero_one.
    rewrite ord_mult_suc.
    rewrite mult_ranni.
    apply plus_lid.
Qed.

Global Instance ord_mult_zero : MultZero ord.
Proof.
    split.
    intros α β eq.
    induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
    -   right; reflexivity.
    -   rewrite ord_mult_suc in eq.
        apply ord_plus_zero in eq.
        left; exact (rand eq).
    -   rewrite <- not_not, not_or.
        intros [α_nz β_nz].
        rewrite ord_mult_lim in eq by exact β_lim.
        pose proof (ord_f_sup_ge β (λ δ, α * [δ|])) as leq.
        rewrite <- eq in leq.
        specialize (leq [ord_suc 0|ord_lim_gt β β_lim]); cbn in leq.
        rewrite ord_mult_suc in leq.
        rewrite mult_ranni, plus_lid in leq.
        apply all_neg_eq in leq.
        contradiction.
Qed.

Global Instance ord_le_lmult : OrderLmult ord.
Proof.
    split.
    intros α β γ γ_pos leq.
    pose proof (ord_mult_homo_le γ).
    apply homo_le.
    exact leq.
Qed.

Global Instance ord_ldist : Ldist ord.
Proof.
    split.
    intros α β γ.
    induction γ as [|γ IHγ|γ γ_lim IHγ] using ord_induction.
    -   rewrite mult_ranni.
        do 2 rewrite plus_rid.
        reflexivity.
    -   rewrite ord_plus_suc.
        do 2 rewrite ord_mult_suc.
        rewrite IHγ.
        rewrite plus_assoc.
        reflexivity.
    -   rewrite (ord_plus_lim _ γ γ_lim).
        rewrite (ord_mult_lim _ γ γ_lim).
        rewrite ord_mult_sup by apply γ_lim.
        rewrite ord_plus_sup by apply γ_lim.
        apply ord_f_sup_f_eq.
        intros [δ δ_lt]; cbn.
        exact (IHγ δ δ_lt).
Qed.

Global Instance ord_mult_assoc : MultAssoc ord.
Proof.
    split.
    intros α β γ.
    induction γ as [|γ IHγ|γ γ_lim IHγ] using ord_induction.
    -   do 3 rewrite mult_ranni.
        reflexivity.
    -   do 2 rewrite ord_mult_suc.
        rewrite ldist.
        rewrite IHγ.
        reflexivity.
    -   do 2 rewrite (ord_mult_lim _ γ γ_lim).
        rewrite ord_mult_sup by apply γ_lim.
        apply ord_f_sup_f_eq.
        intros [δ δ_lt]; cbn.
        exact (IHγ δ δ_lt).
Qed.

Global Instance ord_lt_lmult : OrderLmult2 ord.
Proof.
    split.
    intros α β γ [γ_pos γ_nz] ltq.
    pose proof (ord_mult_homo_le γ).
    pose proof (ord_mult_homo_inj γ γ_nz).
    apply homo_lt.
    exact ltq.
Qed.

Definition ord_mult_lcancel := mult_lcancel1 : MultLcancel ord.
Global Existing Instances ord_mult_lcancel.

Global Instance ord_le_rmult : OrderRmult ord.
Proof.
    split.
    intros α β γ γ_pos leq.
    clear γ_pos.
    induction γ as [|γ IHγ|γ γ_lim IHγ] using ord_induction.
    -   do 2 rewrite mult_ranni.
        apply refl.
    -   do 2 rewrite ord_mult_suc.
        apply le_lrplus; assumption.
    -   do 2 rewrite ord_mult_lim by exact γ_lim.
        apply ord_f_sup_other_leq.
        intros ε ε_ge.
        apply ord_f_sup_least.
        intros [δ δ_lt]; cbn.
        specialize (ε_ge [δ|δ_lt]); cbn in ε_ge.
        specialize (IHγ δ δ_lt).
        exact (trans IHγ ε_ge).
Qed.

Theorem ord_le_self_lmult : ∀ α β, 0 ≠ β → α ≤ β * α.
Proof.
    intros α β β_nz.
    apply ord_normal_le.
    -   apply ord_mult_homo_le.
    -   apply ord_mult_homo_inj.
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
        exists (ord_suc α).
        unfold S.
        rewrite <- ord_le_suc_lt.
        apply ord_le_self_lmult.
        exact β_nz.
    }
    destruct ε_ex as [ε [ε_ltq ε_least]].
    unfold S in *.
    induction ε as [|ε IHε|ε ε_lim IHε] using ord_induction.
    -   rewrite mult_ranni in ε_ltq.
        contradiction (not_neg ε_ltq).
    -   assert (β * ε ≤ α) as leq.
        {
            order_contradiction ltq.
            specialize (ε_least _ ltq).
            rewrite <- nlt_le in ε_least.
            contradiction (ε_least (ord_lt_suc _)).
        }
        apply ord_le_ex in leq as [δ δ_eq].
        exists ε, δ.
        split; [>subst; reflexivity|].
        subst.
        rewrite ord_mult_suc in ε_ltq.
        apply lt_plus_lcancel in ε_ltq.
        exact ε_ltq.
    -   assert (β * ε ≤ α) as α_ge.
        {
            rewrite ord_mult_lim by exact ε_lim.
            apply ord_f_sup_least.
            intros [ζ ζ_lt]; cbn.
            rewrite <- ord_le_suc_lt in ζ_lt.
            order_contradiction ltq.
            specialize (ε_least _ ltq).
            apply (rand ε_lim).
            exists ζ.
            apply antisym.
            -   apply (trans ε_least).
                apply ord_lt_suc.
            -   exact ζ_lt.
        }
        contradiction (irrefl _ (le_lt_trans α_ge ε_ltq)).
Qed.

Theorem ord_mult_lim_lim : ∀ α β, 0 ≠ α → lim_ord β → lim_ord (α * β).
Proof.
    intros α β α_nz β_lim.
    pose proof (ord_mult_normal α).
    pose proof (ord_mult_homo_le α).
    pose proof (ord_mult_homo_inj α α_nz).
    apply (ord_normal_lim_ord (mult α)).
    exact β_lim.
Qed.

Theorem ord_lim_mult_lim : ∀ α β, 0 ≠ β → lim_ord α → lim_ord (α * β).
Proof.
    intros α β β_nz α_lim.
    induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
    -   contradiction.
    -   rewrite ord_mult_suc.
        apply ord_plus_lim_lim.
        exact α_lim.
    -   apply ord_mult_lim_lim.
        +   apply α_lim.
        +   exact β_lim.
Qed.

Close Scope ord_scope.
