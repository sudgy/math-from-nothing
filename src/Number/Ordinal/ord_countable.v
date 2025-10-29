Require Import init.

Require Export ord_nat.
Require Export card_set.

Open Scope card_scope.

Definition ord_countable (α : ord) := ord_to_card α ≤ |nat|.

Theorem ord_countable_suc : ∀ α, ord_countable α → ord_countable (ord_suc α).
Proof.
    intros A.
    equiv_get_value A.
    rewrite ord_suc_type.
    unfold ord_countable.
    unfold ord_to_card; equiv_simpl.
    intros leq.
    assert (|(A + singleton_type)%type| = |A| + 1) as eq.
    {
        unfold one, plus; cbn.
        rewrite binary_op_eq.
        reflexivity.
    }
    rewrite eq; clear eq.
    classic_case (|A| = |nat|) as [eq|neq].
    -   rewrite eq.
        rewrite card_inf_plus_one by apply refl.
        apply refl.
    -   pose proof (fin_nat_ex _ (make_and leq neq)) as [n n_eq].
        rewrite <- n_eq.
        rewrite <- (homo_one (f := from_nat)).
        rewrite <- homo_plus.
        apply nat_is_finite.
Qed.

Theorem ord_sup_countable : ∀ α f,
    ord_countable α → (∀ β, ord_countable (f β)) → ord_countable (ord_sup α f).
Proof.
    intros α f α_count β_count.
    classic_case (∃ β, f β = ord_sup α f) as [β_ex|β_nex].
    {
        destruct β_ex as [β β_eq].
        rewrite <- β_eq.
        apply β_count.
    }
    assert (∀ β, f β < ord_sup α f) as f_in.
    {
        intros β.
        split; [>apply ord_sup_ge|].
        rewrite not_ex in β_nex.
        apply β_nex.
    }
    unfold ord_countable.
    remember (ord_sup α f) as A.
    equiv_get_value A.
    rename H0 into A_eq.
    rewrite <- A_eq.
    rewrite <- A_eq in f_in.
    unfold ord_to_card; equiv_simpl.
    rewrite card_all.
    pose proof (ord_type_init_ord_bij A).
    pose proof (ord_type_init_ord_le A).
    assert ((all (U := A)) = ⋃ (λ S, ∃ β,
        S = initial_segment (bij_inv (ord_type_init_ord A) [f β|f_in β])))
        as eq.
    {
        apply antisym.
        -   intros x x_in; clear x_in.
            pose proof [|ord_type_init_ord A x] as x_lt.
            unfold initial_segment in x_lt.
            rewrite A_eq in x_lt.
            apply ord_sup_in in x_lt as [β x_lt].
            exists (initial_segment (bij_inv (ord_type_init_ord A)
                [f β|f_in β])).
            split.
            +   exists β.
                reflexivity.
            +   unfold initial_segment.
                rewrite (homo_lt2 (f := ord_type_init_ord A)).
                rewrite bij_inv_eq2.
                rewrite <- set_type_lt.
                exact x_lt.
        -   apply all_sub.
    }
    rewrite eq; clear eq.
    apply countable_union_countable.
    -   equiv_get_value α.
        apply (trans2 α_count).
        unfold ord_to_card; equiv_simpl.
        unfold le at 1; equiv_simpl.
        pose proof (ord_type_init_ord_bij α).
        exists (λ g : set_type (λ A0, _),
            bij_inv (ord_type_init_ord α) (ex_val [|g])).
        split.
        intros S T.
        rewrite_ex_val σ σ_eq.
        rewrite_ex_val τ τ_eq.
        intros eq.
        apply set_type_eq.
        rewrite σ_eq, τ_eq.
        clear S T σ_eq τ_eq.
        apply (f_equal (ord_type_init_ord α)) in eq.
        do 2 rewrite bij_inv_eq2 in eq.
        subst τ.
        reflexivity.
    -   intros S [β S_eq]; subst S.
        apply (trans2 (β_count β)).
        pose (B := f β).
        assert (B = f β) as B_eq by reflexivity.
        clearbody B.
        equiv_get_value B.
        rename H2 into B_eq.
        rewrite <- B_eq at 2.
        unfold ord_to_card, le; equiv_simpl.
        assert (to_ord B < to_ord A) as ltq.
        {
            rewrite B_eq.
            apply f_in.
        }
        assert (([f β | f_in β] : set_type (initial_segment (to_ord A)))
            = [to_ord B | ltq]) as eq.
        {
            apply set_type_eq; cbn.
            symmetry; exact B_eq.
        }
        rewrite eq; clear eq β B_eq.
        assert (∀ x, initial_segment (bij_inv (ord_type_init_ord A)
            [to_ord B | ltq]) x → [ord_type_init_ord A x|] < to_ord B) as x_lt.
        {
            intros x x_lt.
            unfold initial_segment in x_lt.
            apply (homo_lt (f := ord_type_init_ord A)) in x_lt.
            rewrite bij_inv_eq2 in x_lt.
            apply set_type_lt in x_lt.
            exact x_lt.
        }
        pose proof (ord_type_init_ord_bij B).
        exists (λ x, bij_inv (ord_type_init_ord B)
            [[ord_type_init_ord A [x|]|]|x_lt [x|] [|x]]).
        split.
        intros [a a_lt] [b b_lt]; cbn.
        intros eq.
        apply (f_equal (ord_type_init_ord B)) in eq.
        do 2 rewrite bij_inv_eq2 in eq.
        rewrite set_type_eq2 in eq.
        pose proof (ord_type_init_ord_base_inj A).
        apply inj in eq.
        apply set_type_eq.
        exact eq.
Qed.

Close Scope card_scope.
Open Scope ord_scope.

Theorem ord_countable_lt : ∀ α β, ord_countable β → α < β → ord_countable α.
Proof.
    intros α β β_count ltq.
    apply (trans2 β_count).
    apply ord_to_card_le.
    apply ltq.
Qed.

Theorem nat_ord_countable : ∀ n, ord_countable (from_nat n).
Proof.
    intros n.
    unfold ord_countable.
    rewrite ord_to_card_nat.
    apply nat_is_finite.
Qed.

Theorem zero_ord_countable : ord_countable 0.
Proof.
    rewrite <- homo_zero.
    apply nat_ord_countable.
Qed.

Theorem one_ord_countable : ord_countable 1.
Proof.
    rewrite <- homo_one.
    apply nat_ord_countable.
Qed.

Theorem omega_countable : ord_countable ω.
Proof.
    unfold ord_countable, ord_to_card, ω; equiv_simpl.
    apply refl.
Qed.

Theorem ord_countable_plus_nat : ∀ α n,
    ord_countable α → ord_countable (α + from_nat n).
Proof.
    intros α n α_count.
    nat_induction n.
    -   rewrite homo_zero, plus_rid.
        exact α_count.
    -   rewrite nat_ord_suc.
        rewrite ord_plus_suc.
        apply ord_countable_suc.
        exact IHn.
Qed.

Theorem ord_countable_plus : ∀ α β,
    ord_countable α → ord_countable β → ord_countable (α + β).
Proof.
    intros α β α_count β_count.
    induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
    -   rewrite plus_rid.
        exact α_count.
    -   rewrite ord_plus_suc.
        apply ord_countable_suc.
        apply IHβ.
        apply (ord_countable_lt _ _ β_count).
        apply ord_lt_suc.
    -   rewrite ord_plus_lim by exact β_lim.
        apply ord_sup_countable; [>exact β_count|].
        intros [δ δ_lt]; cbn.
        apply (IHβ δ δ_lt).
        apply (ord_countable_lt _ _ β_count).
        exact δ_lt.
Qed.

Theorem ord_countable_mult : ∀ α β,
    ord_countable α → ord_countable β → ord_countable (α * β).
Proof.
    intros α β α_count β_count.
    induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
    -   rewrite mult_ranni.
        apply zero_ord_countable.
    -   rewrite ord_mult_suc.
        apply ord_countable_plus; [>|exact α_count].
        apply IHβ.
        apply (ord_countable_lt _ _ β_count).
        apply ord_lt_suc.
    -   rewrite ord_mult_lim by exact β_lim.
        apply ord_sup_countable; [>exact β_count|].
        intros [δ δ_lt]; cbn.
        apply (IHβ δ δ_lt).
        apply (ord_countable_lt _ _ β_count).
        exact δ_lt.
Qed.

Theorem ord_countable_pow : ∀ α β,
    ord_countable α → ord_countable β → ord_countable (α ^ β).
Proof.
    intros α β α_count β_count.
    classic_case (0 = α) as [α_z|α_nz].
    {
        subst α.
        classic_case (0 = β) as [β_z|β_nz].
        -   subst β.
            rewrite ord_pow_zero.
            apply one_ord_countable.
        -   rewrite zero_ord_pow by exact β_nz.
            apply zero_ord_countable.
    }
    induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
    -   rewrite ord_pow_zero.
        apply one_ord_countable.
    -   rewrite ord_pow_suc.
        apply ord_countable_mult; [>|exact α_count].
        apply IHβ.
        apply (ord_countable_lt _ _ β_count).
        apply ord_lt_suc.
    -   rewrite (ord_pow_lim _ _ α_nz) by exact β_lim.
        apply ord_sup_countable; [>exact β_count|].
        intros [δ δ_lt]; cbn.
        apply (IHβ δ δ_lt).
        apply (ord_countable_lt _ _ β_count).
        exact δ_lt.
Qed.

Fixpoint power_tower (α : ord) (n : nat) :=
    match n with
    | nat_zero => 1
    | nat_suc n' => α ^ (power_tower α n')
    end.

Definition ε0 := ord_sup ω (λ n, power_tower ω (ex_val (ord_lt_ω [n|] [|n]))).

Theorem ω_ε0 : ω ^ ε0 = ε0.
Proof.
    unfold ε0.
    rewrite ord_pow_sup by apply ω_lim.
    apply antisym; apply ord_sup_leq_sup.
    -   intros [n' n'_lt]; cbn.
        rewrite_ex_val n n_eq; subst n'.
        exists [from_nat (nat_suc n) | nat_lt_ω (nat_suc n)].
        rewrite_ex_val m m_eq; cbn in m_eq.
        apply inj in m_eq.
        subst m.
        cbn.
        apply refl.
    -   intros [n' n'_lt]; cbn.
        rewrite_ex_val n n_eq; subst n'.
        exists [from_nat n | n'_lt].
        rewrite_ex_val m m_eq; cbn in m_eq.
        apply inj in m_eq.
        subst m.
        apply ord_pow_le_pow.
        rewrite <- homo_one.
        apply nat_lt_ω.
Qed.

Theorem ε0_countable : ord_countable ε0.
Proof.
    unfold ε0.
    apply ord_sup_countable.
    -   exact omega_countable.
    -   intros [n' n'_lt]; cbn.
        rewrite_ex_val n n_eq; subst n'.
        clear n'_lt.
        nat_induction n.
        +   unfold zero; cbn.
            apply one_ord_countable.
        +   cbn.
            apply ord_countable_pow.
            *   exact omega_countable.
            *   exact IHn.
Qed.
