Require Import init.

Require Export ord_nat.
Require Export card_set.
Require Export ord_derivative.
Require Import card_list.

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

Theorem ord_sup_countable : ∀ S Ss,
    small_set_to_card S Ss ≤ |nat| → (∀ α, S α → ord_countable α) →
    ord_countable (ord_sup S Ss).
Proof.
    intros S Ss S_count α_count.
    unfold ord_countable in *.
    classic_case (S (ord_sup S Ss)) as [A_in|A_nin].
    {
        apply α_count.
        exact A_in.
    }
    remember (ord_sup S Ss) as A.
    equiv_get_value A.
    rename H0 into A_eq.
    rewrite <- A_eq.
    assert (∀ α, S α → α < to_ord A) as α_lt.
    {
        rewrite A_eq.
        intros α Sα.
        split.
        -   apply ord_sup_ge.
            exact Sα.
        -   intros contr.
            subst; contradiction.
    }
    clear A_nin.
    unfold ord_to_card; equiv_simpl.
    rewrite card_all.
    pose proof (ord_type_init_ord_bij A).
    pose proof (ord_type_init_ord_le A).
    assert ((all (U := A)) = ⋃ (λ T, ∃ α : set_type S,
        T = initial_segment (bij_inv (ord_type_init_ord A) [[α|]|α_lt _ [|α]])))
        as eq.
    {
        symmetry; apply all_eq.
        intros x.
        pose proof [|ord_type_init_ord A x] as x_lt.
        unfold initial_segment in x_lt.
        rewrite A_eq in x_lt.
        apply ord_sup_in in x_lt as [β [Sβ x_lt]].
        exists (initial_segment (bij_inv (ord_type_init_ord A)
            [β|α_lt β Sβ])).
        split.
        +   exists [β|Sβ]; cbn.
            reflexivity.
        +   unfold initial_segment.
            rewrite (homo_lt2 (f := ord_type_init_ord A)).
            rewrite bij_inv_eq2.
            rewrite <- set_type_lt.
            exact x_lt.
    }
    rewrite eq; clear eq.
    apply countable_union_countable.
    -   unfold small_set_to_card in S_count.
        rewrite_ex_val X [f f_bij].
        apply (trans2 S_count).
        unfold le at 1; equiv_simpl.
        exists (λ T : set_type (λ _, _), bij_inv f (ex_val [|T])).
        split.
        intros T1 T2.
        rewrite_ex_val τ1 τ1_eq.
        rewrite_ex_val τ2 τ2_eq.
        intros eq.
        apply set_type_eq.
        rewrite τ1_eq, τ2_eq.
        clear T1 T2 τ1_eq τ2_eq.
        apply (f_equal f) in eq.
        do 2 rewrite bij_inv_eq2 in eq.
        subst τ2.
        reflexivity.
    -   intros T [[B SB] T_eq]; subst T; cbn.
        apply (trans2 (α_count B SB)).
        equiv_get_value B.
        unfold ord_to_card, le; equiv_simpl.
        assert (∀ x, initial_segment (bij_inv (ord_type_init_ord A)
            [to_ord B | α_lt (to_ord B) SB]) x →
            [ord_type_init_ord A x|] < to_ord B) as x_lt.
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

Theorem ord_initial_countable :
    ∀ α, ord_countable α → small_set_to_card _ (ord_initial_small α) ≤ |nat|.
Proof.
    intros A.
    equiv_get_value A.
    unfold ord_countable, ord_to_card; equiv_simpl.
    rewrite (small_set_to_card_eq _ (ord_initial_small (to_ord A)) A
        (ord_type_init_ord A) (ord_type_init_ord_bij A)).
    trivial.
Qed.

Theorem ord_f_sup_countable : ∀ α f,
    ord_countable α → (∀ β, ord_countable (f β)) →
    ord_countable (ord_f_sup α f).
Proof.
    intros α f α_count β_count.
    apply ord_sup_countable.
    -   apply (trans2 (ord_initial_countable α α_count)).
        unfold small_set_to_card.
        rewrite_ex_val X [g g_bij].
        rewrite_ex_val Y [h h_bij].
        unfold le; equiv_simpl.
        exists (λ x, bij_inv h (ex_val [|g x])).
        split.
        intros a b eq.
        rewrite_ex_val β β_eq.
        rewrite_ex_val γ γ_eq.
        pose proof (bij_inv_bij h).
        apply inj in eq.
        subst γ.
        rewrite <- γ_eq in β_eq.
        rewrite set_type_eq in β_eq.
        apply inj in β_eq.
        exact β_eq.
    -   intros β [γ]; subst β.
        apply β_count.
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

Theorem ord_normal_countable (f : ord → ord) `{OrdNormal f} :
    ord_countable (f 0) →
    (∀ α, ord_countable (f α) → ord_countable (f (ord_suc α))) →
    ∀ α, ord_countable α → ord_countable (f α).
Proof.
    intros zero_count suc_count α α_count.
    induction α as [|α IHα|α α_lim IHα] using ord_induction.
    -   exact zero_count.
    -   apply suc_count.
        apply IHα.
        apply (ord_countable_lt _ _ α_count).
        apply ord_lt_suc.
    -   rewrite (ord_normal) by exact α_lim.
        apply ord_f_sup_countable; [>exact α_count|].
        intros [δ δ_lt].
        apply (IHα δ δ_lt).
        apply (ord_countable_lt _ _ α_count).
        exact δ_lt.
Qed.

Theorem ord_countable_plus : ∀ α β,
    ord_countable α → ord_countable β → ord_countable (α + β).
Proof.
    intros α β α_count β_count.
    pose proof (ord_plus_normal α).
    apply (ord_normal_countable (plus α)).
    -   rewrite plus_rid.
        exact α_count.
    -   intros δ αδ_count.
        rewrite ord_plus_suc.
        apply ord_countable_suc.
        exact αδ_count.
    -   exact β_count.
Qed.

Theorem ord_countable_mult : ∀ α β,
    ord_countable α → ord_countable β → ord_countable (α * β).
Proof.
    intros α β α_count β_count.
    pose proof (ord_mult_normal α).
    apply (ord_normal_countable (mult α)).
    -   rewrite mult_ranni.
        apply zero_ord_countable.
    -   intros δ αδ_count.
        rewrite ord_mult_suc.
        apply ord_countable_plus; [>|exact α_count].
        exact αδ_count.
    -   exact β_count.
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
    pose proof (ord_pow_normal α α_nz).
    apply (ord_normal_countable (ord_pow α)).
    -   rewrite ord_pow_zero.
        apply one_ord_countable.
    -   intros δ αδ_count.
        rewrite ord_pow_suc.
        apply ord_countable_mult; [>|exact α_count].
        exact αδ_count.
    -   exact β_count.
Qed.

Fixpoint power_tower (α : ord) (n : nat) :=
    match n with
    | nat_zero => 1
    | nat_suc n' => α ^ (power_tower α n')
    end.

Definition ε0 := ord_f_sup ω (λ n, power_tower ω (ex_val (ord_lt_ω [n|] [|n]))).

Theorem ω_ε0 : ω ^ ε0 = ε0.
Proof.
    unfold ε0.
    rewrite ord_pow_sup by apply ω_lim.
    apply antisym; apply ord_f_sup_leq_sup.
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
    apply ord_f_sup_countable.
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

Theorem ε0_least : ∀ α, ω ^ α = α → ε0 ≤ α.
Proof.
    intros α α_eq.
    unfold ε0.
    apply ord_f_sup_least.
    intros [n' n'_lt]; cbn.
    rewrite_ex_val n n_eq; subst n'.
    clear n'_lt.
    nat_induction n.
    -   unfold zero, power_tower; cbn.
        apply ord_pos_one.
        intros contr; subst.
        rewrite ord_pow_zero in α_eq.
        symmetry in α_eq; contradiction (ord_not_trivial α_eq).
    -   cbn.
        rewrite <- α_eq.
        apply ord_pow_le; [>apply ω_lim|].
        exact IHn.
Qed.

Open Scope card_scope.

Theorem ord_normal_family_fixed_set_card {X} : ∀ (S : X → Prop) Ss f α,
    small_set_to_card (ord_normal_family_fixed_set S f α)
        (ord_normal_family_fixed_small S Ss f α) ≤
        |list (ex_val (small_bij_ex S Ss))|.
Proof.
    intros S Ss f α.
    rewrite_ex_val Y [g g_bij].
    unfold ord_normal_family_fixed_set.
    pose (h (β : set_type (ord_normal_family_fixed_set S f α)) :=
        list_image (bij_inv g) (ex_val [|β])).
    apply (small_set_to_card_leq _ _ _ h).
    unfold h.
    split.
    intros [a a_in] [b b_in]; cbn.
    rewrite_ex_val al a_eq.
    rewrite_ex_val bl b_eq.
    intros eq.
    apply set_type_eq; cbn.
    subst a b.
    apply (f_equal (list_image g)) in eq.
    do 2 rewrite list_image_comp in eq.
    assert ((λ x, g (bij_inv g x)) = identity) as f_eq.
    {
        functional_intros x.
        apply bij_inv_eq2.
    }
    rewrite f_eq in eq.
    assert (∀ l : list (set_type S), list_image identity l = l) as l_eq.
    {
        intros l.
        induction l as [|a l].
        -   apply list_image_end.
        -   rewrite list_image_add.
            rewrite IHl.
            reflexivity.
    }
    do 2 rewrite l_eq in eq.
    subst bl.
    reflexivity.
Qed.

Lemma small_set_list_countable {X} : ∀ (S : X → Prop) Ss,
    small_set_to_card S Ss ≤ |nat| →
    |list (ex_val (small_bij_ex S Ss))| ≤ |nat|.
Proof.
    intros S Ss S_count.
    rewrite_ex_val Y [f f_bij].
    assert (|Y| ≤ |nat|) as Y_count.
    {
        apply (trans2 S_count).
        unfold small_set_to_card.
        rewrite_ex_val Z [g g_bij].
        unfold le; equiv_simpl.
        exists (λ y, (bij_inv g (f y))).
        apply inj_comp.
        -   apply f_bij.
        -   apply bij_inv_bij.
    }
    classic_case (|Y| = |nat|) as [Y_eq|Y_neq].
    -   rewrite Y_eq in Y_count.
        rewrite <- Y_eq in Y_count at 2.
        rewrite infinite_list_card by exact Y_count.
        rewrite Y_eq.
        apply refl.
    -   classic_case (inhabited Y) as [[y]|y_nex].
        +   rewrite (finite_list_card y) by (split; assumption).
            apply refl.
        +   rewrite empty_list_card by exact y_nex.
            rewrite <- (homo_one (f := from_nat)).
            apply nat_lt_card.
Qed.

Theorem ord_normal_family_fixed_countable {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    small_set_to_card S Ss ≤ |nat| →
    (∀ x α, ord_countable α → ord_countable (f x α)) →
    ∀ α, ord_countable α → ord_countable (ord_normal_family_fixed S Ss f α).
Proof.
    intros S Ss f S_count f_count α α_count.
    unfold ord_normal_family_fixed.
    apply ord_sup_countable.
    -   apply (trans (ord_normal_family_fixed_set_card _ _ _ _ )).
        apply (small_set_list_countable _ _ S_count).
    -   intros δ [l]; subst δ.
        induction l as [|[δ Sδ] l IHl].
        +   rewrite list_image_end, rfold_end.
            exact α_count.
        +   rewrite list_image_add, rfold_add.
            apply f_count.
            exact IHl.
Qed.

Theorem ord_family_derivative_countable {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    small_set_to_card S Ss ≤ |nat| →
    (∀ x α, ord_countable α → ord_countable (f x α)) →
    ∀ α, ord_countable α → ord_countable (ord_family_derivative S Ss f α).
Proof.
    intros S Ss f S_count f_count.
    apply (ord_normal_countable (ord_family_derivative _ _ _)).
    -   rewrite ord_family_derivative_zero.
        apply (ord_normal_family_fixed_countable _ _ _ S_count f_count).
        exact zero_ord_countable.
    -   intros α α_count.
        rewrite ord_family_derivative_suc.
        apply (ord_normal_family_fixed_countable _ _ _ S_count f_count).
        apply ord_countable_suc.
        exact α_count.
Qed.

Theorem ord_derivative_countable : ∀ f : OrdNormalFunction,
    (∀ α, ord_countable α → ord_countable (f α)) →
    ∀ α, ord_countable α → ord_countable (ord_derivative f α).
Proof.
    intros f f_count α α_count.
    apply ord_family_derivative_countable.
    -   unfold small_set_to_card.
        rewrite_ex_val X [g g_bij].
        unfold le; equiv_simpl.
        exists (λ _, 0).
        split.
        intros a b eq.
        apply (inj (f := g)).
        pose proof [|g a] as a_eq.
        pose proof [|g b] as b_eq.
        cbn in *.
        rewrite ord_suc_zero_one in a_eq, b_eq.
        apply ord_lt_one_eq in a_eq, b_eq.
        apply set_type_eq.
        rewrite <- a_eq, <- b_eq.
        reflexivity.
    -   intros _.
        apply f_count.
    -   exact α_count.
Qed.

Close Scope card_scope.
Close Scope ord_scope.
