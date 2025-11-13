Require Import init.

Require Export ord_derivative.
Require Export ord_countable.
Require Import card_list.
Require Import set_induction.

Open Scope ord_scope.

Lemma ω_gt_1 : 1 < ω.
Proof.
    rewrite <- homo_one.
    apply nat_lt_ω.
Qed.

Definition ω_pow := make_ord_normal_function
    (ord_pow ω)
    (ord_pow_normal ω (land ω_lim))
    (ord_pow_homo_le ω (land ω_lim))
    (ord_pow_homo_inj ω ω_gt_1).

Definition veblen (α : ord) : OrdNormalFunction :=
    ex_val (ord_recursion
        ω_pow
        (λ _, ord_derivative)
        (λ β f, ord_family_derivative _ (ord_initial_small β) f)
    ) α.


Theorem veblen_zero : veblen 0 = ω_pow.
Proof.
    unfold veblen.
    rewrite_ex_val φ φ_eq.
    apply φ_eq.
Qed.

Theorem veblen_suc : ∀ α, veblen (ord_suc α) = ord_derivative (veblen α).
Proof.
    intros α.
    unfold veblen.
    rewrite_ex_val φ φ_eq.
    apply φ_eq.
Qed.

Theorem veblen_lim : ∀ α, lim_ord α →
    veblen α = ord_family_derivative _ (ord_initial_small α) (λ δ, veblen [δ|]).
Proof.
    intros α.
    unfold veblen.
    rewrite_ex_val φ φ_eq.
    apply φ_eq.
Qed.

Theorem veblen_zero_eq : ∀ α, veblen 0 α = ω ^ α.
Proof.
    intros α.
    rewrite veblen_zero.
    reflexivity.
Qed.

Theorem veblen_ε0 : veblen 1 0 = ε0.
Proof.
    rewrite <- ord_suc_zero_one.
    rewrite veblen_suc.
    rewrite veblen_zero.
    rewrite ord_derivative_zero.
    apply antisym.
    -   apply ord_normal_fixed_least.
        +   apply all_pos.
        +   apply ω_ε0.
    -   order_contradiction ltq.
        unfold ε0 in ltq.
        apply ord_f_sup_in in ltq as [[n' n'_lt] ltq]; cbn in ltq.
        rewrite_ex_val n n_eq; subst n'.
        rewrite <- nle_lt in ltq.
        apply ltq; clear ltq.
        clear n'_lt.
        nat_induction n.
        +   unfold zero at 1; cbn.
            rewrite <- ord_suc_zero_one.
            rewrite ord_le_suc_lt.
            apply all_pos2.
            intros contr.
            pose proof (ord_normal_fixed_eq ω_pow 0) as eq.
            rewrite <- contr in eq.
            cbn in eq.
            rewrite ord_pow_zero in eq.
            symmetry in eq.
            contradiction (ord_not_trivial eq).
        +   cbn.
            apply (ord_pow_le ω _ _ (land ω_lim)) in IHn.
            pose proof (ord_normal_fixed_eq ω_pow 0) as eq.
            cbn in eq.
            rewrite eq in IHn.
            exact IHn.
Qed.

Theorem veblen_suc_eq : ∀ α ζ,
    veblen α (veblen (ord_suc α) ζ) = veblen (ord_suc α) ζ.
Proof.
    intros α ζ.
    rewrite veblen_suc.
    apply ord_derivative_fixed.
Qed.

Lemma veblen_gt_eq_nat : ∀ α ζ n,
    veblen α (veblen (iterate_func ord_suc (nat_suc n) α) ζ) =
    veblen (iterate_func ord_suc (nat_suc n) α) ζ.
Proof.
    intros α ζ n.
    revert α ζ.
    nat_induction n; intros.
    -   unfold one; cbn.
        apply veblen_suc_eq.
    -   cbn in *.
        rewrite <- veblen_suc_eq at 1.
        rewrite IHn.
        rewrite veblen_suc_eq.
        reflexivity.
Qed.

Theorem veblen_gt_eq : ∀ α β, α < β → ∀ ζ, veblen α (veblen β ζ) = veblen β ζ.
Proof.
    intros α β ltq ζ.
    classic_case (∃ n, iterate_func ord_suc n α = β) as [n_ex|n_nex].
    -   destruct n_ex as [n eq]; subst β.
        nat_destruct n.
        {
            unfold zero in ltq; cbn in ltq.
            contradiction (irrefl _ ltq).
        }
        apply veblen_gt_eq_nat.
    -   rewrite not_ex in n_nex.
        pose proof (ord_near_lim_lt _ _ ltq n_nex) as γ_gt.
        pose proof (ord_near_lim_lim _ _ ltq n_nex) as γ_lim.
        rewrite <- (ord_near_lim_eq β).
        rewrite <- (ord_near_lim_eq β) in ltq.
        remember (ord_near_lim_n β) as n; clear Heqn.
        revert ζ.
        nat_induction n; intros.
        +   unfold zero; cbn.
            rewrite (veblen_lim _ γ_lim).
            apply (ord_family_derivative_fixed _ _ (λ δ, veblen [δ|]) [α|ltq]).
        +   prove_parts IHn.
            {
                apply (lt_le_trans γ_gt).
                clear.
                nat_induction n.
                -   apply refl.
                -   apply (trans IHn).
                    apply ord_le_suc.
            }
            cbn.
            rewrite <- veblen_suc_eq at 1.
            rewrite IHn.
            apply veblen_suc_eq.
Qed.

Theorem veblen_le : HomomorphismLe (λ α, veblen α 0).
Proof.
    split.
    intros α β leq.
    classic_case (α = β) as [eq|neq].
    1: subst; apply refl.
    rewrite <- (veblen_gt_eq _ _ (make_and leq neq)).
    apply homo_le.
    apply all_pos.
Qed.

Theorem veblen_inj : Injective (λ α, veblen α 0).
Proof.
    split.
    assert (∀ α β, veblen α 0 = veblen β 0 → α ≤ β → α = β) as wlog.
    {
        intros α β eq leq.
        classic_contradiction neq.
        rewrite <- (veblen_gt_eq _ _ (make_and leq neq)) in eq.
        apply inj in eq.
        clear α leq neq.
        induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
        -   rewrite veblen_zero in eq.
            cbn in eq.
            rewrite ord_pow_zero in eq.
            contradiction (ord_not_trivial eq).
        -   pose proof eq as eq2.
            apply (f_equal (veblen β)) in eq2.
            rewrite veblen_suc_eq in eq2.
            rewrite eq2 in IHβ.
            exact (IHβ eq).
        -   pose proof eq as eq2.
            apply (f_equal (veblen 0)) in eq2.
            rewrite veblen_gt_eq in eq2.
            2: apply all_pos2; apply β_lim.
            apply (IHβ 0).
            1: apply all_pos2; apply β_lim.
            rewrite eq2.
            exact eq.
    }
    intros α β eq.
    destruct (connex α β) as [leq|leq].
    -   exact (wlog _ _ eq leq).
    -   symmetry.
        symmetry in eq.
        exact (wlog _ _ eq leq).
Qed.

Theorem veblen_normal : OrdNormal (λ α, veblen α 0).
Proof.
    split.
    intros α α_lim.
    rewrite veblen_lim by exact α_lim.
    rewrite ord_family_derivative_zero.
    apply antisym.
    -   apply ord_normal_family_fixed_least.
        1: apply all_pos.
        intros [δ δ_lt]; cbn.
        rewrite (ord_normal_f_sup (veblen δ)).
        2: {
            intros contr; subst.
            contradiction (not_neg δ_lt).
        }
        apply antisym; apply ord_sup_leq_sup.
        +   intros β' [[β β_lt]]; subst; cbn.
            unfold image.
            classic_case (δ < β) as [ltq|leq].
            *   exists (veblen β 0).
                split.
                --  exists [β|β_lt].
                    reflexivity.
                --  rewrite veblen_gt_eq by exact ltq.
                    apply refl.
            *   rewrite nlt_le in leq.
                exists (veblen (ord_suc δ) 0).
                split.
                --  apply (ord_lim_suc _ α α_lim) in δ_lt.
                    exists [ord_suc δ | δ_lt].
                    reflexivity.
                --  pose proof (veblen_le).
                    apply (le_lt_trans2 (ord_lt_suc δ)) in leq.
                    pose proof (homo_le (HomomorphismLe := H) _ _ (land leq))
                        as leq2.
                    cbn in leq2.
                    apply (homo_le (f := veblen δ)) in leq2.
                    rewrite (veblen_gt_eq δ (ord_suc δ)) in leq2
                        by apply ord_lt_suc.
                    exact leq2.
        +   intros β' [[β β_lt]]; subst; cbn.
            unfold image.
            exists (veblen δ (veblen β 0)).
            split.
            1: exists [β|β_lt]; reflexivity.
            apply (ord_normal_le (veblen δ)).
    -   apply ord_f_sup_least.
        intros [δ δ_lt]; cbn.
        unfold ord_normal_family_fixed.
        apply ord_sup_ge.
        exists [[δ|δ_lt]]; cbn.
        rewrite list_image_single.
        rewrite rfold_add, rfold_end.
        reflexivity.
Qed.

Theorem ord_normal_fixed_sup_eq : ∀ (f : OrdNormalFunction) α,
    ord_normal_fixed f α =
    ord_f_sup ω (λ n, iterate_func f (ex_val (ord_lt_ω [n|] [|n])) α).
Proof.
    intros f α.
    unfold ord_normal_fixed.
    unfold ord_normal_family_fixed.
    apply antisym; apply ord_sup_leq_sup.
    -   intros δ [l δ_eq].
        exists δ.
        split; [>|apply refl].
        exists [from_nat (list_size l)|nat_lt_ω (list_size l)].
        rewrite δ_eq; cbn.
        rewrite_ex_val n n_eq.
        apply inj in n_eq.
        subst n.
        clear δ_eq.
        induction l.
        +   reflexivity.
        +   rewrite list_size_add, list_image_add, rfold_add.
            cbn.
            rewrite IHl.
            reflexivity.
    -   intros δ [n'].
        rewrite_ex_val n n_eq.
        clear n' n_eq.
        subst δ.
        exists (iterate_func f n α).
        split; [>|apply refl].
        unfold ord_normal_family_fixed_set.
        exists (list_constant [0|ord_lt_suc 0] n).
        nat_induction n.
        +   reflexivity.
        +   rewrite list_constant_suc, list_image_add, rfold_add.
            cbn.
            rewrite <- IHn.
            reflexivity.
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

Theorem veblen_countable : ∀ α β,
    ord_countable α → ord_countable β → ord_countable (veblen α β).
Proof.
    intros α β α_count β_count.
    revert β β_count.
    induction α as [|α IHα|α α_lim IHα] using ord_induction; intros.
    -   rewrite veblen_zero_eq.
        apply ord_countable_pow.
        +   exact omega_countable.
        +   exact β_count.
    -   rewrite veblen_suc.
        revert β β_count.
        apply (ord_normal_countable (ord_derivative (veblen α))).
        +   rewrite ord_derivative_zero.
            rewrite ord_normal_fixed_sup_eq.
            apply ord_f_sup_countable.
            1: exact omega_countable.
            intros [n' n_lt]; cbn.
            rewrite_ex_val n n_eq.
            clear n' n_lt n_eq.
            nat_induction n.
            *   unfold zero at 1; cbn.
                exact zero_ord_countable.
            *   cbn.
                apply IHα.
                2: exact IHn.
                apply (ord_countable_lt _ _ α_count).
                apply ord_lt_suc.
        +   intros β β_count.
            rewrite ord_derivative_suc.
            rewrite ord_normal_fixed_sup_eq.
            apply ord_f_sup_countable.
            1: exact omega_countable.
            intros [n' n'_lt]; cbn.
            rewrite_ex_val n n_eq.
            clear n' n'_lt n_eq.
            nat_induction n.
            *   unfold zero; cbn.
                apply ord_countable_suc.
                exact β_count.
            *   cbn.
                apply IHα.
                --  apply (ord_countable_lt _ _ α_count).
                    apply ord_lt_suc.
                --  exact IHn.
    -   assert (|list (ex_val (small_bij_ex (λ δ, δ < α)
            (ord_initial_small α)))| ≤ |nat|) as list_card.
        {
            rewrite_ex_val Y [f f_bij].
            assert (|Y| ≤ |nat|) as Y_count.
            {
                equiv_get_value α.
                rename α into A.
                apply (trans2 α_count).
                unfold ord_to_card; equiv_simpl.
                unfold le; equiv_simpl.
                pose proof (ord_type_init_ord_bij A).
                exists (λ y, bij_inv (ord_type_init_ord A) (f y)).
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
        }
        rewrite veblen_lim by exact α_lim.
        revert β β_count.
        apply (ord_normal_countable (ord_family_derivative _ _ _)).
        +   rewrite ord_family_derivative_zero.
            unfold ord_normal_family_fixed.
            apply ord_sup_countable.
            *   apply (trans (ord_normal_family_fixed_set_card _ _ _ _)).
                exact list_card.
            *   intros δ [l]; subst δ.
                induction l as [|[δ δ_lt] l IHl].
                --  rewrite list_image_end, rfold_end.
                    apply zero_ord_countable.
                --  rewrite list_image_add, rfold_add; cbn.
                    apply IHα.
                    2: apply (ord_countable_lt _ _ α_count).
                    1, 2: exact δ_lt.
                    exact IHl.
        +   intros β β_count.
            rewrite ord_family_derivative_suc.
            unfold ord_normal_family_fixed.
            apply ord_sup_countable.
            *   apply (trans (ord_normal_family_fixed_set_card _ _ _ _)).
                exact list_card.
            *   intros δ [l]; subst δ.
                induction l as [|[δ δ_lt] l IHl].
                --  rewrite list_image_end, rfold_end.
                    apply ord_countable_suc.
                    exact β_count.
                --  rewrite list_image_add, rfold_add; cbn.
                    apply IHα.
                    2: apply (ord_countable_lt _ _ α_count).
                    1, 2: exact δ_lt.
                    exact IHl.
Qed.

Definition veblen2 : OrdNormalFunction := make_ord_normal_function
    _ veblen_normal veblen_le veblen_inj.

Definition feferman_schütte := ord_normal_fixed veblen2 0.

Theorem feferman_schütte_fixed : veblen feferman_schütte 0 = feferman_schütte.
Proof.
    apply (ord_normal_fixed_eq veblen2).
Qed.

Theorem feferman_schütte_least : ∀ α, veblen α 0 = α → feferman_schütte ≤ α.
Proof.
    intros α α_eq.
    apply ord_normal_fixed_least.
    -   apply all_pos.
    -   exact α_eq.
Qed.

Theorem feferman_schütte_countable : ord_countable feferman_schütte.
Proof.
    unfold feferman_schütte.
    rewrite ord_normal_fixed_sup_eq.
    apply ord_f_sup_countable.
    1: exact omega_countable.
    intros [n' n'_lt]; cbn.
    rewrite_ex_val n n_eq; subst n'; clear n'_lt.
    nat_induction n.
    -   unfold zero at 2; cbn.
        apply zero_ord_countable.
    -   cbn.
        apply veblen_countable.
        +   exact IHn.
        +   apply zero_ord_countable.
Qed.

Close Scope card_scope.
Close Scope ord_scope.
