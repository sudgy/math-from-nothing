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
    -   apply ε0_least.
        apply (ord_normal_fixed_eq ω_pow).
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

Lemma veblen_gt_eq_lim : ∀ α β, α < β → lim_ord β →
    ∀ ζ, veblen α (veblen β ζ) = veblen β ζ.
Proof.
    intros α β ltq β_lim ζ.
    rewrite (veblen_lim _ β_lim).
    apply (ord_family_derivative_fixed _ _ (λ δ, veblen [δ|]) [α|ltq]).
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
        nat_destruct n.
        +   unfold zero; cbn.
            apply veblen_gt_eq_lim; assumption.
        +   rewrite <- (veblen_gt_eq_nat _ _ n).
            apply (veblen_gt_eq_lim _ _ γ_gt γ_lim).
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
        pose proof (all_pos β) as leq.
        apply veblen_le in leq.
        rewrite <- eq in leq.
        rewrite veblen_zero_eq in leq.
        rewrite ord_pow_zero in leq.
        rewrite <- nlt_le in leq.
        exact (leq ord_one_pos).
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
        apply antisym; apply ord_f_sup_leq_sup.
        +   intros [β β_lt]; cbn.
            classic_case (δ < β) as [ltq|leq].
            *   exists [β|β_lt].
                rewrite veblen_gt_eq by exact ltq.
                apply refl.
            *   rewrite nlt_le in leq.
                apply (ord_lim_suc _ α α_lim) in δ_lt.
                exists [ord_suc δ|δ_lt]; cbn.
                apply (trans2 (ord_le_suc δ)) in leq.
                apply veblen_le in leq.
                apply (homo_le (f := veblen δ)) in leq.
                rewrite (veblen_gt_eq δ (ord_suc δ)) in leq by apply ord_lt_suc.
                exact leq.
        +   intros [β β_lt]; subst; cbn.
            exists [β|β_lt]; cbn.
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
    -   specialize (IHα (ord_countable_lt _ _ α_count (ord_lt_suc α))).
        rewrite veblen_suc.
        apply ord_derivative_countable; assumption.
    -   rewrite veblen_lim by exact α_lim.
        apply ord_family_derivative_countable.
        +   apply ord_initial_countable.
            exact α_count.
        +   intros [δ δ_lt]; cbn.
            apply (IHα δ δ_lt).
            exact (ord_countable_lt _ α α_count δ_lt).
        +   exact β_count.
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

Close Scope ord_scope.
