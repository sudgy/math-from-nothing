Require Import init.

Require Export ord_limit.
Require Import nat.

Theorem ord_normal_recursion : ∀
    (f0 : ord)
    (f_suc : ord → ord → ord),
    ∃ g : ord → ord,
        (g 0 = f0) ∧
        (∀ α, g (ord_suc α) = f_suc α (g α)) ∧
        (∀ α, lim_ord α → g α = ord_sup α (λ β, g [β|])).
Proof.
    intros f0 f_suc.
    pose (f_lim α (h : set_type (λ β, β < α) → ord) := ord_sup α h).
    exists (ex_val (ord_recursion f0 f_suc f_lim)).
    rewrite_ex_val g [g0 [g_suc g_lim]].
    split; [>exact g0|].
    split; [>exact g_suc|].
    unfold f_lim in g_lim.
    exact g_lim.
Qed.

Definition ord_normal (f : ord → ord) :=
    Injective f ∧ HomomorphismLe f ∧
    ∀ α, lim_ord α → f α = ord_sup α (λ β, f [β|]).

Section MakeOrdNormal.

Context (f0 : ord) (f_suc : ord → ord → ord).

Definition make_ord_normal := ex_val (ord_normal_recursion f0 f_suc).
Local Notation "'f'" := make_ord_normal.

Lemma make_ord_normal_zero : f 0 = f0.
Proof.
    apply (ex_proof (ord_normal_recursion f0 f_suc)).
Qed.

Lemma make_ord_normal_suc : ∀ α, f (ord_suc α) = f_suc α (f α).
Proof.
    apply (ex_proof (ord_normal_recursion f0 f_suc)).
Qed.

Lemma make_ord_normal_lim : ∀ α, lim_ord α → f α = ord_sup α (λ β, f [β|]).
Proof.
    apply (ex_proof (ord_normal_recursion f0 f_suc)).
Qed.

Context (f_increasing : ∀ α, f α < f (ord_suc α)).

Lemma make_ord_normal_lt_sucs : ∀ α n,
    f α < f (iterate_func ord_suc (nat_suc n) α).
Proof.
    intros α n.
    nat_induction n.
    -   unfold one; cbn.
        apply f_increasing.
    -   apply (trans IHn).
        cbn.
        apply f_increasing.
Qed.

Lemma make_ord_normal_lt_lim : ∀ α β, lim_ord β → α < β → f α < f β.
Proof.
    intros α β β_lim ltq.
    rewrite (make_ord_normal_lim β β_lim).
    apply (lt_le_trans (f_increasing α)).
    apply ord_sup_other_leq.
    intros ε ε_ge.
    assert (ord_suc α < β) as ltq2.
    {
        split.
        -   rewrite ord_le_suc_lt.
            exact ltq.
        -   intros contr.
            apply (rand β_lim).
            exists α.
            symmetry; exact contr.
    }
    exact (ε_ge [ord_suc α|ltq2]).
Qed.

Lemma make_ord_normal_lt : ∀ α β, α < β → make_ord_normal α < make_ord_normal β.
Proof.
    intros α β ltq.
    induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
    -   contradiction (not_neg ltq).
    -   classic_case (α = β) as [eq|neq].
        {
            subst β.
            apply f_increasing.
        }
        rewrite ord_lt_suc_le in ltq.
        classic_case (∀ n, iterate_func ord_suc n α ≠ β) as [β_neq|β_eq].
        +   pose proof (ord_far_lim α β (make_and ltq neq) β_neq)
                as [γ [n [γ_lim [γ_gt β_eq]]]].
            rewrite <- β_eq.
            apply (make_ord_normal_lt_lim _ _ γ_lim) in γ_gt.
            apply (trans γ_gt).
            apply make_ord_normal_lt_sucs.
        +   rewrite not_all in β_eq.
            destruct β_eq as [n β_eq].
            rewrite not_not in β_eq.
            rewrite <- β_eq.
            apply make_ord_normal_lt_sucs.
    -   exact (make_ord_normal_lt_lim α β β_lim ltq).
Qed.

Global Instance make_ord_normal_inj : Injective f.
Proof.
    split.
    intros α β eq.
    destruct (trichotomy α β) as [[ltq|eq']|ltq].
    -   apply make_ord_normal_lt in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
    -   exact eq'.
    -   apply make_ord_normal_lt in ltq.
        rewrite eq in ltq.
        contradiction (irrefl _ ltq).
Qed.

Global Instance make_ord_normal_le : HomomorphismLe f.
Proof.
    split.
    intros α β leq.
    classic_case (α = β) as [eq|neq].
    -   subst; apply refl.
    -   apply make_ord_normal_lt.
        split; assumption.
Qed.

Theorem make_ord_normal_normal : ord_normal f.
Proof.
    split; [>|split].
    -   exact make_ord_normal_inj.
    -   exact make_ord_normal_le.
    -   exact make_ord_normal_lim.
Qed.

End MakeOrdNormal.

Theorem ord_normal_le : ∀ f, ord_normal f → ∀ α, α ≤ f α.
Proof.
    intros f [f_inj [f_le f_lim]] α.
    order_contradiction ltq.
    pose proof (well_ordered (λ β, f β < β)) as β_ex.
    prove_parts β_ex.
    1: exists α; exact ltq.
    destruct β_ex as [β [β_lt β_least]].
    pose proof β_lt as fβ_lt.
    apply (homo_lt (f := f)) in fβ_lt.
    specialize (β_least _ fβ_lt).
    contradiction (irrefl _ (lt_le_trans β_lt β_least)).
Qed.

Theorem ord_normal_sup : ∀ f, ord_normal f →
    ∀ β (g : set_type (λ α, α < β) → ord), 0 ≠ β →
    f (ord_sup β g) = ord_sup β (λ α, f (g α)).
Proof.
    intros f f_norm β g β_nz.
    pose proof f_norm as [f_inj [f_le f_lim]].
    apply antisym.
    -   remember (ord_sup β g) as γ.
        induction γ as [|γ IHγ|γ γ_lim IHγ] using ord_induction.
        +   apply ord_sup_other_leq.
            intros ε ε_ge.
            apply all_pos2 in β_nz.
            specialize (ε_ge [0|β_nz]).
            assert (g [0 | β_nz] = 0) as g_eq.
            {
                apply antisym; [>|apply all_pos].
                rewrite Heqγ.
                apply ord_sup_ge.
            }
            rewrite g_eq in ε_ge.
            exact ε_ge.
        +   clear IHγ.
            assert (∃ δ, g δ = ord_suc γ) as [δ δ_eq].
            {
                classic_contradiction contr.
                rewrite not_ex in contr.
                rewrite Heqγ in contr.
                assert (ord_sup β g = γ) as γ_eq.
                {
                    apply ord_sup_eq.
                    -   intros [α α_lt].
                        rewrite <- ord_lt_suc_le.
                        rewrite Heqγ.
                        split; [>apply ord_sup_ge|].
                        apply contr.
                    -   intros ε ε_ge.
                        apply ord_sucs_le.
                        rewrite Heqγ.
                        apply ord_sup_least.
                        intros α.
                        specialize (ε_ge α).
                        rewrite <- ord_lt_suc_le in ε_ge.
                        apply ε_ge.
                }
                rewrite γ_eq in Heqγ.
                symmetry in Heqγ.
                apply ord_lt_suc in Heqγ.
                exact Heqγ.
            }
            rewrite <- δ_eq.
            apply ord_sup_other_leq.
            intros ε ε_ge.
            apply ε_ge.
        +   clear IHγ.
            subst γ.
            rewrite (f_lim _ γ_lim).
            apply ord_sup_least.
            intros [α α_lt]; cbn.
            assert (∃ ζ, α ≤ g ζ) as [ζ α_leq].
            {
                classic_contradiction contr.
                rewrite <- nle_lt in α_lt.
                apply α_lt.
                apply ord_sup_least.
                intros ζ.
                rewrite not_ex in contr.
                specialize (contr ζ).
                rewrite nle_lt in contr.
                apply contr.
            }
            apply ord_sup_other_leq.
            intros ε ε_ge.
            apply (homo_le (f := f)) in α_leq.
            apply (trans α_leq).
            apply ε_ge.
    -   apply ord_sup_least.
        intros α.
        apply homo_le.
        apply ord_sup_ge.
Qed.

(* The fixed point lemma requires facts about ω which will be proved in ord_nat.
 * Thus, the fixed point lemma will be there instead. *)
