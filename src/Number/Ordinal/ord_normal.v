Require Import init.

Require Export ord_limit.
Require Import nat.
Require Import set_induction.

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

Class OrdNormal (f : ord → ord) := {
    ord_normal : ∀ α, lim_ord α → f α = ord_sup α (λ β, f [β|])
}.

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

Global Instance make_ord_normal_lim : OrdNormal f.
Proof.
    split.
    apply (ex_proof (ord_normal_recursion f0 f_suc)).
Qed.

Context (f_increasing : ∀ α, f α ≤ f (ord_suc α)).

Lemma make_ord_normal_lt_sucs : ∀ α n,
    f α ≤ f (iterate_func ord_suc (nat_suc n) α).
Proof.
    intros α n.
    nat_induction n.
    -   unfold one; cbn.
        apply f_increasing.
    -   apply (trans IHn).
        cbn.
        apply f_increasing.
Qed.

Lemma make_ord_normal_lt_lim : ∀ α β, lim_ord β → α ≤ β → f α ≤ f β.
Proof.
    intros α β β_lim leq.
    classic_case (α = β) as [eq|neq].
    1: subst; apply refl.
    rewrite (ord_normal (f := f) β β_lim).
    apply (trans (f_increasing α)).
    apply ord_sup_other_leq.
    intros ε ε_ge.
    assert (ord_suc α < β) as ltq2.
    {
        split.
        -   rewrite ord_le_suc_lt.
            split; assumption.
        -   intros contr.
            apply (rand β_lim).
            exists α.
            symmetry; exact contr.
    }
    exact (ε_ge [ord_suc α|ltq2]).
Qed.

Local Instance make_ord_normal_le : HomomorphismLe f.
Proof.
    split.
    intros α β leq.
    induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
    -   apply all_neg_eq in leq.
        subst; apply refl.
    -   classic_case (α = ord_suc β) as [eq|neq].
        {
            subst α.
            apply refl.
        }
        pose proof (make_and leq neq : α < ord_suc β) as ltq.
        rewrite ord_lt_suc_le in ltq.
        apply (trans (IHβ ltq)).
        apply f_increasing.
    -   exact (make_ord_normal_lt_lim α β β_lim leq).
Qed.
(*
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
*)

End MakeOrdNormal.

Section MakeOrdNormal2.

Context (f0 : ord) (f_suc : ord → ord → ord).
Local Notation "'f'" := (make_ord_normal f0 f_suc).

Context (f_increasing : ∀ α, f α < f (ord_suc α)).

Local Instance make_ord_normal_inj_le : HomomorphismLe f.
Proof.
    apply make_ord_normal_le.
    intros α.
    apply f_increasing.
Qed.

Local Instance make_ord_normal_inj : Injective f.
Proof.
    split.
    pose proof make_ord_normal_inj_le.
    assert (∀ α β, α < β → f α ≠ f β) as wlog.
    {
        intros α β ltq eq.
        induction β as [|β IHβ|β β_lim IHβ] using ord_induction.
        -   contradiction (not_neg ltq).
        -   clear IHβ.
            specialize (f_increasing β).
            rewrite <- eq in f_increasing.
            rewrite ord_lt_suc_le in ltq.
            apply (homo_le (f := f)) in ltq.
            contradiction (irrefl _ (le_lt_trans ltq f_increasing)).
        -   specialize (f_increasing α).
            rewrite <- ord_le_suc_lt in ltq.
            apply (homo_le (f := f)) in ltq.
            rewrite eq in f_increasing.
            contradiction (irrefl _ (le_lt_trans ltq f_increasing)).
    }
    intros α β eq.
    destruct (trichotomy α β) as [[ltq|eq']|ltq].
    -   contradiction (wlog _ _ ltq eq).
    -   exact eq'.
    -   symmetry in eq.
        contradiction (wlog _ _ ltq eq).
Qed.

End MakeOrdNormal2.

Section OrdNormal.

Context (f : ord → ord) `{
    @HomomorphismLt ord ord _ _ f,
    @HomomorphismLe ord ord _ _ f,
    @Injective ord ord f,
    OrdNormal f
}.

Theorem ord_normal_le : ∀ α, α ≤ f α.
Proof.
    intros α.
    induction α as [α IHα] using transfinite_induction.
    order_contradiction ltq.
    specialize (IHα _ ltq).
    apply homo_le2 in IHα.
    contradiction (irrefl _ (le_lt_trans IHα ltq)).
Qed.

Theorem ord_normal_sup :
    ∀ β (g : set_type (λ α, α < β) → ord), 0 ≠ β →
    f (ord_sup β g) = ord_sup β (λ α, f (g α)).
Proof.
    intros β g β_nz.
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
            rewrite (ord_normal _ γ_lim).
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

End OrdNormal.
