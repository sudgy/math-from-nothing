Require Import init.

Require Export ord_limit.
Require Export list.

Require Import nat.
Require Import set_induction.
Require Import well_order.
Require Import order_minmax.

Theorem ord_normal_recursion : ∀
    (f0 : ord)
    (f_suc : ord → ord → ord),
    ∃ g : ord → ord,
        (g 0 = f0) ∧
        (∀ α, g (ord_suc α) = f_suc α (g α)) ∧
        (∀ α, lim_ord α → g α = ord_f_sup α (λ β, g [β|])).
Proof.
    intros f0 f_suc.
    pose (f_lim α (h : set_type (λ β, β < α) → ord) := ord_f_sup α h).
    exists (ex_val (ord_recursion f0 f_suc f_lim)).
    rewrite_ex_val g [g0 [g_suc g_lim]].
    split; [>exact g0|].
    split; [>exact g_suc|].
    unfold f_lim in g_lim.
    exact g_lim.
Qed.

Class OrdNormal (f : ord → ord) := {
    ord_normal : ∀ α, lim_ord α → f α = ord_f_sup α (λ β, f [β|])
}.

Record OrdNormalFunction := make_ord_normal_function {
    ord_normal_f :> ord → ord;
    ord_normal_normal : OrdNormal ord_normal_f;
    ord_normal_homo_le : HomomorphismLe ord_normal_f;
    ord_normal_inj : Injective ord_normal_f;
}.
Global Existing Instances ord_normal_normal ord_normal_homo_le ord_normal_inj.

Theorem ord_normal_function_eq :
    ∀ f g : OrdNormalFunction, (∀ α, f α = g α) → f = g.
Proof.
    intros [f f_normal f_le f_inj] [g g_normal g_le g_inj] eq.
    cbn in eq.
    apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_normal g_normal).
    rewrite (proof_irrelevance f_le g_le).
    rewrite (proof_irrelevance f_inj g_inj).
    reflexivity.
Qed.

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
    apply ord_f_sup_other_leq.
    intros ε ε_ge.
    apply (ε_ge [α|make_and leq neq]).
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

Theorem ord_normal_sup : ∀ S Ss, (∃ x, S x) →
    f (ord_sup S Ss) = ord_sup _ (small_image_under f S Ss).
Proof.
    intros S Ss S_nempty.
    apply antisym.
    -   remember (ord_sup S Ss) as γ.
        induction γ as [|γ IHγ|γ γ_lim IHγ] using ord_induction.
        +   apply ord_sup_other_leq.
            intros ε ε_ge.
            apply ε_ge.
            exists 0.
            split; [>|reflexivity].
            destruct S_nempty as [x Sx].
            pose proof (ord_sup_zero S Ss Heqγ x Sx); subst x.
            exact Sx.
        +   clear IHγ.
            symmetry in Heqγ; apply ord_sup_suc in Heqγ.
            apply ord_sup_ge.
            exists (ord_suc γ).
            split; [>exact Heqγ | reflexivity].
        +   clear IHγ.
            subst γ.
            rewrite (ord_normal _ γ_lim).
            apply ord_f_sup_least.
            intros [α α_lt]; cbn.
            apply ord_sup_in in α_lt as [ζ [Sζ [ζ_ge ζ_neq]]].
            apply ord_sup_other_leq.
            intros ε ε_ge.
            apply (homo_le (f := f)) in ζ_ge.
            apply (trans ζ_ge).
            apply ε_ge.
            exists ζ.
            split; [>exact Sζ|reflexivity].
    -   apply ord_sup_least.
        intros α' [α [Sα]]; subst α'.
        apply homo_le.
        apply ord_sup_ge.
        exact Sα.
Qed.

Theorem ord_normal_f_sup :
    ∀ β (g : set_type (λ α, α < β) → ord), 0 ≠ β →
    f (ord_f_sup β g) = ord_f_sup β (λ α, f (g α)).
Proof.
    intros β g β_nz.
    unfold ord_f_sup.
    rewrite ord_normal_sup.
    2: {
        apply all_pos2 in β_nz.
        exists (g [0|β_nz]).
        exists [0|β_nz].
        reflexivity.
    }
    apply ord_sup_set_eq.
    intros α.
    split.
    -   intros [γ' [[γ]]]; subst.
        exists γ.
        reflexivity.
    -   intros [γ]; subst α.
        exists (g γ).
        split; [>|reflexivity].
        exists γ.
        reflexivity.
Qed.

Theorem ord_normal_lim_ord : ∀ α, lim_ord α → lim_ord (f α).
Proof.
    intros α α_lim.
    rewrite (ord_normal α α_lim).
    split.
    -   intros contr.
        pose proof (ord_f_sup_ge α (λ β, f [β|])) as leq; cbn in leq.
        specialize (leq [ord_suc 0|ord_lim_gt α α_lim]); cbn in leq.
        rewrite <- contr in leq.
        apply (trans (ord_normal_le (ord_suc 0))) in leq.
        rewrite <- nlt_le in leq.
        contradiction (leq (ord_lt_suc _)).
    -   intros [β eq].
        pose proof (ord_f_sup_suc _ _ _ eq) as [[δ δ_lt] δ_eq].
        cbn in δ_eq.
        apply (ord_lim_suc _ _ α_lim) in δ_lt.
        pose proof (ord_f_sup_ge α (λ δ, f [δ|]) [ord_suc δ|δ_lt]) as leq.
        rewrite eq in leq.
        cbn in leq.
        rewrite <- δ_eq in leq.
        rewrite <- nlt_le in leq.
        apply leq.
        apply homo_lt.
        apply ord_lt_suc.
Qed.

End OrdNormal.

Section OrdNormalFamily.

Context {X} (S : X → Prop) (S_small : small S)
    (f : set_type S → OrdNormalFunction) (α : ord).

Definition ord_normal_family_fixed_set (β : ord) :=
    ∃ l : list (set_type S), β = rfold (λ h1 h2, (λ x, h1 (h2 x))) identity
        (list_image (λ x, ord_normal_f (f x)) l) α.

Theorem ord_normal_family_fixed_small : small ord_normal_family_fixed_set.
Proof.
    destruct S_small as [Y [g g_sur]].
    exists (list Y).
    assert (∀ l : list Y, ord_normal_family_fixed_set
        (rfold (λ h1 h2, (λ x, h1 (h2 x))) identity
        (list_image (λ y, ord_normal_f (f (g y))) l) α)) as l_in.
    {
        intros l.
        exists (list_image g l).
        rewrite list_image_comp.
        reflexivity.
    }
    exists (λ y, [_|l_in y]).
    split.
    intros [y [l y_eq]].
    exists (list_image (λ x, ex_val (sur g x)) l).
    apply set_type_eq; cbn.
    subst y.
    apply f_equal2; [>|reflexivity].
    rewrite list_image_comp.
    induction l as [|x l].
    -   do 2 rewrite list_image_end.
        reflexivity.
    -   do 2 rewrite list_image_add.
        rewrite IHl.
        rewrite_ex_val y y_eq.
        rewrite y_eq.
        reflexivity.
Qed.

Definition ord_normal_family_fixed := ord_sup _ ord_normal_family_fixed_small.

Theorem ord_normal_family_fixed_eq : ∀ x,
    f x ord_normal_family_fixed = ord_normal_family_fixed.
Proof.
    intros x.
    unfold ord_normal_family_fixed.
    rewrite (ord_normal_sup (f x)).
    2: {
        exists α.
        exists [].
        rewrite list_image_end, rfold_end.
        reflexivity.
    }
    apply antisym; apply ord_sup_leq_sup.
    -   intros β' [β [β_in]]; subst β'.
        destruct β_in as [l β_eq].
        exists (f x β).
        split; [>|apply refl].
        exists (x ꞉ l).
        rewrite β_eq.
        rewrite list_image_add, rfold_add.
        reflexivity.
    -   intros β β_in.
        exists (f x β).
        split.
        +   exists β.
            split; [>exact β_in | reflexivity].
        +   apply (ord_normal_le (f x)).
Qed.

Theorem ord_normal_family_fixed_leq : α ≤ ord_normal_family_fixed.
Proof.
    unfold ord_normal_family_fixed.
    apply ord_sup_ge.
    exists [].
    rewrite list_image_end, rfold_end.
    reflexivity.
Qed.

Theorem ord_normal_family_fixed_least : ∀ β, α ≤ β → (∀ x, f x β = β) →
    ord_normal_family_fixed ≤ β.
Proof.
    intros β leq β_eq.
    unfold ord_normal_family_fixed.
    apply ord_sup_least.
    intros γ [l γ_eq]; subst γ.
    induction l as [|x l].
    -   rewrite list_image_end, rfold_end.
        exact leq.
    -   rewrite list_image_add, rfold_add.
        rewrite <- (β_eq x).
        apply homo_le.
        exact IHl.
Qed.

End OrdNormalFamily.

Definition ord_normal_fixed (f : OrdNormalFunction) α
    := ord_normal_family_fixed _ (ord_initial_small (ord_suc 0)) (λ _, f) α.

Theorem ord_normal_fixed_eq : ∀ (f : OrdNormalFunction) α,
    f (ord_normal_fixed f α) = ord_normal_fixed f α.
Proof.
    intros f α.
    unfold ord_normal_fixed.
    rewrite <- ord_normal_family_fixed_eq at 2.
    -   reflexivity.
    -   exists 0.
        apply ord_lt_suc.
Qed.

Theorem ord_normal_fixed_leq : ∀ (f : OrdNormalFunction) α,
    α ≤ ord_normal_fixed f α.
Proof.
    intros f α.
    apply ord_normal_family_fixed_leq.
Qed.

Theorem ord_normal_fixed_least : ∀ (f : OrdNormalFunction) α,
    ∀ β, α ≤ β → f β = β → ord_normal_fixed f α ≤ β.
Proof.
    intros f α β leq β_eq.
    apply ord_normal_family_fixed_least.
    -   exact leq.
    -   intro; exact β_eq.
Qed.
