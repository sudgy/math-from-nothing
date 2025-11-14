Require Import init.

Require Export ord_nat.
Require Import set_induction.
Require Import list.

Definition ord_family_derivative_base {X} (S : X → Prop) (Ss : small S)
    (f : set_type S → OrdNormalFunction) : ord → ord :=
    make_ord_normal
        (ord_normal_family_fixed S Ss f 0)
        (λ α gα, ord_normal_family_fixed S Ss f (ord_suc gα)).

Lemma ord_family_derivative_base_zero {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    ord_family_derivative_base S Ss f 0 =
    ord_normal_family_fixed S Ss f 0.
Proof.
    intros S Ss f.
    apply make_ord_normal_zero.
Qed.

Lemma ord_family_derivative_base_suc {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    ∀ α, ord_family_derivative_base S Ss f (ord_suc α) =
    ord_normal_family_fixed S Ss f
        (ord_suc (ord_family_derivative_base S Ss f α)).
Proof.
    intros S Ss f.
    apply make_ord_normal_suc.
Qed.

Lemma ord_family_derivative_normal {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    OrdNormal (ord_family_derivative_base S Ss f).
Proof.
    intros S Ss f.
    apply make_ord_normal_lim.
Qed.

Lemma ord_family_derivative_base_increasing {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    ∀ α, ord_family_derivative_base S Ss f α <
         ord_family_derivative_base S Ss f (ord_suc α).
Proof.
    intros S Ss f α.
    rewrite ord_family_derivative_base_suc.
    apply (lt_le_trans2 (ord_normal_family_fixed_leq _ _ _ _)).
    apply ord_lt_suc.
Qed.

Lemma ord_family_derivative_le {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    HomomorphismLe (ord_family_derivative_base S Ss f).
Proof.
    intros S Ss f.
    apply make_ord_normal_le.
    intros α.
    apply ord_family_derivative_base_increasing.
Qed.

Lemma ord_family_derivative_inj {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    Injective (ord_family_derivative_base S Ss f).
Proof.
    intros S Ss f.
    apply make_ord_normal_inj.
    intros α.
    apply ord_family_derivative_base_increasing.
Qed.

Definition ord_family_derivative
    {X} (S : X → Prop) Ss (f : set_type S → OrdNormalFunction)
    : OrdNormalFunction :=
    make_ord_normal_function
        (ord_family_derivative_base S Ss f)
        (ord_family_derivative_normal S Ss f)
        (ord_family_derivative_le S Ss f)
        (ord_family_derivative_inj S Ss f).
Arguments ord_family_derivative : simpl never.

Theorem ord_family_derivative_zero {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    ord_family_derivative S Ss f 0 =
    ord_normal_family_fixed S Ss f 0.
Proof.
    apply ord_family_derivative_base_zero.
Qed.

Theorem ord_family_derivative_suc {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    ∀ α, ord_family_derivative S Ss f (ord_suc α) =
    ord_normal_family_fixed S Ss f
        (ord_suc (ord_family_derivative S Ss f α)).
Proof.
    apply ord_family_derivative_base_suc.
Qed.

Theorem ord_family_derivative_lim {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    ∀ γ, lim_ord γ → ord_family_derivative S Ss f γ =
    ord_f_sup γ (λ δ, ord_family_derivative S Ss f [δ|]).
Proof.
    intros S Ss f.
    apply ord_normal.
Qed.

Theorem ord_family_derivative_fixed {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    ∀ x α,
    f x (ord_family_derivative S Ss f α) = ord_family_derivative S Ss f α.
Proof.
    intros S Ss f x α.
    induction α as [|α _ | α α_lim IHα] using ord_induction.
    -   rewrite ord_family_derivative_zero.
        apply ord_normal_family_fixed_eq.
    -   rewrite ord_family_derivative_suc.
        apply ord_normal_family_fixed_eq.
    -   rewrite ord_family_derivative_lim by exact α_lim.
        rewrite (ord_normal_f_sup (f x)).
        2: apply α_lim.
        apply ord_f_sup_f_eq.
        intros δ.
        apply IHα.
        exact [|δ].
Qed.

Theorem ord_family_derivative_lim_eq {X} :
    ∀ (S : X → Prop) Ss (f : set_type S → OrdNormalFunction),
    ∀ γ, lim_ord γ → ord_family_derivative S Ss f γ =
    ord_normal_family_fixed S Ss f (ord_family_derivative S Ss f γ).
Proof.
    intros S Ss f γ γ_lim.
    apply antisym.
    -   rewrite ord_family_derivative_lim at 1 by exact γ_lim.
        apply ord_f_sup_least.
        intros [δ δ_lt]; cbn.
        apply (trans2 (ord_normal_family_fixed_leq _ _ _ _)).
        apply homo_lt.
        exact δ_lt.
    -   apply ord_normal_family_fixed_least.
        1: apply refl.
        intros x.
        apply ord_family_derivative_fixed.
Qed.

Definition ord_derivative (f : OrdNormalFunction) : OrdNormalFunction :=
    ord_family_derivative _ (ord_initial_small (ord_suc 0)) (λ _, f).
Arguments ord_derivative : simpl never.

Theorem ord_derivative_zero : ∀ f, ord_derivative f 0 = ord_normal_fixed f 0.
Proof.
    intros f.
    apply ord_family_derivative_zero.
Qed.

Theorem ord_derivative_suc : ∀ f α,
    ord_derivative f (ord_suc α) =
    ord_normal_fixed f (ord_suc (ord_derivative f α)).
Proof.
    intros f α.
    apply ord_family_derivative_suc.
Qed.

Theorem ord_derivative_lim : ∀ f γ, lim_ord γ →
    ord_derivative f γ = ord_f_sup γ (λ δ, ord_derivative f [δ|]).
Proof.
    intros f.
    apply ord_family_derivative_lim.
Qed.

Theorem ord_derivative_fixed : ∀ (f : OrdNormalFunction) α,
    f (ord_derivative f α) = ord_derivative f α.
Proof.
    intros f α.
    unfold ord_derivative.
    rewrite <- ord_family_derivative_fixed at 2; [>reflexivity|].
    exists 0.
    apply ord_lt_suc.
Qed.

Theorem ord_derivative_lim_eq : ∀ f γ, lim_ord γ →
    ord_derivative f γ =
    ord_normal_fixed f (ord_derivative f γ).
Proof.
    intros f.
    apply ord_family_derivative_lim_eq.
Qed.
