Require Import init.

Require Export card_base.
Require Import card_order.
Require Import card_plus.
Require Import card_mult.
Require Import set.
Require Import function.
Require Import nat0.

(* begin hide *)
Open Scope card_scope.
(* end hide *)
Lemma card_pow_wd : ∀ A B C D, A ~ B → C ~ D → (C → A) ~ (D → B).
    intros A B C D [f f_bij] [g g_bij].
    pose (g' := bij_inv g g_bij).
    exists (λ h, (λ x, f (h (g' x)))).
    split.
    -   intros h1 h2 eq.
        apply functional_ext.
        intros c.
        pose proof (func_eq _ _ eq) as eq2.
        cbn in eq2.
        specialize (eq2 (g c)).
        rewrite inverse_eq1 in eq2 by apply bij_inv_inv.
        apply f_bij in eq2.
        exact eq2.
    -   intros h.
        pose (f' := bij_inv f f_bij).
        exists (λ c, f' (h (g c))).
        apply functional_ext.
        intros d.
        do 2 rewrite inverse_eq2 by apply bij_inv_inv.
        reflexivity.
Qed.

Definition card_pow := binary_self_op card_pow_wd.
Infix "^" := card_pow : card_scope.

Theorem func_size : ∀ A B, |A → B| = |B| ^ |A|.
    intros A B.
    unfold card_pow; equiv_simpl.
    exists identity.
    apply identity_bijective.
Qed.

Theorem card_pow_0 : ∀ κ, κ ^ 0 = 1.
    intros A.
    equiv_get_value A.
    unfold zero, one; cbn.
    unfold nat0_to_card, card_pow; equiv_simpl.
    exists (λ x, [0|nat0_0_lt_1]).
    assert (set_type (λ x : nat0, x < 0) → False) as xf.
    {
        intros [x x_lt].
        contradiction (nat0_lt_zero _ x_lt).
    }
    split.
    -   intros f g eq; clear eq.
        apply functional_ext.
        intros x.
        contradiction (xf x).
    -   intros [n n_lt].
        exists (empty_function _ _ xf).
        apply set_type_eq; cbn.
        apply nat0_lt_1 in n_lt.
        exact n_lt.
Qed.

Theorem card_pow_from_0 : ∀ κ, 1 <= κ → 0 ^ κ = 0.
    intros A.
    equiv_get_value A.
    unfold one, zero; cbn.
    unfold nat0_to_card, card_pow, le; equiv_simpl.
    intros [f f_inj].
    assert ((A → set_type (λ x : nat0, x < 0)) → False) as Af.
    {
        intros g.
        apply nat0_lt_0_false.
        apply g; clear g.
        exact (f [0|nat0_0_lt_1]).
    }
    exists (empty_function _ _ Af).
    apply empty_bij.
    exact nat0_lt_0_false.
Qed.

Theorem card_pow_from_1 : ∀ κ, 1 ^ κ = 1.
    intros A.
    equiv_get_value A.
    unfold one; cbn.
    unfold nat0_to_card, card_pow; equiv_simpl.
    exists (λ x, [0|nat0_0_lt_1]).
    split.
    -   intros f g eq; clear eq.
        apply functional_ext.
        intros a.
        destruct (f a) as [fa fa_lt].
        destruct (g a) as [ga ga_lt].
        apply set_type_eq; cbn.
        apply nat0_lt_1 in fa_lt.
        apply nat0_lt_1 in ga_lt.
        subst.
        reflexivity.
    -   intros [n n_lt].
        exists (λ x, [0|nat0_0_lt_1]).
        apply set_type_eq; cbn.
        apply nat0_lt_1 in n_lt.
        exact n_lt.
Qed.

Theorem card_pow_1 : ∀ κ, κ ^ 1 = κ.
    intros A.
    symmetry.
    equiv_get_value A.
    unfold one; cbn.
    unfold nat0_to_card, card_pow; equiv_simpl.
    exists (λ a, (λ x, a)).
    split.
    -   intros a b eq.
        apply func_eq in eq; try exact eq.
        exact [0|nat0_0_lt_1].
    -   intros f.
        exists (f [0|nat0_0_lt_1]).
        apply functional_ext.
        intros [x x_lt].
        apply f_equal.
        apply set_type_eq; cbn.
        apply nat0_lt_1 in x_lt.
        exact x_lt.
Qed.

Theorem card_pow_plus : ∀ κ μ ν, κ ^ (μ + ν) = κ ^ μ * κ ^ ν.
    intros A B C.
    equiv_get_value A B C.
    unfold plus, mult, card_pow; equiv_simpl.
    exists (λ f, ((λ b, f (inl b)), (λ c, f (inr c)))).
    split.
    -   intros f g eq.
        apply functional_ext.
        inversion eq as [[eq1' eq2']].
        pose proof (func_eq _ _ eq1') as eq1.
        pose proof (func_eq _ _ eq2') as eq2.
        clear eq1' eq2'.
        intros [b|c].
        +   specialize (eq1 b).
            cbn in eq1.
            exact eq1.
        +   specialize (eq2 c).
            cbn in eq2.
            exact eq2.
    -   intros [f g].
        exists (λ x, match x with
                     | inl b => f b
                     | inr c => g c
                     end).
        apply f_equal2.
        all: reflexivity.
Qed.

Theorem card_pow_mult : ∀ κ μ ν, κ ^ (μ * ν) = (κ ^ μ) ^ ν.
    intros A B C.
    equiv_get_value A B C.
    unfold mult, card_pow; equiv_simpl.
    exists (λ f, (λ c, (λ b, f (b, c)))).
    split.
    -   intros f g eq.
        apply functional_ext.
        intros [b c].
        pose proof (func_eq _ _ eq) as eq1.
        specialize (eq1 c); cbn in eq1.
        pose proof (func_eq _ _ eq1) as eq2.
        specialize (eq2 b); cbn in eq2.
        exact eq2.
    -   intros f.
        exists (λ x, f (snd x) (fst x)).
        cbn.
        reflexivity.
Qed.

Theorem card_mult_pow : ∀ κ μ ν, (κ * μ) ^ ν = κ ^ ν * μ ^ ν.
    intros A B C.
    equiv_get_value A B C.
    unfold mult, card_pow; equiv_simpl.
    exists (λ f, ((λ c, fst (f c)), (λ c, snd (f c)))).
    split.
    -   intros f g eq.
        apply functional_ext.
        intros c.
        inversion eq as [[eq1' eq2']]; clear eq.
        pose proof (func_eq _ _ eq1') as eq1.
        pose proof (func_eq _ _ eq2') as eq2.
        clear eq1' eq2'.
        specialize (eq1 c).
        specialize (eq2 c).
        cbn in *.
        destruct (f c) as [fc1 fc2].
        destruct (g c) as [gc1 gc2].
        cbn in *.
        rewrite eq1, eq2.
        reflexivity.
    -   intros f.
        exists (λ c, (fst f c, snd f c)).
        destruct f as [f1 f2].
        cbn.
        reflexivity.
Qed.

Theorem prop_size : |Prop| = 2.
    unfold one; cbn.
    unfold nat0_to_card, plus; equiv_simpl.
    exists (λ P, If (P = True) then (inl [0|nat0_0_lt_1])
                               else (inr [0|nat0_0_lt_1])).
    split.
    -   intros A B eq.
        repeat case_if.
        all: inversion eq.
        +   subst; reflexivity.
        +   rewrite neq_true_false in n, n0.
            subst; reflexivity.
    -   intros [[n n_lt]|[n n_lt]].
        all: pose proof n_lt as n_lt2.
        all: apply nat0_lt_1 in n_lt2.
        all: subst.
        +   exists True.
            case_if; try contradiction.
            apply f_equal.
            apply set_type_eq; reflexivity.
        +   exists False.
            case_if.
            *   pose proof prop_neq.
                symmetry in e.
                contradiction.
            *   apply f_equal.
                apply set_type_eq; reflexivity.
Qed.

Theorem power_set_size : ∀ A, |A → Prop| = 2 ^ |A|.
    intros A.
    rewrite func_size.
    rewrite prop_size.
    reflexivity.
Qed.

Theorem power_set_bigger : ∀ A, |A| < |A → Prop|.
    intros A.
    split.
    -   unfold le; equiv_simpl.
        exists (λ a, singleton a).
        intros a b eq.
        unfold singleton in eq.
        pose proof (func_eq _ _ eq) as eq2.
        specialize (eq2 b).
        cbn in eq2.
        rewrite eq2.
        reflexivity.
    -   intros eq.
        equiv_simpl in eq.
        destruct eq as [f f_bij].
        pose (B x := ¬f x x).
        pose proof (rand f_bij B) as [x x_eq].
        unfold B in x_eq.
        pose proof (func_eq _ _ x_eq) as eq.
        specialize (eq x).
        cbn in eq.
        apply any_prop_neq in eq.
        exact eq.
Qed.

Theorem card_lt_pow2 : ∀ κ, κ < 2^κ.
    intros A.
    equiv_get_value A.
    rewrite <- power_set_size.
    apply power_set_bigger.
Qed.

(* begin hide *)
Lemma card_suc_ex : ∀ κ, ∃ μ, κ < μ ∧ ∀ ν, κ < ν → μ <= ν.
    intros κ.
    pose (S μ := κ < μ).
    assert (∃ x, S x) as S_nempty.
    {
        exists (2^κ).
        apply card_lt_pow2.
    }
    pose proof (well_founded _ S_nempty) as [μ [Sμ μ_min]].
    exists μ.
    split; try exact Sμ.
    intros ν Sν.
    classic_contradiction leq.
    rewrite nle_lt in leq.
    exact (μ_min _ Sν (rand leq) (land leq)).
Qed.
(* end hide *)
Definition card_suc κ := ex_val (card_suc_ex κ).

Theorem card_suc_lt : ∀ κ, κ < card_suc κ.
    intros κ.
    unfold card_suc.
    rewrite_ex_val μ μ_eq.
    apply μ_eq.
Qed.

Theorem card_suc_le : ∀ κ μ, κ < μ → card_suc κ <= μ.
    intros κ μ lt.
    unfold card_suc.
    rewrite_ex_val ν ν_eq.
    apply ν_eq.
    exact lt.
Qed.
(* begin hide *)
Close Scope card_scope.
(* end hide *)
