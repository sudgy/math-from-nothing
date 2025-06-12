Require Import init.

Require Export ord2_plus.
Require Import order_dict.

Open Scope ord_scope.

Notation "A ⊗ B" := (make_ord_type (A * B) (dictionary_order A B) _ _)
    : ord_scope.

Lemma ord_mult_wd : ∀ A B C D : ord_type, A ~ B → C ~ D → (A ⊗ C) ~ (B ⊗ D).
Proof.
    intros A B C D [f] [g].
    split.
    exists (λ x, (f (fst x), g (snd x))).
    1: split.
    all: split.
    -   intros [a1 c1] [a2 c2]; cbn.
        intros eq.
        apply prod_split in eq as [eq1 eq2].
        apply inj in eq1, eq2.
        subst.
        reflexivity.
    -   intros [b d].
        pose proof (sur f b) as [a a_eq].
        pose proof (sur g d) as [c c_eq].
        exists (a, c); cbn.
        subst.
        reflexivity.
    -   intros [a1 c1] [a2 c2]; cbn.
        unfold le; cbn.
        intros [ltq|[leq eq]].
        +   left.
            apply homo_lt.
            exact ltq.
        +   right.
            subst.
            split.
            *   apply homo_le.
                exact leq.
            *   reflexivity.
Qed.

Global Instance ord_mult : Mult ord := {
    mult := binary_op (binary_self_wd ord_mult_wd)
}.

Global Instance ord_ldist : Ldist ord.
Proof.
    split.
    intros A B C.
    equiv_get_value A B C.
    unfold plus, mult; equiv_simpl.
    split.
    exists (λ x, match x with
        | (a, inl b) => inl (a, b)
        | (a, inr c) => inr (a, c)
        end).
    1: split.
    all: split; cbn.
    -   intros [a1 [b1|c1]] [a2 [b2|c2]] eq.
        +   apply (inl_eq (a1, b1)) in eq.
            apply prod_split in eq as [eq1 eq2].
            subst.
            reflexivity.
        +   contradiction (inlr_neq eq).
        +   contradiction (inrl_neq eq).
        +   apply (inr_eq (a1, c1)) in eq.
            apply prod_split in eq as [eq1 eq2].
            subst.
            reflexivity.
    -   intros [[a b]|[a c]].
        +   exists (a, inl b).
            reflexivity.
        +   exists (a, inr c).
            reflexivity.
    -   intros [a1 [b1|c1]] [a2 [b2|c2]] leq.
        all: unfold le; cbn.
        all: destruct leq as [ltq|[leq eq]].
        +   apply inl_lt in ltq.
            left.
            exact ltq.
        +   apply (inl_eq b1) in eq.
            right.
            split; [>exact leq|exact eq].
        +   exact true.
        +   exact true.
        +   destruct ltq as [leq neq].
            contradiction leq.
        +   contradiction (inrl_neq eq).
        +   apply inr_lt in ltq.
            left.
            exact ltq.
        +   apply (inr_eq c1) in eq.
            subst c2.
            right.
            split; [>exact leq|reflexivity].
Qed.

Global Instance ord_mult_assoc : MultAssoc ord.
Proof.
    split.
    intros A B C.
    equiv_get_value A B C.
    unfold mult; equiv_simpl.
    split.
    exists (λ x, match x with
        | (a, (b, c)) => ((a, b), c)
        end).
    1: split.
    all: split; cbn.
    -   intros [a1 [b1 c1]] [a2 [b2 c2]] eq.
        apply prod_split in eq as [eq1 eq2].
        apply prod_split in eq1 as [eq1 eq3].
        subst.
        reflexivity.
    -   intros [[a b] c].
        exists (a, (b, c)).
        reflexivity.
    -   intros [a1 [b1 c1]] [a2 [b2 c2]] leq.
        destruct leq as [ltq|[leq eq]].
        +   apply dict_order_lt in ltq; cbn in ltq.
            destruct ltq as [ltq|[ltq eq]].
            *   left.
                exact ltq.
            *   right.
                split; [>|exact eq].
                left.
                exact ltq.
        +   apply prod_split in eq as [eq1 eq2].
            subst b2 c2.
            right.
            split; [>|reflexivity].
            right.
            split; [>|reflexivity].
            exact leq.
Qed.

Global Instance ord_mult_lanni : MultLanni ord.
Proof.
    split.
    intros A.
    equiv_get_value A.
    unfold zero, mult; equiv_simpl.
    split.
    exists fst.
    1: split.
    all: split; cbn.
    -   intros [a b].
        contradiction (empty_false a).
    -   intros a.
        contradiction (empty_false a).
    -   intros [a b].
        contradiction (empty_false a).
Qed.

Global Instance ord_one : One ord := {
    one := to_ord (make_ord_type singleton_type _ _ _)
}.

Global Instance ord_mult_lid : MultLid ord.
Proof.
    split.
    intros A.
    equiv_get_value A.
    unfold one, mult; equiv_simpl.
    split.
    exists snd.
    1: split.
    all: split; cbn.
    -   intros [a1 a2] [b1 b2] eq.
        cbn in eq.
        apply prod_combine; cbn.
        +   apply singleton_type_eq.
        +   exact eq.
    -   intros y.
        exists (Single, y).
        reflexivity.
    -   intros [a1 a2] [b1 b2] leq; cbn.
        destruct leq as [ltq|[leq eq]].
        +   apply ltq.
        +   rewrite eq.
            apply refl.
Qed.

Global Instance ord_mult_rid : MultRid ord.
Proof.
    split.
    intros A.
    equiv_get_value A.
    unfold one, mult; equiv_simpl.
    split.
    exists fst.
    1: split.
    all: split; cbn.
    -   intros [a1 a2] [b1 b2] eq.
        cbn in eq.
        apply prod_combine; cbn.
        +   exact eq.
        +   apply singleton_type_eq.
    -   intros y.
        exists (y, Single).
        reflexivity.
    -   intros [a1 a2] [b1 b2] leq; cbn.
        destruct leq as [ltq|[leq eq]].
        +   rewrite (singleton_type_eq a2 b2) in ltq.
            contradiction (irrefl _ ltq).
        +   exact leq.
Qed.

Global Instance ord_le_mult : OrderMult ord.
Proof.
    split.
    intros α β a b.
    apply ord_pos.
Qed.

Theorem ord_mult_zero : ∀ α β, 0 = α * β → {0 = α} + {0 = β}.
Proof.
    intros A B eq.
    classic_case (0 = A) as [A_z|A_nz].
    1: left; exact A_z.
    right.
    equiv_get_value A B.
    apply ord_false_0.
    intros b.
    apply A_nz.
    apply ord_false_0.
    intros a.
    symmetry in eq.
    unfold mult, zero in eq; equiv_simpl in eq.
    destruct eq as [f].
    contradiction (empty_false (f (a, b))).
Qed.

Theorem ord_le_lmult : ∀ {α β} γ, α ≤ β → γ * α ≤ γ * β.
Proof.
    intros α β γ leq.
    apply ord_le_ex in leq as [δ eq].
    rewrite <- eq.
    rewrite ldist.
    rewrite <- plus_rid at 1.
    apply le_lplus.
    apply ord_pos.
Qed.

Theorem ord_lt_lmult : ∀ {α β} γ, 0 ≠ γ → α < β → γ * α < γ * β.
Proof.
    intros α β γ γ_nz ltq.
    apply ord_lt_ex in ltq as [δ [δ_nz δ_eq]].
    subst β.
    rewrite ldist.
    rewrite <- plus_rid at 1.
    apply lt_lplus.
    apply ord_pos2.
    intros contr.
    apply ord_mult_zero in contr as [eq|eq]; contradiction.
Qed.

Global Instance ord_mult_lcancel : MultLcancel ord.
Proof.
    split.
    intros α β γ γ_nz eq.
    destruct (trichotomy α β) as [[ltq|eq']|ltq].
    -   apply ord_lt_lmult with γ in ltq; [>|exact γ_nz].
        destruct ltq; contradiction.
    -   exact eq'.
    -   symmetry in eq.
        apply ord_lt_lmult with γ in ltq; [>|exact γ_nz].
        destruct ltq; contradiction.
Qed.

Global Instance ord_le_lmult_class : OrderLmult ord.
Proof.
    split.
    intros α β γ z leq.
    apply ord_le_lmult.
    exact leq.
Qed.

Theorem ord_lt_mult_lcancel : ∀ {α β} γ, γ * α < γ * β → α < β.
Proof.
    intros α β γ eq.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    apply ord_le_lmult with γ in contr.
    contradiction (irrefl _ (le_lt_trans contr eq)).
Qed.

Theorem ord_le_mult_lcancel : ∀ {α β} γ, 0 ≠ γ → γ * α ≤ γ * β → α ≤ β.
Proof.
    intros α β γ γ_nz leq.
    classic_case (γ * α = γ * β) as [eq|neq].
    -   apply mult_lcancel in eq; [>|exact γ_nz].
        rewrite eq.
        apply refl.
    -   apply (ord_lt_mult_lcancel γ).
        split; assumption.
Qed.

Global Instance ord_le_mult_lcancel_pos : OrderMultLcancel ord.
Proof.
    split.
    intros α β γ [γ_leq γ_nz] leq.
    apply ord_le_mult_lcancel with γ; assumption.
Qed.

Theorem ord_le_rmult : ∀ {α β} γ, α ≤ β → α * γ ≤ β * γ.
Proof.
    intros A B C leq.
    equiv_get_value A B C.
    unfold le in leq; equiv_simpl in leq.
    destruct leq as [f [f_inj [f_le f_lt]]].
    unfold mult; equiv_simpl.
    apply ord_le_simpl.
    exists (λ x, (f (fst x), snd x)).
    split; split.
    -   intros [a1 c1] [a2 c2] eq.
        cbn in eq.
        apply prod_split in eq as [eq1 eq2].
        apply inj in eq1.
        subst.
        reflexivity.
    -   intros [a1 c1] [a2 c2] leq; cbn.
        destruct leq as [ltq|[leq eq]].
        +   left.
            exact ltq.
        +   right.
            split.
            *   apply homo_le.
                exact leq.
            *   exact eq.
Qed.

Global Instance ord_le_rmult_class : OrderRmult ord.
Proof.
    split.
    intros α β γ z leq.
    apply ord_le_rmult.
    exact leq.
Qed.

Theorem ord_lt_mult_rcancel : ∀ {α β} γ, α * γ < β * γ → α < β.
Proof.
    intros α β γ ltq.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    apply ord_le_rmult with γ in contr.
    contradiction (irrefl _ (le_lt_trans contr ltq)).
Qed.

Theorem ord_lt_one : ∀ α, α < 1 → 0 = α.
Proof.
    intros A.
    equiv_get_value A.
    unfold one; equiv_simpl.
    rewrite ord_lt_simpl.
    intros [x [f]]; cbn in x.
    apply ord_false_0.
    intros a.
    pose proof [|f a] as ltq.
    unfold initial_segment in ltq.
    rewrite (singleton_type_eq _ x) in ltq.
    contradiction (irrefl _ ltq).
Qed.

Theorem ord_le_self_lmult : ∀ α β, 0 ≠ β → α ≤ β * α.
Proof.
    intros α β β_nz.
    rewrite <- (mult_lid α) at 1.
    apply ord_le_rmult.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    apply ord_lt_one in contr.
    contradiction.
Qed.

Theorem ord_le_self_rmult : ∀ α β, 0 ≠ β → α ≤ α * β.
Proof.
    intros α β β_nz.
    rewrite <- (mult_rid α) at 1.
    apply ord_le_lmult.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    apply ord_lt_one in contr.
    contradiction.
Qed.

#[refine]
Global Instance ord_not_trivial : NotTrivial ord := {
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Proof.
    intros contr.
    symmetry in contr.
    unfold one, zero in contr; equiv_simpl in contr.
    destruct contr as [f].
    contradiction (empty_false (f Single)).
Qed.

Close Scope ord_scope.
