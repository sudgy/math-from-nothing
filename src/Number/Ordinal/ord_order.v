Require Import init.

Require Export ord_base.
Require Import set_induction.

Open Scope ord_scope.

Definition ord_leq_func {A B : ord_type} (f : A → B) :=
    Injective f ∧ HomomorphismLe f ∧
    ∀ b : B, (∀ a, f a ≠ b) → ∀ a : A, f a < b.

Definition ord_leq (A B : ord_type) := ∃ f : A → B, ord_leq_func f.
Definition ord_ltq (A B : ord_type) :=
    ∃ b : B, A ~ (sub_ord_type (initial_segment b)).

Lemma ord_le_wd1 : ∀ A B C D, A ~ B → C ~ D → ord_leq A C → ord_leq B D.
Proof.
    intros A B C D [f] [g] [h [h_inj [h_le h_lt]]].
    exists (λ x, g (h (bij_inv f x))).
    split; [>|split].
    -   apply inj_comp; [>apply inj_comp|].
        +   apply bij_inv_bij.
        +   exact h_inj.
        +   apply g.
    -   split.
        intros a b leq.
        do 2 rewrite <- homo_le2.
        rewrite (homo_le2 (f := f)).
        do 2 rewrite bij_inv_eq2.
        exact leq.
    -   intros b b_nin a.
        specialize (h_lt (bij_inv g b)).
        prove_parts h_lt.
        {
            intros x x_eq.
            apply (b_nin (f x)).
            rewrite bij_inv_eq1.
            rewrite x_eq.
            apply bij_inv_eq2.
        }
        rewrite <- (bij_inv_eq2 g b).
        rewrite <- homo_lt2.
        apply h_lt.
Qed.
Lemma ord_le_wd : ∀ A B C D, A ~ B → C ~ D → (ord_leq A C) = (ord_leq B D).
Proof.
    intros A B C D AB CD.
    apply propositional_ext.
    split.
    -   apply ord_le_wd1; assumption.
    -   pose proof (eq_symmetric ord_equiv) as sym.
        apply ord_le_wd1; apply sym; assumption.
Qed.

Global Instance ord_order : Order ord := {
    le := binary_op ord_le_wd;
}.

Theorem ord_lt_simpl : ∀ A B, to_ord A < to_ord B ↔ ord_ltq A B.
Proof.
    intros A B.
    unfold strict, le; equiv_simpl.
    split.
    -   intros [[f [f_inj [f_le f_lt]]] neq].
        assert (∃ x : B, ∀ a, f a ≠ x) as S_ex.
        {
            classic_contradiction contr.
            apply neq.
            split.
            exists f; [>|exact f_le].
            split; [>exact f_inj|].
            split.
            intros y.
            rewrite not_ex in contr.
            specialize (contr y).
            rewrite not_all in contr.
            destruct contr as [a eq].
            exists a.
            rewrite not_not in eq.
            exact eq.
        }
        pose proof (well_ordered _ S_ex) as [x [x_neq x_least]].
        specialize (f_lt _ x_neq).
        exists x.
        split.
        exists (λ a, [f a|f_lt a]); [>split|].
        +   split.
            intros a b eq.
            apply (set_type_eq2 (S := initial_segment x)) in eq.
            apply inj in eq.
            exact eq.
        +   split.
            intros [y y_lt].
            specialize (x_least y).
            classic_contradiction contr.
            prove_parts x_least.
            {
                intros a eq.
                subst y.
                apply contr.
                exists a.
                apply set_type_refl.
            }
            contradiction (irrefl _ (le_lt_trans x_least y_lt)).
        +   split.
            apply f_le.
    -   intros [x [f]].
        split.
        +   exists (λ x, [f x|]).
            split; [>|split].
            *   split.
                intros a b eq.
                apply set_type_eq in eq.
                apply f in eq.
                exact eq.
            *   split.
                apply f.
            *   intros b b_nin a.
                order_contradiction leq.
                pose proof (le_lt_trans leq [|f a]) as b_lt.
                pose proof (sur f [b|b_lt]) as [z eq].
                apply (b_nin z).
                rewrite eq.
                reflexivity.
        +   intros g.
            apply (eq_symmetric ord_equiv) in g.
            destruct g as [g].
            assert (∀ a, a ≤ [f (g a)|]) as leq.
            {
                intros a.
                induction a as [a IHa] using transfinite_induction.
                order_contradiction contr.
                specialize (IHa _ contr).
                assert (f (g a) ≤ f (g [f (g a)|])) as leq by exact IHa.
                do 2 rewrite <- homo_le2 in leq.
                contradiction (irrefl _ (lt_le_trans contr leq)).
            }
            pose proof [|f (g x)] as ltq.
            contradiction (irrefl _ (le_lt_trans (leq x) ltq)).
Qed.

Lemma ord_nlt_le : ∀ α β : ord, ¬(α < β) → β ≤ α.
Proof.
    intros A B AB.
    equiv_get_value A B.
    unfold le; equiv_simpl.
    rewrite ord_lt_simpl in AB.
    assert (B → A) as throwaway.
    {
        intros b.
        classic_contradiction contr.
        apply AB.
        exists (ex_val (well_ordered all (ex_intro all b true))).
        rewrite_ex_val z [C0 z_min]; clear C0.
        split.
        exists (empty_function _ _ contr).
        -   apply empty_bij.
            intros [x x_lt].
            contradiction (irrefl _ (le_lt_trans (z_min x true) x_lt)).
        -   split.
            intros a.
            contradiction.
    }
    pose (f (p : B) (g : set_type (λ x, x < p) → A) :=
        IfH (∃ a, ∀ x, g x < a)
        then λ H, ex_val (well_ordered _ H)
        else λ _, throwaway p).
    pose proof (transfinite_recursion _ f) as [g g_eq].
    pose (G (n : B) := λ z, ∀ x : set_type (λ x, x < n), g [x|] < z).
    pose (good n := ∃ a, G n a).
    assert (∀ n, good n → is_least le (G n) (g n)) as good_least.
    {
        intros n n_good.
        unfold good in n_good.
        rewrite g_eq.
        unfold f.
        destruct (sem _) as [S_ex|S_nex].
        -   rewrite_ex_val a [a_ltq a_least].
            split.
            +   exact a_ltq.
            +   exact a_least.
        -   contradiction.
    }
    clear g_eq.
    assert (∀ a b, good a → good b → a < b → g a < g b) as g_lt.
    {
        intros a b a_good b_good ltq.
        pose proof (good_least b b_good) as [b1 b2].
        exact (b1 [a|ltq]).
    }
    assert (∀ a b, good a → good b → a ≤ b → g a ≤ g b) as g_le.
    {
        intros a b a_good b_good leq.
        classic_case (a = b) as [eq|neq]; [>subst; apply refl|].
        apply g_lt; try split; assumption.
    }
    assert (∀ a b, good a → good b → g a = g b → a = b) as g_inj.
    {
        intros a b a_good b_good eq.
        destruct (trichotomy a b) as [[ltq|eq']|ltq].
        +   apply (g_lt _ _ a_good b_good) in ltq.
            rewrite eq in ltq.
            contradiction (irrefl _ ltq).
        +   exact eq'.
        +   apply (g_lt _ _ b_good a_good) in ltq.
            rewrite eq in ltq.
            contradiction (irrefl _ ltq).
    }
    assert (∀ n, good n) as all_good.
    {
        intros n.
        induction n as [n IHn] using transfinite_induction.
        classic_contradiction contr.
        apply AB.
        exists n.
        apply (eq_symmetric ord_equiv).
        split.
        exists (λ x, g [x|]); [>split|].
        +   split.
            intros [a a_lt] [b b_lt] eq.
            apply set_type_eq2.
            apply g_inj.
            *   exact (IHn a a_lt).
            *   exact (IHn b b_lt).
            *   exact eq.
        +   split.
            intros x.
            classic_contradiction contr2.
            rewrite not_ex in contr2.
            apply contr.
            exists x.
            intros [a a_lt]; cbn.
            induction a as [a IHa] using transfinite_induction.
            assert (G a x) as Gax.
            {
                intros [z z_lt].
                exact (IHa z z_lt (trans z_lt a_lt)).
            }
            split; [>|exact (contr2 [a|a_lt])].
            apply (good_least _ (IHn a a_lt)).
            exact Gax.
        +   split.
            intros a b leq.
            apply g_le.
            *   exact (IHn [a|] [|a]).
            *   exact (IHn [b|] [|b]).
            *   exact leq.
    }
    exists g.
    split; [>|split].
    -   split.
        intros a b.
        apply g_inj; apply all_good.
    -   split.
        intros a b.
        apply g_le; apply all_good.
    -   intros b b_neq a.
        induction a as [a IHa] using transfinite_induction.
        split; [>|apply b_neq].
        apply good_least; [>apply all_good|].
        intros [x x_lt].
        exact (IHa x x_lt).
Qed.

Global Instance ord_le_connex : Connex le.
Proof.
    split.
    intros α β.
    classic_case (α < β) as [ltq|leq].
    -   left.
        apply ltq.
    -   right.
        apply ord_nlt_le in leq.
        exact leq.
Qed.

Lemma ord_le_part : ∀ {A B : ord_type} {f : A → B},
    ord_leq_func f → ∀ x y, (∀ a, a < x → f a ≠ y) → f x ≤ y.
Proof.
    intros A B f [f_inj [f_le f_lt]] x y y_neq.
    order_contradiction ltq.
    assert (f x < y) as ltq'.
    {
        apply f_lt.
        intros a.
        classic_case (a < x) as [ax|xa].
        -   exact (y_neq _ ax).
        -   rewrite nlt_le in xa.
            pose proof (homo_le (f := f) _ _ xa) as xa'.
            rewrite neq_sym.
            apply (lt_le_trans ltq xa').
    }
    contradiction (irrefl _ (trans ltq ltq')).
Qed.

Global Instance ord_le_antisym : Antisymmetric le.
Proof.
    split.
    intros A B.
    equiv_get_value A B.
    unfold le; equiv_simpl.
    intros [f f_leq] [g g_leq].
    split.
    exists f; [>|apply f_leq].
    split; [>apply f_leq|].
    split.
    intros x.
    exists (g x).
    pose proof (land f_leq).
    pose proof (land g_leq).
    induction x as [x IHx] using transfinite_induction.
    pose proof (ord_le_part f_leq (g x) x) as f_le'.
    prove_parts f_le'.
    {
        intros a a_ltq.
        pose proof (ord_le_part g_leq x a) as g_le'.
        intros eq.
        prove_parts g_le'.
        {
            intros b b_ltq eq'.
            specialize (IHx _ b_ltq).
            subst a.
            rewrite IHx in eq.
            rewrite eq in b_ltq.
            contradiction (irrefl _ b_ltq).
        }
        contradiction (irrefl _ (lt_le_trans a_ltq g_le')).
    }
    classic_contradiction neq.
    specialize (IHx _ (make_and f_le' neq)).
    do 2 apply inj in IHx.
    contradiction.
Qed.

Lemma ord_le_simpl : ∀ (A B : ord_type),
    (∃ f : A → B, Injective f ∧ HomomorphismLe f) → to_ord A ≤ to_ord B.
Proof.
    intros A B [f [f_inj f_homo]].
    order_contradiction ltq.
    rewrite ord_lt_simpl in ltq.
    destruct ltq as [x [g]].
    pose (h (a : A) := g (f a)).
    assert (Injective h) as h_inj.
    {
        unfold h.
        apply inj_comp.
        -   exact f_inj.
        -   apply g.
    }
    assert (HomomorphismLe h) as h_le.
    {
        unfold h.
        apply homo_le_compose.
        -   exact f_homo.
        -   apply g.
    }
    clearbody h.
    clear f g f_inj f_homo.
    assert (∀ a, a ≤ [h a|]) as h_ge.
    {
        intros a.
        induction a as [a IHa] using transfinite_induction.
        order_contradiction contr.
        specialize (IHa _ contr).
        assert (h a ≤ h [h a|]) as leq by exact IHa.
        rewrite <- homo_le2 in leq.
        contradiction (irrefl _ (le_lt_trans leq contr)).
    }
    pose proof [|h x] as x_lt.
    unfold initial_segment in x_lt.
    contradiction (irrefl _ (le_lt_trans (h_ge x) x_lt)).
Qed.

Global Instance ord_le_trans : Transitive le.
Proof.
    split.
    intros A B C AB BC.
    equiv_get_value A B C.
    apply ord_le_simpl.
    unfold le in *; equiv_simpl in BC; equiv_simpl in AB.
    destruct AB as [f [f_inj [f_le f_gt]]].
    destruct BC as [g [g_inj [g_le g_gt]]].
    exists (λ x, g (f x)).
    split.
    -   apply inj_comp; assumption.
    -   apply homo_le_compose; assumption.
Qed.

Definition ord_type_init_ord_base (A : ord_type) (a : A)
    := to_ord (sub_ord_type (initial_segment a)).
Lemma ord_type_init_ord_in {A : ord_type} :
    ∀ a : A, initial_segment (to_ord A) (ord_type_init_ord_base A a).
Proof.
    intros a.
    unfold ord_type_init_ord_base, initial_segment.
    rewrite ord_lt_simpl.
    exists a.
    apply refl.
Qed.
Definition ord_type_init_ord (A : ord_type) (a : A)
    := [ord_type_init_ord_base A a | ord_type_init_ord_in a].

Theorem ord_type_init_ord_base_le A : HomomorphismLe (ord_type_init_ord_base A).
Proof.
    split.
    intros a b leq.
    unfold ord_type_init_ord_base.
    apply ord_le_simpl.
    exists (λ x : sub_ord_type (initial_segment a),
        [[x|] | lt_le_trans [|x] leq] : sub_ord_type (initial_segment b)).
    split; split.
    -   intros x y eq.
        apply (set_type_eq2 (a := [x|])) in eq.
        rewrite set_type_eq in eq.
        exact eq.
    -   intros x y xy.
        unfold le; cbn.
        exact xy.
Qed.

Theorem ord_type_init_ord_le A : HomomorphismLe (ord_type_init_ord A).
Proof.
    split.
    intros a b leq.
    unfold le; cbn.
    apply ord_type_init_ord_base_le.
    exact leq.
Qed.

Lemma ord_type_init_ord_inj_wlog A :
    ∀ a b, ord_type_init_ord_base A a = ord_type_init_ord_base A b → a ≤ b.
Proof.
    intros a b eq.
    unfold ord_type_init_ord_base in eq.
    equiv_simpl in eq.
    destruct eq as [f].
    assert (∀ x, [x|] ≤ [f x|]) as f_leq.
    {
        intros x.
        induction x as [x IHx] using transfinite_induction.
        order_contradiction ltq2.
        pose proof (trans ltq2 [|x]) as fx_lt.
        specialize (IHx [[f x|]|fx_lt]); cbn in IHx.
        prove_parts IHx; [>apply set_type_lt; apply ltq2|].
        assert (f x ≤ f [[f x|] | fx_lt]) as leq by exact IHx.
        apply homo_le2 in leq.
        unfold le in leq; cbn in leq.
        contradiction (irrefl _ (le_lt_trans leq ltq2)).
    }
    order_contradiction ltq.
    specialize (f_leq [b|ltq]); cbn in f_leq.
    pose proof [|f [b|ltq]] as ltq2.
    unfold initial_segment in ltq2.
    contradiction (irrefl _ (le_lt_trans f_leq ltq2)).
Qed.

Theorem ord_type_init_ord_base_inj A : Injective (ord_type_init_ord_base A).
Proof.
    split.
    intros a b eq.
    apply antisym.
    -   exact (ord_type_init_ord_inj_wlog A _ _ eq).
    -   symmetry in eq.
        exact (ord_type_init_ord_inj_wlog A _ _ eq).
Qed.

Theorem ord_type_init_ord_bij A : Bijective (ord_type_init_ord A).
Proof.
    split; split.
    -   intros a b eq.
        unfold ord_type_init_ord in eq.
        rewrite set_type_eq2 in eq.
        pose proof (ord_type_init_ord_base_inj A).
        apply inj.
        exact eq.
    -   intros [y y_lt].
        unfold initial_segment in y_lt.
        equiv_get_value y.
        pose proof y_lt as y_lt2.
        rewrite ord_lt_simpl in y_lt2.
        destruct y_lt2 as [x x_eq].
        exists x.
        unfold ord_type_init_ord.
        rewrite set_type_eq2.
        unfold ord_type_init_ord_base.
        symmetry.
        equiv_simpl.
        exact x_eq.
Qed.

Lemma ords_lt_wo :
    ∀ α : ord, WellOrdered (λ a b : set_type (initial_segment α), [a|] ≤ [b|]).
Proof.
    intros A.
    split.
    intros S [β Sβ].
    equiv_get_value A.
    pose proof (ord_type_init_ord_bij A).
    pose proof (ord_type_init_ord_le A).
    pose (S' (a : A) := S (ord_type_init_ord A a)).
    pose proof (sur (ord_type_init_ord A) β) as [x x_eq].
    assert (S' x) as Sx.
    {
        unfold S'.
        rewrite x_eq.
        exact Sβ.
    }
    pose proof (well_ordered S' (ex_intro _ _ Sx)) as [m [S'm m_least]].
    clear x x_eq Sx.
    exists (ord_type_init_ord A m).
    split; [>exact S'm|].
    intros γ Sγ.
    pose proof (sur (ord_type_init_ord A) γ) as [z z_eq].
    subst γ.
    pose proof (homo_le (f := ord_type_init_ord A)) as stupid.
    apply stupid.
    exact (m_least z Sγ).
Qed.

Global Instance ord_le_wo : WellOrdered le.
Proof.
    split.
    intros S [α Sα].
    classic_case (is_least le S α) as [α_least|α_nleast].
    1: exists α; exact α_least.
    unfold is_least in α_nleast.
    rewrite not_and_impl in α_nleast.
    specialize (α_nleast Sα).
    rewrite not_all in α_nleast.
    destruct α_nleast as [β α_nleast].
    rewrite not_impl in α_nleast.
    destruct α_nleast as [Sβ β_lt].
    rewrite nle_lt in β_lt.
    pose proof (ords_lt_wo α).
    pose proof (well_ordered (λ γ, S [γ|]) (ex_intro _ [β|β_lt] Sβ))
        as [[μ μ_lt] [Sμ μ_least]].
    exists μ.
    split; [>exact Sμ|].
    intros y Sy.
    classic_case (y < α) as [ltq|leq].
    -   exact (μ_least [y|ltq] Sy).
    -   rewrite nlt_le in leq.
        apply (lt_le_trans μ_lt leq).
Qed.

Close Scope ord_scope.
