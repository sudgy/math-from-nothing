Require Import init.

Require Export nat_base.
Require Import nat_plus.
Require Import nat_mult.
Require Export nat_order.

Definition simple_finite U := ∃ n (f : U → nat_to_set_type n), Injective f.

Theorem simple_finite_trans : ∀ U V,
    simple_finite V → (∃ f : U → V, Injective f) → simple_finite U.
Proof.
    intros U V [n [g g_inj]] [f f_inj].
    exists n, (λ x, g (f x)).
    apply inj_comp; assumption.
Qed.

Theorem simple_finite_nat : ∀ n, simple_finite (set_type (initial_segment n)).
Proof.
    intros n.
    exists n.
    exists identity.
    apply identity_bijective.
Qed.

Theorem simple_finite_sum : ∀ U V,
    simple_finite U → simple_finite V → simple_finite (U + V).
Proof.
    intros U V [m [f f_inj]] [n [g g_inj]].
    exists (m + n).
    assert (∀ x, initial_segment (m + n) [f x|]) as f_in.
    {
        intros x.
        pose proof [|f x] as ltq.
        unfold initial_segment in *.
        apply (lt_le_trans ltq).
        apply nat_le_self_rplus.
    }
    assert (∀ x, initial_segment (m + n) (m + [g x|])) as g_in.
    {
        intros x.
        pose proof [|g x] as ltq.
        unfold initial_segment in *.
        apply lt_lplus.
        exact ltq.
    }
    exists (λ x, match x with
                 | inl a => [_|f_in a]
                 | inr b => [_|g_in b]
                 end).
    split.
    intros [a|a] [b|b] eq; setoid_rewrite set_type_eq2 in eq.
    -   rewrite set_type_eq in eq.
        apply inj in eq.
        subst b.
        reflexivity.
    -   pose proof [|f a] as ltq.
        unfold initial_segment in ltq.
        rewrite eq in ltq.
        apply (le_lt_trans (nat_le_self_rplus _ _)) in ltq.
        contradiction (irrefl _ ltq).
    -   pose proof [|f b] as ltq.
        unfold initial_segment in ltq.
        rewrite <- eq in ltq.
        apply (le_lt_trans (nat_le_self_rplus _ _)) in ltq.
        contradiction (irrefl _ ltq).
    -   apply plus_lcancel in eq.
        rewrite set_type_eq in eq.
        apply inj in eq.
        subst b.
        reflexivity.
Qed.

Theorem simple_finite_prod : ∀ U V,
    simple_finite U → simple_finite V → simple_finite (U * V).
Proof.
    intros U V [m [f f_inj]] [n [g g_inj]].
    exists (m * n).
    assert (∀ a b, initial_segment (m * n) (n * [f a|] + [g b|])) as fg_in.
    {
        intros a b.
        pose proof [|f a] as a_lt.
        pose proof [|g b] as b_lt.
        unfold initial_segment in *.
        rewrite <- nat_le_suc_lt in a_lt.
        apply (nat_le_lmult n) in a_lt.
        rewrite nat_mult_rsuc in a_lt.
        apply (lt_rplus (n * [f a|])) in b_lt.
        pose proof (lt_le_trans b_lt a_lt) as ltq.
        rewrite plus_comm in ltq.
        rewrite (mult_comm n m) in ltq.
        exact ltq.
    }
    exists (λ x, [_|fg_in (fst x) (snd x)]).
    split.
    intros [a1 a2] [b1 b2]; cbn.
    intros eq.
    setoid_rewrite set_type_eq2 in eq.
    pose proof [|g a2] as a2_lt.
    pose proof [|g b2] as b2_lt.
    unfold initial_segment in *.
    destruct (trichotomy [f a1|] [f b1|]) as [[ltq|eq2]|ltq].
    -   apply nat_lt_ex in ltq as [c c_eq].
        rewrite <- c_eq in eq.
        rewrite ldist in eq.
        rewrite <- plus_assoc in eq.
        apply plus_lcancel in eq.
        rewrite eq in a2_lt.
        apply (le_lt_trans (nat_le_self_rplus _ _)) in a2_lt.
        rewrite nat_mult_rsuc in a2_lt.
        apply (le_lt_trans (nat_le_self_rplus _ _)) in a2_lt.
        contradiction (irrefl _ a2_lt).
    -   rewrite set_type_eq in eq2.
        apply inj in eq2.
        subst b1.
        apply plus_lcancel in eq.
        rewrite set_type_eq in eq.
        apply inj in eq.
        subst b2.
        reflexivity.
    -   apply nat_lt_ex in ltq as [c c_eq].
        rewrite <- c_eq in eq.
        rewrite ldist in eq.
        rewrite <- plus_assoc in eq.
        apply plus_lcancel in eq.
        rewrite <- eq in b2_lt.
        apply (le_lt_trans (nat_le_self_rplus _ _)) in b2_lt.
        rewrite nat_mult_rsuc in b2_lt.
        apply (le_lt_trans (nat_le_self_rplus _ _)) in b2_lt.
        contradiction (irrefl _ b2_lt).
Qed.

Theorem simple_finite_bij : ∀ U, simple_finite U →
    ∃ n (f : U → nat_to_set_type n), Bijective f.
Proof.
    intros U [n [f f_inj]].
    revert U f f_inj.
    nat_induction n; intros.
    {
        exists 0, f.
        split; [>exact f_inj|].
        split.
        intros n.
        contradiction (nat_lt_0_false n).
    }
    classic_case (∃ a, [f a|] = n) as [[a a_eq]|a_nex].
    -   pose (V := set_type (λ x, x ≠ a)).
        assert (∀ x : V, initial_segment n [f [x|]|]) as f_in.
        {
            intros x.
            split.
            -   rewrite <- nat_lt_suc_le.
                exact [|f [x|]].
            -   intros eq.
                destruct x as [x x_neq].
                cbn in eq.
                rewrite <- a_eq in eq.
                rewrite set_type_eq in eq.
                apply inj in eq.
                contradiction.
        }
        specialize (IHn _ (λ x, [_|f_in x])).
        prove_parts IHn.
        {
            split.
            intros x y.
            setoid_rewrite set_type_eq2.
            rewrite set_type_eq.
            intros eq.
            apply inj in eq.
            rewrite set_type_eq in eq.
            exact eq.
        }
        destruct IHn as [m [g g_bij]].
        exists (nat_suc m).
        assert (initial_segment (nat_suc m) m) as m_in by apply nat_lt_suc.
        assert (∀ x, initial_segment (nat_suc m) [g x|]) as g_in.
        {
            intros x.
            unfold initial_segment.
            apply (trans2 (nat_lt_suc m)).
            exact [|g x].
        }
        exists (λ x, IfH x = a
            then (λ _, [m|m_in])
            else (λ H, [_|g_in [_|H]])).
        split; split.
        +   intros x y.
            destruct (strong_excluded_middle (x = a)) as [x_eq|x_neq];
            destruct (strong_excluded_middle (y = a)) as [y_eq|y_neq].
            *   subst.
                reflexivity.
            *   intros eq.
                setoid_rewrite set_type_eq2 in eq.
                pose proof [|g [y|y_neq]] as ltq.
                unfold initial_segment in ltq.
                rewrite <- eq in ltq.
                contradiction (irrefl _ ltq).
            *   intros eq.
                setoid_rewrite set_type_eq2 in eq.
                pose proof [|g [x|x_neq]] as ltq.
                unfold initial_segment in ltq.
                rewrite eq in ltq.
                contradiction (irrefl _ ltq).
            *   intros eq.
                setoid_rewrite set_type_eq2 in eq.
                rewrite set_type_eq in eq.
                apply inj in eq.
                inversion eq.
                reflexivity.
        +   intros [y y_lt].
            unfold initial_segment in y_lt.
            pose proof y_lt as y_lt2.
            rewrite nat_lt_suc_le in y_lt2.
            classic_case (y = m) as [eq|neq].
            *   subst y.
                exists a.
                destruct (strong_excluded_middle (a = a)); [>|contradiction].
                apply set_type_eq2.
                reflexivity.
            *   assert (initial_segment m y) as y_in by (split; assumption).
                pose proof (sur g [y|y_in]) as [[x x_neq] x_eq].
                exists x.
                destruct (strong_excluded_middle (x = a)); [>contradiction|].
                setoid_rewrite set_type_eq2.
                apply set_type_eq in x_eq.
                cbn in x_eq.
                rewrite <- x_eq.
                apply set_type_eq.
                apply f_equal.
                apply set_type_eq.
                reflexivity.
    -   assert (∀ a, initial_segment n [f a|]) as f_in.
        {
            intros a.
            split.
            -   rewrite <- nat_lt_suc_le.
                exact [|f a].
            -   intros eq.
                apply a_nex.
                exists a.
                exact eq.
        }
        specialize (IHn U (λ a, [_|f_in a])).
        apply IHn.
        split.
        intros a b.
        setoid_rewrite set_type_eq2.
        rewrite set_type_eq.
        apply inj.
Qed.

Theorem nat_not_finite : ¬simple_finite nat.
Proof.
    intros [n [f f_inj]].
    revert f f_inj.
    nat_induction n; intros; [>contradiction (nat_lt_0_false (f 0))|].
    classic_case (∃ a, [f a|] = n) as [[a a_eq]|a_nex].
    -   pose (g x := If x < a then [f x|] else [f (nat_suc x)|]).
        assert (∀ x, initial_segment n (g x)) as g_in.
        {
            intros x.
            split.
            -   rewrite <- nat_lt_suc_le.
                unfold g.
                case_if.
                +   exact [|f x].
                +   exact [|f (nat_suc x)].
            -   intros contr.
                rewrite <- a_eq in contr.
                unfold g in contr.
                case_if [ltq|leq].
                +   rewrite set_type_eq in contr.
                    apply inj in contr.
                    subst.
                    contradiction (irrefl _ ltq).
                +   rewrite set_type_eq in contr.
                    apply inj in contr.
                    subst a.
                    exact (leq (nat_lt_suc x)).
        }
        apply (IHn (λ x, [_|g_in x])).
        split.
        intros x y eq.
        setoid_rewrite set_type_eq2 in eq.
        unfold g in eq.
        case_if [x_lt|x_le]; case_if [y_lt|y_le];
                rewrite set_type_eq in eq; apply inj in eq.
        +   exact eq.
        +   rewrite nlt_le in y_le.
            pose proof (lt_le_trans x_lt y_le) as ltq.
            rewrite eq in ltq.
            rewrite <- nle_lt in ltq.
            contradiction (ltq (nat_le_suc y)).
        +   rewrite nlt_le in x_le.
            pose proof (lt_le_trans y_lt x_le) as ltq.
            rewrite <- eq in ltq.
            rewrite <- nle_lt in ltq.
            contradiction (ltq (nat_le_suc x)).
        +   rewrite nat_suc_eq in eq.
            exact eq.
    -   assert (∀ a, initial_segment n [f a|]) as f_in.
        {
            intros a.
            split.
            -   rewrite <- nat_lt_suc_le.
                exact [|f a].
            -   intros contr.
                apply a_nex.
                exists a.
                exact contr.
        }
        apply (IHn (λ x, [_|f_in x])).
        split.
        intros a b eq.
        setoid_rewrite set_type_eq2 in eq.
        rewrite set_type_eq in eq.
        apply inj in eq.
        exact eq.
Qed.

Section MinMax.

Context {U : Type}.
Hypothesis U_fin : simple_finite U.

Section Min.

Context `{TotalOrder U}.

Theorem simple_finite_min : U → ∃ m : U, ∀ a, m ≤ a.
Proof.
    intros z.
    classic_contradiction contr.
    assert (∀ m : U, ∃ a, a < m) as lt_ex.
    {
        intros m.
        rewrite not_ex in contr.
        specialize (contr m).
        rewrite not_all in contr.
        destruct contr as [a ltq].
        rewrite nle_lt in ltq.
        exists a.
        exact ltq.
    }
    clear contr.
    pose (f := fix build (n : nat) :=
        match n with
        | nat_zero => z
        | nat_suc n' => ex_val (lt_ex (build n'))
        end).
    apply simple_finite_bij in U_fin as [n [g g_bij]].
    pose (h x := g (f x)).
    assert (Injective h) as h_inj.
    {
        unfold h.
        apply inj_comp; [>|apply g_bij].
        split.
        assert (∀ n, f (nat_suc n) < f n) as lt.
        {
            intros m.
            unfold f at 1; fold f.
            rewrite_ex_val a a_lt.
            exact a_lt.
        }
        assert (∀ a b, a < b → f a ≠ f b) as wlog.
        {
            intros a b ltq eq.
            assert (f b < f a) as ltq'.
            {
                clear eq.
                apply nat_lt_ex in ltq as [c c_eq]; subst b.
                nat_induction c.
                -   rewrite plus_comm.
                    apply lt.
                -   rewrite nat_plus_rsuc.
                    apply (trans (lt _)).
                    exact IHc.
            }
            rewrite eq in ltq'.
            contradiction (irrefl _ ltq').
        }
        intros a b eq.
        destruct (trichotomy a b) as [[ltq|eq']|ltq].
        -   apply wlog in ltq.
            contradiction.
        -   exact eq'.
        -   apply wlog in ltq.
            symmetry in eq.
            contradiction.
    }
    clearbody h.
    clear - h_inj.
    apply nat_not_finite.
    exists n, h.
    exact h_inj.
Qed.

End Min.

Context `{TotalOrder U}.

Theorem simple_finite_max : U → ∃ m : U, ∀ a, a ≤ m.
Proof.
    intros z.
    make_dual_op le.
    pose (UO' := {|le := dual_op le|}).
    pose proof (simple_finite_min (UO := UO') z) as [m m_least].
    exists m.
    apply m_least.
Qed.

End MinMax.
