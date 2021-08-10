Require Import init.

Require Import set.
Require Import function.
Require Import nat0.
Require Export ord_base.
Require Import ord_order.
Require Import ord_plus.
Require Import ord_mult.
Require Import ord_induction.
Require Import ord_pow_def.
Require Import card.

Open Scope card_scope.
Open Scope ord_scope.

Theorem ord_pow_0 : ∀ α, α ^ 0 = 1.
    intros A.
    equiv_get_value A.
    unfold zero, one; cbn.
    unfold nat0_to_ord, ord_pow; equiv_simpl.
    pose proof (nat0_lt_suc 0) as z_gt.
    exists (λ _, [0|z_gt]).
    split.
    1: split.
    -   intros a b eq.
        apply ord_pow_eq.
        intros x.
        contradiction (nat0_lt_0_false x).
    -   intros z.
        pose (f (x : ord_U (nat0_to_ord_type 0))
            := False_rect (ord_U A) (nat0_lt_0_false x)).
        assert (ord_fin_support f) as f_fin.
        {
            unfold ord_fin_support.
            assert (|set_type (λ x, f x ≠ ord_zero (f x))| = 0) as eq.
            {
                apply card_false_0.
                intros [x C0]; clear C0.
                contradiction (nat0_lt_0_false x).
            }
            rewrite eq; clear eq.
            apply nat0_is_finite.
        }
        exists (make_ord_pow f f_fin).
        destruct z as [z z_lt].
        apply set_type_eq; cbn.
        apply nat0_lt_1 in z_lt.
        exact z_lt.
    -   intros F G.
        assert (F = G) as eq.
        {
            apply ord_pow_eq.
            intros x.
            contradiction (nat0_lt_0_false x).
        }
        subst.
        split; intro.
        +   apply refl.
        +   pose proof (ord_pow_wo A (nat0_to_ord_type 0)) as [[C]].
            destruct (connex G G); assumption.
Qed.

Theorem ord_pow_suc : ∀ α β, α ^ (β + 1) = α ^ β * α.
    intros A B.
    equiv_get_value A B.
    unfold one; cbn.
    unfold nat0_to_ord, plus, mult, ord_pow; equiv_simpl.
    pose (AB := {|
        ord_U := ord_U B + set_type (λ m : nat0, m < 1);
        ord_le := ord_plus_le B (nat0_to_ord_type 1);
        ord_wo := ord_plus_wo B (nat0_to_ord_type 1)
    |}).
    fold AB.
    pose (F (f : ord_pow_type A AB) (b : ord_U B) := ord_pow_f f (inl b)).
    assert (∀ f, ord_fin_support (F f)) as F_fin.
    {
        intros f.
        pose proof (ord_pow_fin f) as f_fin.
        unfold ord_fin_support, finite in *.
        apply (le_lt_trans2 f_fin); clear f_fin.
        unfold le; equiv_simpl.
        assert (∀ a : set_type (λ x, F f x ≠ ord_zero (F f x)),
            ord_pow_f f (inl [a|]) ≠ ord_zero (ord_pow_f f (inl [a|]))) as g_in.
        {
            intros [a a_neq]; cbn.
            unfold F in a_neq.
            exact a_neq.
        }
        exists (λ x, [inl [x|]|g_in x]).
        intros a b eq.
        inversion eq as [eq2].
        apply set_type_eq; exact eq2.
    }
    pose proof (nat0_lt_suc 0) as z_gt.
    exists (λ f, (make_ord_pow (F f) (F_fin f), ord_pow_f f (inr [0|z_gt]))).
    split.
    1: split.
    -   intros C D eq.
        inversion eq as [[eq1 eq2]].
        unfold F in eq1.
        pose proof (func_eq _ _ eq1) as eq1'; cbn in eq1'.
        apply ord_pow_eq.
        intros [x|x].
        +   exact (eq1' x).
        +   destruct x as [x x_gt].
            pose proof (nat0_lt_1 x x_gt) as x0.
            subst x.
            rewrite (proof_irrelevance x_gt z_gt).
            exact eq2.
    -   intros [y1 y2].
        pose (f (x : ord_U (B ⊕ nat0_to_ord_type 1)) :=
            match x with
            | inl b => ord_pow_f y1 b
            | inr _ => y2
            end).
        assert (ord_fin_support f) as f_fin.
        {
            unfold ord_fin_support; cbn.
            pose proof (ord_pow_fin y1) as y1_fin.
            pose proof (fin_nat0_ex _ y1_fin) as [n n_eq].
            apply (le_lt_trans2 (nat0_is_finite (nat0_suc n))).
            symmetry in n_eq.
            unfold nat0_to_card in n_eq; equiv_simpl in n_eq.
            destruct n_eq as [g g_inj].
            unfold nat0_to_card, le; equiv_simpl.
            assert (∀ x, f (inl x) ≠ ord_zero (f (inl x)) →
                ord_pow_f y1 x ≠ ord_zero (ord_pow_f y1 x)) as in_g.
            {
                intros x x_eq.
                exact x_eq.
            }
            assert (∀ x : set_type (λ x, x < n), [x|] < nat0_suc n) as g_in.
            {
                intros [x x_lt].
                exact (trans x_lt (nat0_lt_suc n)).
            }
            pose proof (nat0_lt_suc n) as n_lt.
            exists (λ (x : set_type (λ y : ord_U B + set_type (λ m : nat0, m<1),
                    f y ≠ ord_zero (f y))),
                match x with
                | make_set_type_val (inl b) H =>
                    let res := g [b | in_g b H] in [[res|] | g_in res]
                | make_set_type_val (inr _) _ =>
                    make_set_type_val (S := (λ x, x < nat0_suc n)) n n_lt
                end).
            intros [[a|a] a_eq] [[b|b] b_eq] eq; cbn in *.
            all: apply set_type_eq; cbn.
            all: try apply f_equal.
            all: inversion eq as [eq2].
            -   apply set_type_eq in eq2.
                apply g_inj in eq2.
                inversion eq2.
                reflexivity.
            -   pose proof [|g [a |in_g a a_eq]] as ltq; cbn in ltq.
                rewrite eq2 in ltq.
                destruct ltq; contradiction.
            -   pose proof [|g [b |in_g b b_eq]] as ltq; cbn in ltq.
                rewrite <- eq2 in ltq.
                destruct ltq; contradiction.
            -   destruct a as [a a_lt], b as [b b_lt].
                apply set_type_eq; cbn.
                apply nat0_lt_1 in a_lt.
                apply nat0_lt_1 in b_lt.
                subst.
                reflexivity.
        }
        exists (make_ord_pow f f_fin).
        cbn.
        apply f_equal2; try reflexivity.
        apply ord_pow_eq; cbn.
        reflexivity.
    -   intros C D.
        split.
        +   intros [eq|leq].
            *   pose proof (ord_pow_eq eq) as eq2; subst.
                pose proof (ord_mult_wo (A ⊙ B) A) as [[C]].
                assert (Reflexive (ord_mult_le (A ⊙ B) A)).
                {
                    split; intros x.
                    destruct (connex x x); assumption.
                }
                apply refl.
            *   destruct leq as [x [x_lt x_gt]].
                unfold ord_mult_le; cbn.
                destruct x as [x|x].
                --  right.
                    split.
                    ++  right; cbn.
                        exists x.
                        split.
                        **  exact x_lt.
                        **  intros y y_lt.
                            specialize (x_gt (inl y)).
                            apply x_gt.
                            split; try apply y_lt.
                            intro contr.
                            inversion contr.
                            subst x.
                            destruct y_lt; contradiction.
                    ++  apply x_gt.
                        split; cbn.
                        **  exact true.
                        **  intro contr; inversion contr.
                --  left.
                    destruct x as [x x_lt2]; cbn in *.
                    pose proof x_lt2 as x_eq.
                    apply nat0_lt_1 in x_eq.
                    subst x.
                    rewrite (proof_irrelevance _ x_lt2).
                    exact x_lt.
        +   intros [[leq neq]|[leq eq]].
            *   right.
                exists (inr [0|z_gt]).
                split.
                --  split; assumption.
                --  intros [y|y] [leq2 neq2].
                    ++  cbn in leq2.
                        contradiction.
                    ++  cbn in leq2.
                        exfalso; apply neq2.
                        apply f_equal.
                        destruct y as [y y_lt].
                        apply set_type_eq; cbn.
                        clear leq2 neq2.
                        apply nat0_lt_1 in y_lt.
                        exact y_lt.
            *   destruct leq as [eq2|leq].
                --  left.
                    intros [x|x].
                    ++  cbn in eq2.
                        apply eq2.
                    ++  destruct x as [x x_lt].
                        pose proof (nat0_lt_1 _ x_lt); subst x.
                        rewrite (proof_irrelevance _ z_gt).
                        exact eq.
                --  right.
                    destruct leq as [x [x_lt x_gt]]; cbn in *.
                    exists (inl x).
                    split; try assumption.
                    intros [y|[y y_lt]] ltq.
                    ++  apply x_gt.
                        split; try apply ltq.
                        intro contr; subst.
                        destruct ltq; contradiction.
                    ++  pose proof (nat0_lt_1 _ y_lt); subst y.
                        rewrite (proof_irrelevance _ z_gt).
                        exact eq.
Qed.

Theorem ord_pow_from_0 : ∀ α, 0 < α → 0 ^ α = 0.
    intros A A_nz.
    equiv_get_value A.
    assert (ord_U A) as a.
    {
        classic_contradiction contr.
        apply ord_false_0 in contr.
        rewrite <- contr in A_nz.
        destruct A_nz; contradiction.
    }
    unfold ord_pow, zero; cbn; unfold nat0_to_ord; equiv_simpl.
    assert (ord_pow_type (nat0_to_ord_type 0) A → False) as no_pow.
    {
        intros [f f_fin].
        contradiction (nat0_lt_0_false (f a)).
    }
    exists (empty_function _ _ no_pow).
    split.
    -   apply empty_bij.
        apply nat0_lt_0_false.
    -   intros x y.
        contradiction (no_pow x).
Qed.

Theorem ord_pow_from_1 : ∀ α, 1 ^ α = 1.
    intros A.
    equiv_get_value A.
    unfold ord_pow, one; cbn; unfold nat0_to_ord; equiv_simpl.
    assert ((zero (U := nat0)) < 1) as one_pos by apply nat0_zero_lt_suc.
    exists (λ f, [0|one_pos]).
    split.
    split.
    -   intros [f f_fin] [g g_fin] eq; clear eq.
        assert (f = g) as eq.
        {
            apply functional_ext.
            intros x.
            apply set_type_eq.
            pose proof [|f x] as fz; cbn in fz.
            apply nat0_lt_1 in fz.
            pose proof [|g x] as gz; cbn in gz.
            apply nat0_lt_1 in gz.
            rewrite <- fz, <- gz.
            reflexivity.
        }
        subst.
        rewrite (proof_irrelevance f_fin g_fin).
        reflexivity.
    -   intros x.
        assert ((zero (U := ord)) < 1) as ord_one_pos.
        {
            split.
            -   apply ord_le_zero.
            -   apply ord_not_trivial.
        }
        pose (f (x : ord_U A) := [0|one_pos] : ord_U (nat0_to_ord_type 1)).
        assert (finite (|set_type (λ x, f x ≠ ord_zero (f x))|)) as fin.
        {
            assert (|set_type (λ x, f x ≠ ord_zero (f x))| = 0) as eq.
            {
                unfold zero; cbn; unfold nat0_to_card; equiv_simpl.
                assert (∀ x, f x = ord_zero (f x)) as eq.
                {
                    unfold f.
                    intros y; clear y.
                    unfold ord_zero.
                    unpack_ex_val z z_ex z_eq.
                    destruct z as [z z_lt]; cbn in *.
                    rewrite z_ex.
                    specialize (z_eq [0|one_pos]).
                    cbn in z_eq.
                    apply set_type_eq; cbn.
                    unfold le in z_eq; cbn in z_eq.
                    apply nat0_le_zero_eq in z_eq.
                    symmetry; exact z_eq.
                }
                assert (set_type (λ x, f x ≠ ord_zero (f x)) → False) as fa.
                {
                    intros [a a_neq].
                    apply a_neq.
                    apply eq.
                }
                exists (empty_function _ _ fa).
                apply empty_bij.
                apply nat0_lt_0_false.
            }
            rewrite eq.
            apply nat0_is_finite.
        }
        exists (make_ord_pow f fin).
        destruct x as [x x_lt].
        apply set_type_eq; cbn.
        apply nat0_lt_1 in x_lt.
        exact x_lt.
    -   intros f g.
        split.
        +   intros; apply refl.
        +   intros leq; clear leq.
            unfold ord_pow_le; cbn.
            left.
            intros x.
            apply set_type_eq.
            pose proof [|ord_pow_f f x] as fz.
            cbn in fz.
            apply nat0_lt_1 in fz.
            pose proof [|ord_pow_f g x] as gz.
            cbn in gz.
            apply nat0_lt_1 in gz.
            rewrite <- fz, <- gz.
            reflexivity.
Qed.
(*
Section OrdPowLim.

Variables α β : ord.

Let S γ := ∃ δ, 0 < δ ∧ δ < β ∧ γ = α ^ δ.
Hypothesis β_lim : lim_ord β.

Lemma ord_pow_lim_upper : is_upper_bound le S (α ^ β).
    intros γ [δ [δ_nz [δ_lt γ_eq]]].
    subst.
    clear S.
    classic_case (0 = α) as [eq|α_nz].
    {
        subst.
        rewrite ord_pow_from_0 by exact δ_nz.
        apply ord_le_zero.
    }
    classic_case (1 = α) as [eq|α_no].
    {
        subst.
        do 2 rewrite ord_pow_from_1.
        apply refl.
    }
    rename α into A, β into B, δ into C.
    equiv_get_value A B C.
    get_ord_wo A.
    get_ord_wo B.
    unfold le, ord_pow; equiv_simpl.
    rewrite ord_lt_initial in δ_lt.
    destruct δ_lt as [x [f [f_bij f_iso]]].
    right.
    assert (ord_U A) as make_zero.
    {
        classic_contradiction contr.
        apply α_nz.
        apply ord_false_0.
        exact contr.
    }
    assert (∃ a, a ≠ ord_zero make_zero) as one_ex.
    {
        classic_contradiction contr.
        rewrite not_ex in contr.
        setoid_rewrite not_not in contr.
        apply α_no.
        unfold one; cbn; unfold nat0_to_ord; equiv_simpl.
        exists (λ _, ord_zero make_zero).
        split.
        split.
        -   intros [a a_lt] [b b_lt] eq.
            apply set_type_eq; cbn.
            apply nat0_lt_1 in a_lt.
            apply nat0_lt_1 in b_lt.
            subst; reflexivity.
        -   intros b.
            pose proof (nat0_lt_suc 0) as z_lt.
            exists [0|z_lt].
            symmetry.
            apply contr.
        -   intros [a a_lt] [b b_lt].
            split; intro leq.
            +   apply refl.
            +   unfold le; cbn.
                apply nat0_lt_1 in a_lt.
                apply nat0_lt_1 in b_lt.
                subst; apply refl.
    }
    pose proof (well_ordered _ one_ex) as [a [a_neq a_least]].
    pose (g b := If b = x then a else ord_zero make_zero).
    assert (ord_fin_support g) as g_fin.
    {
        admit.
    }
    exists (make_ord_pow g g_fin).
    pose (F (G : ord_pow_type A C) (b : ord_U B) :=
        match (strong_excluded_middle (initial_segment_set B x b)) with
        | strong_or_left H => ord_pow_f G (ex_val (proj2 f_bij [_|H]))
        | _ => ord_zero make_zero
        end).
    assert (∀ G, ord_fin_support (F G)) as F_fin.
    {
        admit.
    }
    assert (∀ G, initial_segment_set (A ⊙ B)
        (make_ord_pow g g_fin) (make_ord_pow (F G) (F_fin G))) as F_lt.
    {
        admit.
    }
    exists (λ G, [_|F_lt G]).
    cbn.
    split.
    split.
    -   intros G1 G2 eq.
        inversion eq as [eq2].
        apply ord_pow_eq.
        intros c.
        unfold F in eq2.
        pose proof (func_eq _ _ eq2) as eq3; cbn in eq3.
        clear eq eq2.
        specialize (eq3 [f c|]).
        destruct (strong_excluded_middle _) as [ltq|leq]; cbn in *.
        +   unfold ex_val in eq3.
            destruct (ex_to_type _) as [c' c'_eq]; cbn in *.
            assert (f c' = f c) as eq.
            {
                rewrite c'_eq.
                apply set_type_eq; cbn.
                reflexivity.
            }
            apply f_bij in eq.
            subst.
            exact eq3.
        +   clear eq3.
            unfold initial_segment_set in leq.
            rewrite not_and in leq.
            rewrite not_not in leq.
            pose proof [|f c] as [leq2 eq].
            destruct leq; contradiction.
    -   intros [G G_lt].
        pose (h (c : ord_U C) := ord_pow_f G [f c|]).
        assert (ord_fin_support h) as h_fin.
        {
            admit.
        }
        exists (make_ord_pow h h_fin).
        apply set_type_eq; cbn.
        apply ord_pow_eq; cbn.
        intros b.
        unfold F; cbn.
        destruct (strong_excluded_middle _) as [ltq|leq].
        +   unfold h.
            apply f_equal.
            unfold ex_val.
            destruct (ex_to_type _) as [b' b'_eq]; cbn.
            rewrite b'_eq.
            reflexivity.
        +   unfold initial_segment_set in G_lt.
            destruct G_lt as [G_le G_neq].
            cbn in G_le.
            destruct G_le as [G_eq|G_le].
            *   exfalso; apply G_neq.
                apply ord_pow_eq.
                exact G_eq.
            *   destruct G_le as [x' [x'_lt x'_gt]].
                cbn in *.
Admitted.

Lemma ord_pow_lim_least : ∀ γ, is_upper_bound le S γ → α ^ β <= γ.
Admitted.

Theorem ord_pow_lim : is_supremum le S (α ^ β).
    split.
    -   apply ord_pow_lim_upper.
    -   apply ord_pow_lim_least.
Qed.

End OrdPowLim.

Close Scope card_scope.

Theorem ord_pow_from_0 : ∀ α, 0 < α → 0 ^ α = 0.
    intros α α_gt.
    induction α using transfinite_induction3.
    -   contradiction (irrefl _ α_gt).
    -   rename H into α_suc, H0 into α_ind.
        unfold suc_ord in α_suc.
        destruct α_suc as [β α_eq].
        rewrite α_eq.
        rewrite ord_pow_suc.
        apply mult_ranni.
    -   rename H into α_lim, H0 into α_ind.
        pose proof (ord_pow_lim 0 α α_lim) as [upper least].
        apply (antisym (op := le)); try apply ord_le_zero.
        apply least.
        intros β [δ [δ_nz [δ_lt β_eq]]].
        rewrite β_eq.
        rewrite (α_ind δ δ_lt δ_nz).
        apply refl.
Qed.
(*
Theorem ord_pow_1 : ∀ α, α ^ 1 = α.
    intros α.
    rewrite <- (plus_lid 1).
    rewrite ord_pow_suc.
    rewrite ord_pow_0.
    apply mult_lid.
Qed.

Theorem ord_pow_from_1 : ∀ α, 1 ^ α = 1.
    intros α.
    induction α using transfinite_induction3.
    -   apply ord_pow_0.
    -   rename H into α_suc, H0 into α_ind.
        destruct α_suc as [β α_eq].
        rewrite α_eq.
        rewrite ord_pow_suc.
        rewrite mult_rid.
        apply α_ind.
        rewrite α_eq.
        apply ord_lt_plus1.
    -   rename H into α_lim, H0 into α_ind.
        pose proof (ord_pow_lim 1 α α_lim) as [upper least].
        apply (antisym (op := le)).
        +   apply least.
            intros β [δ [δ_nz [δ_lt β_eq]]].
            rewrite β_eq.
            rewrite (α_ind δ δ_lt).
            apply refl.
        +   apply upper.
            exists 1.
            repeat split.
            *   apply ord_le_zero.
            *   apply ord_not_trivial.
            *   classic_contradiction ltq.
                rewrite nle_lt in ltq.
                apply (proj1 α_lim).
                apply ord_lt_1.
                exact ltq.
            *   intro contr.
                apply (proj2 α_lim).
                exists 0.
                rewrite plus_lid.
                symmetry; exact contr.
            *   rewrite ord_pow_1.
                reflexivity.
Qed.
*)
*)
Close Scope ord_scope.
