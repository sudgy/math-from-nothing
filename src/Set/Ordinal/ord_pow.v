Require Import init.

Require Import set.
Require Import function.
Require Import nat.
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
Proof.
    intros A.
    equiv_get_value A.
    unfold zero, one; cbn.
    unfold nat_to_ord, ord_pow; equiv_simpl.
    pose proof (nat_lt_suc 0) as z_gt.
    exists (λ _, [0|z_gt]).
    split.
    1: split; split.
    -   intros a b eq.
        apply ord_pow_eq.
        intros x.
        contradiction (nat_lt_0_false x).
    -   intros z.
        pose (f (x : ord_U (nat_to_ord_type 0))
            := False_rect (ord_U A) (nat_lt_0_false x)).
        assert (ord_fin_support f) as f_fin.
        {
            unfold ord_fin_support.
            assert (|set_type (λ x, f x ≠ ord_zero (f x))| = 0) as eq.
            {
                apply card_false_0.
                intros [x C0]; clear C0.
                contradiction (nat_lt_0_false x).
            }
            rewrite eq; clear eq.
            apply nat_is_finite.
        }
        exists (make_ord_pow f f_fin).
        destruct z as [z z_lt].
        apply set_type_eq; cbn.
        apply nat_lt_one_eq in z_lt.
        exact z_lt.
    -   intros F G.
        assert (F = G) as eq.
        {
            apply ord_pow_eq.
            intros x.
            contradiction (nat_lt_0_false x).
        }
        subst.
        split; intro.
        +   apply refl.
        +   pose proof (ord_pow_wo A (nat_to_ord_type 0)) as C.
            destruct (connex G G); assumption.
Qed.

Theorem ord_pow_suc : ∀ α β, α ^ (β + 1) = α ^ β * α.
Proof.
    intros A B.
    equiv_get_value A B.
    unfold one; cbn.
    unfold nat_to_ord, plus, mult, ord_pow; equiv_simpl.
    pose (AB := {|
        ord_U := ord_U B + set_type (λ m : nat, m < 1);
        ord_le := ord_plus_le B (nat_to_ord_type 1);
        ord_antisym := ord_plus_antisym B (nat_to_ord_type 1);
        ord_wo := ord_plus_wo B (nat_to_ord_type 1)
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
        split.
        intros a b eq.
        inversion eq as [eq2].
        apply set_type_eq; exact eq2.
    }
    pose proof (nat_lt_suc 0) as z_gt.
    exists (λ f, (make_ord_pow (F f) (F_fin f), ord_pow_f f (inr [0|z_gt]))).
    split.
    1: split; split.
    -   intros C D eq.
        inversion eq as [[eq1 eq2]].
        unfold F in eq1.
        pose proof (func_eq _ _ eq1) as eq1'; cbn in eq1'.
        apply ord_pow_eq.
        intros [x|x].
        +   exact (eq1' x).
        +   destruct x as [x x_gt].
            pose proof (nat_lt_one_eq x x_gt) as x0.
            subst x.
            rewrite (proof_irrelevance x_gt z_gt).
            exact eq2.
    -   intros [y1 y2].
        pose (f (x : ord_U (B ⊕ nat_to_ord_type 1)) :=
            match x with
            | inl b => ord_pow_f y1 b
            | inr _ => y2
            end).
        assert (ord_fin_support f) as f_fin.
        {
            unfold ord_fin_support; cbn.
            pose proof (ord_pow_fin y1) as y1_fin.
            pose proof (fin_nat_ex _ y1_fin) as [n n_eq].
            apply (le_lt_trans2 (nat_is_finite (nat_suc n))).
            symmetry in n_eq.
            unfold nat_to_card in n_eq; equiv_simpl in n_eq.
            destruct n_eq as [g g_inj].
            unfold nat_to_card, le; equiv_simpl.
            assert (∀ x, f (inl x) ≠ ord_zero (f (inl x)) →
                ord_pow_f y1 x ≠ ord_zero (ord_pow_f y1 x)) as in_g.
            {
                intros x x_eq.
                exact x_eq.
            }
            assert (∀ x : set_type (λ x, x < n), [x|] < nat_suc n) as g_in.
            {
                intros [x x_lt].
                exact (trans x_lt (nat_lt_suc n)).
            }
            pose proof (nat_lt_suc n) as n_lt.
            exists (λ (x : set_type (λ y : ord_U B + set_type (λ m : nat, m<1),
                    f y ≠ ord_zero (f y))),
                match x with
                | make_set_type_val (inl b) H =>
                    let res := g [b | in_g b H] in [[res|] | g_in res]
                | make_set_type_val (inr _) _ =>
                    make_set_type_val (S := (λ x, x < nat_suc n)) n n_lt
                end).
            split.
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
                apply nat_lt_one_eq in a_lt.
                apply nat_lt_one_eq in b_lt.
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
                pose proof (ord_mult_wo (A ⊙ B) A) as C.
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
                    apply nat_lt_one_eq in x_eq.
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
                        apply nat_lt_one_eq in y_lt.
                        exact y_lt.
            *   destruct leq as [eq2|leq].
                --  left.
                    intros [x|x].
                    ++  cbn in eq2.
                        apply eq2.
                    ++  destruct x as [x x_lt].
                        pose proof (nat_lt_one_eq _ x_lt); subst x.
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
                    ++  pose proof (nat_lt_one_eq _ y_lt); subst y.
                        rewrite (proof_irrelevance _ z_gt).
                        exact eq.
Qed.

Theorem ord_pow_from_0 : ∀ α, 0 < α → 0 ^ α = 0.
Proof.
    intros A A_nz.
    equiv_get_value A.
    assert (ord_U A) as a.
    {
        classic_contradiction contr.
        apply ord_false_0 in contr.
        rewrite <- contr in A_nz.
        destruct A_nz; contradiction.
    }
    unfold ord_pow, zero; cbn; unfold nat_to_ord; equiv_simpl.
    assert (ord_pow_type (nat_to_ord_type 0) A → False) as no_pow.
    {
        intros [f f_fin].
        contradiction (nat_lt_0_false (f a)).
    }
    exists (empty_function _ _ no_pow).
    split.
    -   apply empty_bij.
        apply nat_lt_0_false.
    -   intros x y.
        contradiction (no_pow x).
Qed.

Theorem ord_pow_from_1 : ∀ α, 1 ^ α = 1.
Proof.
    intros A.
    equiv_get_value A.
    unfold ord_pow, one; cbn; unfold nat_to_ord; equiv_simpl.
    assert ((zero (U := nat)) < 1) as one_pos by apply nat_pos2.
    exists (λ f, [0|one_pos]).
    split.
    split; split.
    -   intros [f f_fin] [g g_fin] eq; clear eq.
        assert (f = g) as eq.
        {
            apply functional_ext.
            intros x.
            apply set_type_eq.
            pose proof [|f x] as fz; cbn in fz.
            apply nat_lt_one_eq in fz.
            pose proof [|g x] as gz; cbn in gz.
            apply nat_lt_one_eq in gz.
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
        pose (f (x : ord_U A) := [0|one_pos] : ord_U (nat_to_ord_type 1)).
        assert (finite (|set_type (λ x, f x ≠ ord_zero (f x))|)) as fin.
        {
            assert (|set_type (λ x, f x ≠ ord_zero (f x))| = 0) as eq.
            {
                unfold zero; cbn; unfold nat_to_card; equiv_simpl.
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
                    apply all_neg_eq in z_eq.
                    exact z_eq.
                }
                assert (set_type (λ x, f x ≠ ord_zero (f x)) → False) as fa.
                {
                    intros [a a_neq].
                    apply a_neq.
                    apply eq.
                }
                exists (empty_function _ _ fa).
                apply empty_bij.
                apply nat_lt_0_false.
            }
            rewrite eq.
            apply nat_is_finite.
        }
        exists (make_ord_pow f fin).
        destruct x as [x x_lt].
        apply set_type_eq; cbn.
        apply nat_lt_one_eq in x_lt.
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
            apply nat_lt_one_eq in fz.
            pose proof [|ord_pow_f g x] as gz.
            cbn in gz.
            apply nat_lt_one_eq in gz.
            rewrite <- fz, <- gz.
            reflexivity.
Qed.
Close Scope ord_scope.
