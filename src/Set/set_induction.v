Require Import init.

Require Export relation.
Require Export set_type.
Require Export set_set.

Section TransfiniteInduction.

Context {U} `{WellOrder U}.

Theorem transfinite_induction :
    ∀ S : U → Prop, (∀ α, (∀ β, β < α → S β) → S α) → ∀ α, S α.
Proof.
    intros S S_all α.
    classic_contradiction contr.
    pose proof (well_ordered (𝐂 S)) as S'_wo.
    prove_parts S'_wo; [>exists α; exact contr|].
    destruct S'_wo as [β [S'β β_min]].
    apply S'β.
    apply S_all.
    intros γ γ_lt.
    classic_contradiction S'γ.
    specialize (β_min _ S'γ).
    contradiction (irrefl _ (lt_le_trans γ_lt β_min)).
Qed.

(* I don't like how most of the proofs relating to transfinite recursion are
* repeated, but that's because in one case it's working on an initial segment of
* U, while on the other case it's working on all of U.  Maybe there's some way
* of generalizing it better.
*)
Variables (X : Type) (f : ∀ p : U, (set_type (λ x, x < p) → X) → X).

Theorem transfinite_recursion_unique :
    ∀ g h : U → X,
    (∀ n, g n = f n (λ x, g [x|])) → (∀ n, h n = f n (λ x, h [x|])) →
    g = h.
Proof.
    intros g h g_ind h_ind.
    apply functional_ext.
    intros x.
    induction x as [x IHx] using transfinite_induction.
    rewrite g_ind, h_ind.
    apply f_equal.
    apply functional_ext.
    intros [y y_lt]; cbn.
    exact (IHx y y_lt).
Qed.

Lemma transfinite_recursion_unique_initial : ∀ α,
    ∀ g h : (set_type (λ x, x < α)) → X,
    (∀ n, g n = f [n|] (λ x, g [[x|] | trans [|x] [|n]])) →
    (∀ n, h n = f [n|] (λ x, h [[x|] | trans [|x] [|n]])) →
    g = h.
Proof.
    intros α g h g_ind h_ind.
    apply functional_ext.
    intros [x x_lt].
    induction x as [x IHx] using transfinite_induction.
    rewrite g_ind, h_ind; cbn.
    apply f_equal.
    apply functional_ext.
    intros [y y_lt]; cbn.
    apply (IHx y y_lt).
Qed.

Lemma transfinite_recursion_part :
    ∀ (g : ∀ n, set_type (λ a, a < n) → X),
    (∀ n a, g n a = f [a|] (λ x, g n [[x|] | trans [|x] [|a]])) →
    ∀ n, g n = λ a, f [a|] (g [a|]).
Proof.
    intros g g_ind n.
    apply functional_ext.
    intros a.
    rewrite g_ind.
    apply f_equal.
    apply transfinite_recursion_unique_initial.
    -   intros x; cbn.
        rewrite g_ind; cbn.
        apply f_equal.
        apply functional_ext.
        intros y.
        do 2 apply f_equal.
        apply proof_irrelevance.
    -   apply g_ind.
Qed.

Lemma transfinite_recursion_part_initial : ∀ (α : U)
    (g : ∀ n : set_type (λ n, n < α), set_type (λ a, a < [n|]) → X),
    (∀ n a, g n a = f [a|] (λ x, g n [[x|] | trans [|x] [|a]])) →
    ∀ n, g n = λ a, f [a|] (g [[a|] | trans [|a] [|n]]).
Proof.
    intros α g g_ind [n n_lt]; cbn.
    apply functional_ext.
    intros a; cbn.
    rewrite g_ind.
    apply f_equal.
    apply transfinite_recursion_unique_initial.
    -   intros x; cbn.
        rewrite g_ind; cbn.
        apply f_equal.
        apply functional_ext.
        intros y.
        do 2 apply f_equal.
        apply proof_irrelevance.
    -   intros x.
        apply g_ind.
Qed.

Lemma transfinite_recursion_initial :
    ∀ α, ∃ g : set_type (λ x, x < α) → X,
    ∀ n, g n = f [n|] (λ x, g [[x|] | trans [|x] [|n]]).
Proof.
    intros α.
    induction α as [α IHα] using transfinite_induction.
    exists (λ n, f [n|] (ex_val (IHα [n|] [|n]))).
    intros n.
    apply f_equal.
    apply (transfinite_recursion_part_initial _ (λ x, ex_val (IHα [x|] [|x]))).
    intros a.
    rewrite_ex_val h h_eq.
    exact h_eq.
Qed.

Theorem transfinite_recursion : ∃ g : U → X, ∀ n, g n = f n (λ x, g [x|]).
Proof.
    exists (λ α, f α (ex_val (transfinite_recursion_initial α))).
    intros n.
    apply f_equal.
    apply (transfinite_recursion_part
        (λ x, ex_val (transfinite_recursion_initial x))).
    intros α.
    rewrite_ex_val h h_eq.
    exact h_eq.
Qed.

End TransfiniteInduction.
