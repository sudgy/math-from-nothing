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
    pose (S' α := ¬S α).
    assert (∃ β, S' β) as S'_nempty by (exists α; exact contr).
    pose proof (well_ordered S' S'_nempty) as [β [S'β β_min]].
    apply S'β.
    apply S_all.
    intros γ γ_lt.
    classic_contradiction S'γ.
    specialize (β_min _ S'γ).
    destruct (lt_le_trans γ_lt β_min); contradiction.
Qed.

(* I don't like how most of the proofs relating to transfinite recursion are
* repeated, but that's because in one case it's working on an initial segment of
* U, while on the other case it's working on all of U.  Maybe there's some way
* of generalizing it better.
*)
#[universes(template)]
Record transfinite_recursion_domain X := make_trd {
    trd_p : U;
    trd_f : set_type (λ x, x < trd_p) → X;
}.

Local Notation "'trd'" := transfinite_recursion_domain.
Global Arguments trd_p {X}.
Global Arguments trd_f {X}.

Theorem transfinite_recursion_unique : ∀ X (f : trd X → X),
    ∀ g h : U → X,
        (∀ n, g n = f (make_trd X n (λ x, g [x|]))) →
        (∀ n, h n = f (make_trd X n (λ x, h [x|]))) →
        g = h.
Proof.
    intros X f g h g_ind h_ind.
    apply functional_ext.
    intros x.
    induction x as [x IHx] using transfinite_induction.
    rewrite g_ind, h_ind.
    apply f_equal.
    apply f_equal.
    apply functional_ext.
    intros [y y_lt]; cbn.
    apply IHx.
    exact y_lt.
Qed.

Theorem transfinite_recursion_unique2 : ∀ X (f : trd X → X),
    ∀ α,
    ∀ g h : (set_type (λ x, x < α)) → X,
        (∀ n, g n = f (make_trd X [n|] (λ x, g [[x|] | trans [|x] [|n]]))) →
        (∀ n, h n = f (make_trd X [n|] (λ x, h [[x|] | trans [|x] [|n]]))) →
        g = h.
    intros X f α g h g_ind h_ind.
    apply functional_ext.
    intros [x x_lt].
    induction x as [x IHx] using transfinite_induction.
    rewrite g_ind, h_ind.
    apply f_equal.
    apply f_equal.
    apply functional_ext.
    intros [y y_lt]; cbn.
    apply IHx.
    exact y_lt.
Qed.

End TransfiniteInduction.
Section TransfiniteRecursion.

Context {U} `{WellOrder U}.

Local Notation "'trd'" := transfinite_recursion_domain.

Theorem transfinite_recursion : ∀ X (f : trd X → X),
    ∃ g : U → X,
    ∀ n, g n = f (make_trd X n (λ x, g [x|])).
Proof.
    intros X f.
    assert (∀ α, ∃ g : set_type (λ x, x < α) → X,
        ∀ n, g n = f (make_trd X [n|] (λ x, g [[x|] | trans [|x] [|n]])))
        as part_ex.
    {
        intros α.
        induction α as [α IHα] using transfinite_induction.
        pose (g (n : set_type (λ x, x < α)) := ex_val (IHα [n|] [|n])).
        exists (λ n, f (make_trd X [n|] (g n))).
        intros [n n_lt]; cbn.
        do 2 apply f_equal.
        apply functional_ext.
        intros [x x_lt]; cbn.
        unfold g at 1.
        rewrite_ex_val h1 h1_eq.
        rewrite h1_eq.
        do 2 apply f_equal.
        unfold g.
        rewrite_ex_val h2 h2_eq.
        apply (transfinite_recursion_unique2 _ f).
        -   intros a; cbn.
            rewrite h1_eq; cbn.
            do 2 apply f_equal.
            apply functional_ext.
            intros b.
            do 2 apply f_equal.
            apply proof_irrelevance.
        -   intros a.
            rewrite h2_eq.
            reflexivity.
    }
    exists (λ α, f (make_trd X α (ex_val (part_ex α)))).
    intros n.
    do 2 apply f_equal.
    apply functional_ext.
    intros x.
    rewrite_ex_val h1 h1_eq.
    rewrite h1_eq.
    do 2 apply f_equal.
    rewrite_ex_val h2 h2_eq.
    apply (transfinite_recursion_unique2 _ f).
    -   intros a; cbn.
        rewrite h1_eq; cbn.
        do 2 apply f_equal.
        apply functional_ext.
        intros b.
        do 2 apply f_equal.
        apply proof_irrelevance.
    -   intros a.
        rewrite h2_eq.
        reflexivity.
Qed.

End TransfiniteRecursion.

Arguments transfinite_recursion_domain U {UO}.
