Require Import init.

Require Export ring_ideal.
Require Export domain_category.
Require Import factorization.
Require Import noetherian.

Require Import gcd.
Require Import mult_div.
Require Import nat.
Require Import set.
Require Import unordered_list.
Require Import order_minmax.

Class PrincipleIdealDomain (U : IntegralDomain) := {
    ideal_principle : ∀ I : CIdeal (domain_to_cring U), principle_ideal I
}.

Section PrincipleIdeal.

Context {U : IntegralDomain} `{PrincipleIdealDomain U}.

Global Instance pid_noetherian : Noetherian U.
Proof.
    split.
    intros In I_sub.
    assert (∀ m n, m ≤ n → cideal_set (In m) ⊆ cideal_set (In n)) as I_sub2.
    {
        intros m n leq.
        apply nat_le_ex in leq as [c eq].
        subst n.
        nat_induction c.
        -   rewrite plus_rid.
            apply refl.
        -   apply (trans (IHc)).
            rewrite nat_plus_rsuc.
            apply I_sub.
    }
    pose (I x := ∃ n, cideal_set (In n) x).
    assert (∃ a, I a) as I_nempty.
    {
        exists 0.
        exists 0.
        apply (cideal_zero (In 0)).
    }
    assert (∀ a b, I a → I b → I (a + b)) as I_plus.
    {
        intros a b [m Ia] [n Ib].
        exists (max m n).
        apply (cideal_plus (In (max m n))).
        -   apply (I_sub2 m); [>|exact Ia].
            apply lmax.
        -   apply (I_sub2 n); [>|exact Ib].
            apply rmax.
    }
    assert (∀ a b, I a → I (a * b)) as I_mult.
    {
        intros a b [n Ia].
        exists n.
        apply (cideal_mult (In n)).
        exact Ia.
    }
    pose (I' := make_cideal I I_nempty I_plus I_mult).
    pose proof (ideal_principle I') as [a0 I'_eq].
    assert (cideal_set I' a0) as [n0 Ia0].
    {
        rewrite I'_eq.
        apply cideal_generated_by_in.
        reflexivity.
    }
    exists n0.
    intros n n_ge.
    apply cideal_eq_set.
    apply antisym.
    1: apply (I_sub2 _ _ n_ge).
    assert (cideal_set (In n) ⊆ I) as sub1.
    {
        intros a Ia.
        exists n.
        exact Ia.
    }
    apply (trans sub1).
    intros a Ia.
    change (I a) with (I' a) in Ia.
    rewrite I'_eq in Ia.
    destruct Ia as [l a_eq].
    rewrite a_eq; clear a a_eq.
    induction l as [|a l] using ulist_induction.
    -   rewrite ulist_image_end, ulist_sum_end.
        apply cideal_zero.
    -   rewrite ulist_image_add, ulist_sum_add; cbn.
        apply (cideal_plus (In n0)); [>clear IHl|exact IHl].
        destruct a as [a1 [a2 a2_eq]]; cbn.
        apply (cideal_mult (In n0)).
        rewrite singleton_eq in a2_eq; subst.
        exact Ia0.
Qed.

#[refine]
Local Instance pid_gcd : GCDDomain (domain_to_cring U) := {
    gcd (a b : domain_to_cring U) := ex_val (ideal_principle
        (cideal_generated_by (❴a, b❵)))
}.
Proof.
-   intros a b.
    rewrite_ex_val d d_eq.
    split.
    +   rewrite <- (principle_ideal_div d).
        rewrite <- d_eq.
        apply cideal_generated_by_in.
        left.
        reflexivity.
    +   rewrite <- (principle_ideal_div d).
        rewrite <- d_eq.
        cbn.
        apply cideal_generated_by_in.
        right.
        reflexivity.
-   intros a b ab d' [d'a d'b].
    rewrite_ex_val d d_eq.
    assert (cideal_set (principle_ideal_by d) d) as d_in.
    {
        rewrite principle_ideal_div.
        apply refl.
    }
    rewrite <- d_eq in d_in.
    destruct d_in as [l eq].
    subst d.
    clear d_eq.
    induction l as [|c l] using ulist_induction.
    +   rewrite ulist_image_end, ulist_sum_end.
        apply divides_zero.
    +   rewrite ulist_image_add, ulist_sum_add.
        apply plus_stays_divides; [>clear IHl|exact IHl].
        destruct c as [c1 [c2 c2_eq]]; cbn.
        apply mult_factors_extend.
        unfold list_to_set, union in c2_eq; cbn in c2_eq.
        destruct c2_eq; subst c2; assumption.
Qed.

Global Instance pid_factorization : UniqueFactorizationDomain U.
Proof.
    apply div_factorization_ufd.
    intros x x_nz.
    pose proof (noetherian_factors x x_nz) as [l [l_irr l_eq]].
    exists l.
    split; [>|exact l_eq].
    clear l_eq.
    ulist_prop_induction l l_irr as p p_irr IHl.
    -   apply ulist_prop_end.
    -   rewrite ulist_prop_add.
        split; [>|exact IHl].
        apply div_irreducible_prime.
        exact p_irr.
Qed.

End PrincipleIdeal.
