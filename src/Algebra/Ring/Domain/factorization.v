Require Import init.

Require Export mult_div.
Require Import gcd.
Require Import relation.
Require Import set.

Require Export unordered_list.

Class UniqueFactorizationDomain (U : IntegralDomain) := {
    factorization_base : ∀ x : U, 0 ≠ x → ¬unit x →
        ∃ l, ulist_prop prime l ∧ x = ulist_prod l
}.

Arguments factorization_base {U UniqueFactorizationDomain}.

Section UniqueFactorization.

Context {U : IntegralDomain} `{UniqueFactorizationDomain U}.

Theorem div_factorization_base : ∀ x : div_type U, 0 ≠ x → ∃ l,
    ulist_prop prime l ∧ x = ulist_prod l.
Proof.
    intros x x_nz.
    classic_case (1 = x) as [x_o|x_no].
    {
        subst x.
        exists ⟦⟧.
        split.
        -   apply ulist_prop_end.
        -   symmetry; apply ulist_prod_end.
    }
    pose proof (sur to_div x) as [x' x'_eq].
    subst x.
    rewrite <- div_equiv_zero in x_nz.
    rewrite neq_sym in x_no.
    rewrite <- div_equiv_unit in x_no.
    unfold unit in x_no.
    unfold one in x_no; cbn in x_no.
    rewrite <- div_equiv_div in x_no.
    pose proof (factorization_base x' x_nz x_no) as [l [l_prime l_eq]].
    exists (ulist_image to_div l).
    split.
    -   clear l_eq.
        apply (ulist_prop_image prime _ _ _ l_prime).
        intros x x_prime.
        rewrite <- div_equiv_prime.
        exact x_prime.
    -   rewrite l_eq.
        apply (ulist_prod_homo to_div).
Qed.

Theorem div_factorization_unique : ∀ x : div_type U, 0 ≠ x → ∃ l,
    ulist_prop prime l ∧
    x = ulist_prod l ∧
    (∀ l',
        ulist_prop prime l' →
        x = ulist_prod l' →
        l = l').
Proof.
    intros x x_nz.
    pose proof (div_factorization_base x x_nz) as [l [l_prime l_eq]].
    exists l.
    split; [>exact l_prime|].
    split; [>exact l_eq|].
    clear x_nz.
    revert x l_eq.
    ulist_prop_induction l l_prime as p p_prime IHl;
        intros x l_eq l' l'_prime l'_eq.
    {
        destruct l' as [|b l'] using ulist_destruct; [>reflexivity|].
        exfalso.
        rewrite ulist_prod_end in l_eq.
        subst x.
        rewrite ulist_prop_add in l'_prime.
        destruct l'_prime as [b_prime l'_prime].
        apply prime_irreducible in b_prime.
        destruct b_prime as [b_nz [b_nu b_irr]].
        apply b_nu.
        rewrite ulist_prod_add in l'_eq.
        exists (ulist_prod l').
        rewrite mult_comm.
        symmetry; exact l'_eq.
    }
    rewrite ulist_prod_add in l_eq.
    assert (in_ulist l' p) as p_in.
    {
        assert (p ∣ ulist_prod l') as p_div.
        {
            rewrite <- l'_eq.
            exists (ulist_prod l).
            rewrite mult_comm.
            symmetry; exact l_eq.
        }
        destruct p_prime as [p_nz [p_nu p_prime]].
        clear l'_eq.
        ulist_prop_induction l' l'_prime as b b_prime IHl'.
        -   rewrite ulist_prod_end in p_div.
            contradiction.
        -   rewrite ulist_prod_add in p_div.
            apply p_prime in p_div as [p_div|p_div].
            +   destruct p_div as [u b_eq].
                classic_case (unit u) as [uu|unu].
                *   apply div_equiv_unit in uu.
                    subst u.
                    rewrite mult_lid in b_eq.
                    subst b.
                    apply in_ulist_add.
                *   apply prime_irreducible in b_prime as [b_nz [b_nu b_prime]].
                    specialize (b_prime _ _ unu p_nu).
                    symmetry in b_eq; contradiction.
            +   specialize (IHl' p_div).
                rewrite in_ulist_add_eq.
                right; exact IHl'.
    }
    apply in_ulist_split in p_in as [l'' l''_eq]; subst l'; rename l'' into l'.
    apply f_equal.
    apply (IHl _ Logic.eq_refl).
    -   rewrite ulist_prop_add in l'_prime.
        apply l'_prime.
    -   rewrite l_eq in l'_eq.
        rewrite ulist_prod_add in l'_eq.
        apply mult_lcancel in l'_eq; [>|apply p_prime].
        exact l'_eq.
Qed.

Definition factorization x x_nz x_nuni
    := ex_val (factorization_base x x_nz x_nuni).

Theorem factorization_prime : ∀ x x_nz x_nuni,
    ulist_prop prime (factorization x x_nz x_nuni).
Proof.
    intros x x_nz x_nuni.
    apply (ex_proof (factorization_base x x_nz x_nuni)).
Qed.

Theorem factorization_irreducible : ∀ x x_nz x_nuni,
    ulist_prop irreducible (factorization x x_nz x_nuni).
Proof.
    intros x x_nz x_nuni.
    apply (ulist_prop_sub _ prime irreducible).
    -   intros p.
        apply prime_irreducible.
    -   apply factorization_prime.
Qed.

Theorem factorization_eq : ∀ x x_nz x_nuni,
    x = ulist_prod (factorization x x_nz x_nuni).
Proof.
    intros x x_nz x_nuni.
    apply (ex_proof (factorization_base x x_nz x_nuni)).
Qed.

Theorem factorization_uni : ∀ x x_nz x_nuni,
    ∀ l,
        ulist_prop prime l →
        x = ulist_prod l →
        ulist_image to_div l = ulist_image to_div (factorization x x_nz x_nuni).
Proof.
    intros x x_nz x_nuni l l_prime l_eq.
    pose proof x_nz as x_nz'.
    rewrite div_equiv_zero in x_nz'.
    pose proof (div_factorization_unique _ x_nz')
        as [dl [dl_prime [dl_eq dl_uni]]].
    assert (dl = ulist_image to_div l) as eq1.
    {
        apply dl_uni.
        -   apply (ulist_prop_image prime _ _ _ l_prime).
            intros p p_prime.
            rewrite <- div_equiv_prime.
            exact p_prime.
        -   rewrite l_eq.
            apply (ulist_prod_homo to_div).
    }
    assert (dl = ulist_image to_div (factorization x x_nz x_nuni)) as eq2.
    {
        apply dl_uni.
        -   apply (ulist_prop_image prime).
            +   apply factorization_prime.
            +   intros p p_prime.
                rewrite <- div_equiv_prime.
                exact p_prime.
        -   rewrite (factorization_eq x x_nz x_nuni) at 1.
            apply (ulist_prod_homo to_div).
    }
    rewrite <- eq1, <- eq2.
    reflexivity.
Qed.

End UniqueFactorization.
