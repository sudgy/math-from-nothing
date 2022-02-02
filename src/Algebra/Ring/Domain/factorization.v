Require Import init.

Require Import mult_div.
Require Import gcd.
Require Import relation.
Require Import set.

Require Import unordered_list.

(* begin hide *)
Section UniqueFactorizationDef.

Context U `{
    UZ : Zero U,
    UM : Mult U,
    UO : One U,
    @MultAssoc U UM,
    @MultComm U UM
}.

(* end hide *)
#[universes(template)]
Class UniqueFactorizationDomain := {
    factorization_base : ∀ x : U, 0 ≠ x →
        ∃ a l, unit a ∧ ulist_prop (λ x, prime x) l ∧ x = a * ulist_prod l
}.

(* begin hide *)
End UniqueFactorizationDef.
Arguments factorization_base {U UZ UM UO H H0 UniqueFactorizationDomain}.
Section UniqueFactorization.

Context U `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    @Ldist U UP UM,
    @Rdist U UP UM,
    UMA : @MultAssoc U UM,
    UMC : @MultComm U UM,
    @MultLid U UM UO,
    @MultLcancel U UZ UM,
    @UniqueFactorizationDomain U UZ UM UO UMA UMC
}.

(* end hide *)
Theorem factorization_ex : ∀ x : U, 0 ≠ x → ∃ a l,
        unit a ∧
        ulist_prop (λ x, irreducible x) l ∧
        x = a * ulist_prod l ∧
        (∀ a' l',
            unit a' →
            ulist_prop (λ x, irreducible x) l' →
            x = a' * ulist_prod l' →
            ∃ l'', ulist_prop (λ x, unit (fst x)) l'' ∧
                   ulist_image l'' (λ x, snd x) = l ∧
                   ulist_image l'' (λ x, fst x * snd x) = l').
    intros x x_nz.
    pose proof (factorization_base x x_nz) as [a [l [au [l_prime x_eq]]]].
    clear x_nz.
    exists a, l.
    repeat split; try assumption.
    {
        clear x_eq.
        induction l as [|b l] using ulist_induction.
        -   apply ulist_prop_end.
        -   rewrite ulist_prop_add.
            apply ulist_prop_add in l_prime as [b_prime l_prime].
            split.
            +   apply prime_irreducible.
                exact b_prime.
            +   apply IHl.
                exact l_prime.
    }
    revert x a au l_prime x_eq.
    induction l as [|p l] using ulist_induction;
        intros x a au l_prime x_eq a' l' a'u l'_irr x_eq'.
    {
        destruct l' as [|b l'] using ulist_destruct.
        -   exists ulist_end.
            repeat split.
            +   apply ulist_prop_end.
            +   apply ulist_image_end.
            +   apply ulist_image_end.
        -   exfalso.
            rewrite ulist_prod_end in x_eq.
            rewrite mult_rid in x_eq.
            subst x.
            rewrite ulist_prop_add in l'_irr.
            destruct l'_irr as [b_irr l'_irr].
            destruct b_irr as [b_nz [b_nu b_irr]].
            destruct au as [da a_eq].
            apply b_nu.
            exists (da * a' * ulist_prod l').
            apply lmult with da in x_eq'.
            rewrite a_eq in x_eq'.
            rewrite x_eq'.
            do 2 rewrite <- mult_assoc.
            do 2 apply f_equal.
            rewrite ulist_prod_add.
            apply mult_comm.
    }
    apply ulist_prop_add in l_prime as [p_prime l_prime].
    assert (∃ u, unit u ∧ in_ulist l' (u * p)) as [u [uu p_in]].
    {
        assert (p ∣ a' * ulist_prod l') as p_div.
        {
            rewrite <- x_eq', x_eq.
            exists (a * ulist_prod l).
            rewrite <- mult_assoc.
            apply f_equal.
            rewrite ulist_prod_add.
            apply mult_comm.
        }
        destruct p_prime as [p_nz [p_nu p_prime]].
        apply p_prime in p_div as [p_div|p_div].
        {
            exfalso; apply p_nu.
            destruct p_div as [p' p_eq].
            destruct a'u as [a'' a'_eq].
            exists (a'' * p').
            rewrite <- mult_assoc.
            rewrite p_eq.
            exact a'_eq.
        }
        clear x_eq'.
        induction l' as [|b l'] using ulist_induction.
        -   rewrite ulist_prod_end in p_div.
            contradiction.
        -   apply ulist_prop_add in l'_irr as [[b_nz [b_nu b_irr]] l'_irr].
            rewrite ulist_prod_add in p_div.
            apply p_prime in p_div as [p_div|p_div].
            +   destruct p_div as [u b_eq].
                classic_case (unit u) as [uu|unu].
                *   exists u.
                    split; [>exact uu|].
                    rewrite in_ulist_add.
                    left.
                    symmetry; exact b_eq.
                *   specialize (b_irr _ _ unu p_nu).
                    symmetry in b_eq; contradiction.
            +   specialize (IHl' l'_irr p_div) as [u [uu up_in]].
                exists u.
                split; [>exact uu|].
                rewrite in_ulist_add.
                right; exact up_in.
    }
    apply in_ulist_split in p_in as [l'' l'_eq]; subst l'; rename l'' into l'.
    apply ulist_prop_add in l'_irr as [up_irr l'_irr].
    rewrite x_eq in x_eq'.
    do 2 rewrite ulist_prod_add in x_eq'.
    rewrite (mult_comm u p) in x_eq'.
    do 3 rewrite mult_assoc in x_eq'.
    do 2 rewrite (mult_comm _ p) in x_eq'.
    do 3 rewrite <- mult_assoc in x_eq'.
    apply mult_lcancel in x_eq'; [>|apply p_prime].
    rewrite mult_assoc in x_eq'.
    specialize (IHl (a * ulist_prod l) a au l_prime Logic.eq_refl).
    assert (unit (a' * u)) as a'u_u by (apply unit_mult; assumption).
    specialize (IHl (a' * u) l' a'u_u l'_irr x_eq')
        as [l'' [l''_unit [l''_l l''_l']]].
    exists ((u, p) ::: l'').
    repeat split.
    -   rewrite ulist_prop_add; split.
        +   exact uu.
        +   exact l''_unit.
    -   rewrite ulist_image_add; cbn.
        apply f_equal.
        exact l''_l.
    -   rewrite ulist_image_add; cbn.
        apply f_equal.
        exact l''_l'.
Qed.

Definition factorization_unit x x_nz := ex_val (factorization_ex x x_nz).
Definition factorization x x_nz := ex_val (ex_proof (factorization_ex x x_nz)).

Theorem factorization_unit_unit : ∀ x x_nz, unit (factorization_unit x x_nz).
    intros x x_nz.
    apply (ex_proof (ex_proof (factorization_ex x x_nz))).
Qed.

Theorem factorization_irreducible : ∀ x x_nz,
        ulist_prop (λ x, irreducible x) (factorization x x_nz).
    intros x x_nz.
    apply (ex_proof (ex_proof (factorization_ex x x_nz))).
Qed.

Theorem factorization_eq : ∀ x x_nz,
        x = factorization_unit x x_nz * ulist_prod (factorization x x_nz).
    intros x x_nz.
    apply (ex_proof (ex_proof (factorization_ex x x_nz))).
Qed.

Theorem factorization_uni : ∀ (x : U) (x_nz : 0 ≠ x),
        ∀ a l,
            unit a →
            ulist_prop (λ x, irreducible x) l →
            x = a * ulist_prod l →
            ∃ l', ulist_prop (λ x, unit (fst x)) l' ∧
                   ulist_image l' (λ x, snd x) = factorization x x_nz ∧
                   ulist_image l' (λ x, fst x * snd x) = l.
    intros x x_nz.
    apply (ex_proof (ex_proof (factorization_ex x x_nz))).
Qed.
(* begin hide *)

End UniqueFactorization.
(* end hide *)
