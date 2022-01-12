Require Import init.

Require Import mult_div.
Require Import principle_ideal.
Require Import gcd.
Require Import relation.
Require Import set.

Require Import unordered_list.

Section UniqueFactorizationDef.

Context U `{
    UZ : Zero U,
    UM : Mult U,
    UO : One U,
    @MultAssoc U UM,
    @MultComm U UM
}.

#[universes(template)]
Class UniqueFactorizationDomain := {
    factorization_base : ∀ x : U, 0 ≠ x →
        ∃ a l, unit a ∧ ulist_prop (λ x, prime x) l ∧ x = a * ulist_prod l
}.

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

Theorem factorization : ∀ x : U, 0 ≠ x → ∃ a l,
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

End UniqueFactorization.

Section PIDFactorization.

Context U `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    UPA : @PlusAssoc U UP,
    UPC : @PlusComm U UP,
    UPZ : @PlusLid U UP UZ,
    UPN : @PlusLinv U UP UZ UN,
    UL : @Ldist U UP UM,
    UR : @Rdist U UP UM,
    UMA : @MultAssoc U UM,
    @MultComm U UM,
    @MultLid U UM UO,
    @MultLcancel U UZ UM,
    @PrincipleIdealDomain U UP UZ UN UM UPA UPC UPZ UPN UL UR UMA
}.

Existing Instance pid_gcd.

Lemma pid_factor_ex : ∀ a, 0 ≠ a → ¬unit a → ∃ b, prime b ∧ b ∣ a.
    intros a a_nz au.
    classic_contradiction contr.
    rewrite not_ex in contr.
    setoid_rewrite not_and in contr.
    assert (∀ p, p ∣ a → ¬prime p) as a_factors.
    {
        intros p p_div p_irr.
        specialize (contr p) as [contr|contr]; contradiction.
    }
    clear contr.
    assert (∀ a', ¬unit a' → a' ∣ a →
            ∃ a1 a2, ¬unit a1 ∧ ¬unit a2 ∧ a' = a1 * a2) as a'_part.
    {
        intros a' a'_nu a'_div.
        specialize (a_factors _ a'_div).
        assert (¬irreducible a') as a_factors'.
        {
            intros a_irr.
            apply irreducible_prime in a_irr.
            contradiction.
        }
        clear a_factors; rename a_factors' into a_factors.
        unfold irreducible in a_factors.
        do 2 rewrite not_and in a_factors.
        destruct a_factors as [a'_z|[C0|a_factors]]; [>|contradiction|].
        -   rewrite not_not in a'_z.
            rewrite <- a'_z in a'_div.
            destruct a'_div as [c eq].
            rewrite mult_ranni in eq.
            contradiction.
        -   rewrite not_all in a_factors.
            destruct a_factors as [a1 a_factors].
            rewrite not_all in a_factors.
            destruct a_factors as [a2 a_factors].
            do 2 rewrite not_impl in a_factors.
            rewrite not_not in a_factors.
            exists a1, a2.
            exact a_factors.
    }
    pose (S (x : U * U) := ¬unit (fst x) ∧ ¬unit (snd x)).
    pose (S2 (x : U * U) := ¬unit (fst x) ∧ ¬unit (snd x) ∧ fst x ∣ a).
    pose (make_S a' a'_nu a'_div
        := let a_ex := a'_part a' a'_nu a'_div in
            [(ex_val a_ex, ex_val (ex_proof a_ex)) |
             make_and (land (ex_proof (ex_proof a_ex)))
                      (land (rand (ex_proof (ex_proof a_ex))))] : set_type S).
    assert (∀ a' a'_nu a'_div, S2 [make_S a' a'_nu a'_div|]) as SS2.
    {
        intros a' a'_nu a'_div.
        unfold make_S; cbn.
        unfold ex_val, ex_proof.
        destruct (ex_to_type _) as [a1 C0]; cbn.
        destruct (ex_to_type _) as [a2 [a1_nu [a2_nu a_eq]]]; cbn; clear C0.
        repeat split.
        -   exact a1_nu.
        -   exact a2_nu.
        -   cbn.
            apply (trans2 a'_div).
            exists a2.
            rewrite mult_comm.
            symmetry; exact a_eq.
    }
    pose (make_S2 a' a'_nu a'_div := [_|SS2 a' a'_nu a'_div]).
    pose (build_a' := fix build_a (n : nat) :=
        match n with
        | nat_zero => make_S2 a au (refl a)
        | nat_suc n' => make_S2
            (fst [build_a n'|])
            (land [|build_a n'])
            (rand (rand [|build_a n']))
        end).
    pose (I n := principle_ideal_by (fst [build_a' n|])).
    assert (∀ n, ideal_set (I n) ⊆ ideal_set (I (nat_suc n))) as I_sub.
    {
Local Arguments principle_ideal_by : simpl never.
        intros n x Inx.
        unfold I in Inx; cbn in Inx.
        unfold I; cbn.
        rewrite_ex_val x1 [x2 [x1_nu [x2_nu eq]]].
        rewrite eq in Inx.
        rewrite principle_ideal_div.
        rewrite principle_ideal_div in Inx.
        destruct Inx as [x3 eq'].
        exists (x3 * x2).
        rewrite <- eq'.
        rewrite <- mult_assoc.
        apply f_equal.
        apply mult_comm.
    }
    pose proof (pid_noetherian I I_sub) as [n n_eq].
    specialize (n_eq (nat_suc n) (nat_le_suc n)).
    unfold I in n_eq.
    rewrite principle_ideal_associates in n_eq.
    cbn in n_eq.
    rewrite_ex_val a1 [a2 [a1_nu [a2_nu eq]]].
    destruct [|build_a' n] as [C0 [C1 a_div]]; clear C0 C1.
    rewrite eq in n_eq, a_div; clear eq.
    destruct n_eq as [div1 div2].
    destruct div1 as [c eq].
    apply a2_nu.
    exists c.
    rewrite (mult_comm a1 a2) in eq.
    rewrite mult_assoc in eq.
    rewrite <- (mult_lid a1) in eq at 2.
    apply mult_rcancel in eq.
    -   exact eq.
    -   intros contr.
        rewrite <- contr in a_div.
        rewrite mult_lanni in a_div.
        destruct a_div as [b a_eq].
        rewrite mult_ranni in a_eq.
        contradiction.
Qed.

Program Instance pid_factorization : UniqueFactorizationDomain U.
Next Obligation.
    rename x into a.
    rename H3 into a_nz.
    classic_case (unit a) as [au|au].
    {
        exists a, ulist_end.
        repeat split.
        -   exact au.
        -   apply ulist_prop_end.
        -   rewrite ulist_prod_end.
            rewrite mult_rid.
            reflexivity.
    }
    classic_contradiction contr.
    assert (∀ b l, ulist_prop (λ x, prime x) l → a = b * ulist_prod l →
            ∃ b' p, ulist_prop (λ x, prime x) (p ::: l) ∧
                a = b' * ulist_prod (p ::: l)) as b_ex.
    {
        intros b l l_prime a_eq.
        assert (0 ≠ b) as b_nz.
        {
            intro; subst b.
            rewrite mult_lanni in a_eq.
            symmetry in a_eq; contradiction.
        }
        assert (¬unit b) as bu.
        {
            intros bu.
            rewrite not_ex in contr.
            specialize (contr b).
            rewrite not_ex in contr.
            specialize (contr l).
            do 2 rewrite not_and in contr.
            destruct contr as [contr|[contr|contr]]; contradiction.
        }
        pose proof (pid_factor_ex b b_nz bu) as [p [p_prime pb]].
        destruct pb as [b' b_eq]; subst b.
        exists b', p.
        split.
        -   rewrite ulist_prop_add.
            split; assumption.
        -   rewrite ulist_prod_add.
            rewrite mult_assoc.
            exact a_eq.
    }
    pose (S (x : U * ulist U) := ulist_prop (λ x, prime x) (snd x) ∧
        a = fst x * ulist_prod (snd x)).
    assert (a = a * ulist_prod ulist_end) as a_eq.
    {
        rewrite ulist_prod_end.
        rewrite mult_rid.
        reflexivity.
    }
    pose (build_p := fix build_p' (n : nat) : set_type S :=
        match n with
        | nat_zero => [(a, ulist_end) |
                       make_and (ulist_prop_end (λ x, prime x)) a_eq]
        | nat_suc n' =>
            let bp := build_p' n' in
            let p_ex := b_ex (fst [bp|]) (snd [bp|]) (land [|bp]) (rand [|bp])in
            [(ex_val p_ex, ex_val (ex_proof p_ex) ::: snd [bp|]) |
             ex_proof (ex_proof p_ex)]
        end).
    pose (I n := principle_ideal_by (fst [build_p n|])).
    assert (∀ l, ulist_prop (λ x, prime x) l → 0 ≠ ulist_prod l) as l_nz.
    {
        clear au contr b_ex S a_eq build_p I.
        intros l l_prime.
        induction l as [|p l] using ulist_induction.
        -   rewrite ulist_prod_end.
            intros triv.
            rewrite <- (mult_lid a) in a_nz.
            rewrite <- triv in a_nz.
            rewrite mult_lanni in a_nz.
            contradiction.
        -   apply ulist_prop_add in l_prime as [p_prime l_prime].
            specialize (IHl l_prime).
            intros contr.
            destruct p_prime as [p_nz p_prime].
            rewrite ulist_prod_add in contr.
            rewrite <- (mult_ranni p) in contr.
            apply mult_lcancel in contr.
            +   contradiction.
            +   exact p_nz.
    }
    assert (∀ n, ideal_set (I n) ⊆ ideal_set (I (nat_suc n))) as I_sub.
    {
        intros n.
        unfold I; cbn.
        rewrite_ex_val a' p_ex.
        destruct p_ex as [p [ps_prime a'_eq]].
        intros x.
        do 2 rewrite principle_ideal_div.
        destruct [|build_p n] as [C0 a_eq']; clear C0.
        remember (fst [build_p n|]) as b; clear Heqb.
        remember (snd [build_p n|]) as l; clear Heql.
        intros [c x_eq].
        rewrite <- x_eq; clear x x_eq.
        rewrite mult_comm.
        apply mult_factors_extend.
        rewrite a_eq' in a'_eq.
        rewrite ulist_prod_add in a'_eq.
        rewrite mult_assoc in a'_eq.
        apply mult_rcancel in a'_eq.
        -   exists p.
            rewrite mult_comm.
            symmetry; exact a'_eq.
        -   apply ulist_prop_add in ps_prime as [p_prime l_prime].
            apply l_nz.
            exact l_prime.
    }
    pose proof (pid_noetherian I I_sub) as [n n_eq].
    specialize (n_eq (nat_suc n) (nat_le_suc n)).
    unfold I in n_eq.
    cbn in n_eq.
    rewrite_ex_val a' p_ex.
    destruct p_ex as [p [ps_prime a'_eq]].
    destruct [|build_p n] as [C0 a_eq']; clear C0.
    remember (fst [build_p n|]) as b; clear Heqb.
    remember (snd [build_p n|]) as l; clear Heql.
    assert (ideal_set (principle_ideal_by a') a') as a'_in.
    {
        rewrite principle_ideal_div.
        apply refl.
    }
    rewrite <- n_eq in a'_in.
    rewrite principle_ideal_div in a'_in.
    destruct a'_in as [c c_eq].
    rewrite <- c_eq in a'_eq.
    rewrite a_eq' in a'_eq.
    clear c_eq.
    rewrite (mult_comm c b) in a'_eq.
    rewrite <- mult_assoc in a'_eq.
    apply mult_lcancel in a'_eq.
    2: {
        intro; subst b.
        rewrite mult_lanni in a_eq'.
        symmetry in a_eq'; contradiction.
    }
    apply ulist_prop_add in ps_prime as [p_prime l_prime].
    rewrite ulist_prod_add in a'_eq.
    rewrite mult_assoc in a'_eq.
    rewrite <- (mult_lid (ulist_prod l)) in a'_eq at 1.
    apply mult_rcancel in a'_eq.
    2: {
        apply l_nz.
        exact l_prime.
    }
    destruct p_prime as [p_nz [pu p_prime]].
    apply pu.
    exists c.
    symmetry; exact a'_eq.
Qed.

End PIDFactorization.
