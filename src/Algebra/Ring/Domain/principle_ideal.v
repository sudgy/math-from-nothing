Require Import init.

Require Export ring_ideal.
Require Import factorization.

Require Import gcd.
Require Import mult_div.
Require Import nat.
Require Import set.
Require Import unordered_list.
Require Import order_minmax.

(* begin hide *)
Section PrincipleIdealDef.

Context {U} `{
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
    @MultAssoc U UM,
    @MultComm U UM,
    @MultLid U UM UO,
    @MultRid U UM UO
}.

(* end hide *)
Definition principle_ideal_by x := ideal_generated_by (singleton x).

Definition principle_ideal (I : Ideal U)
    := ∃ x, I = principle_ideal_by x.

Theorem principle_ideal_div : ∀ a b, ideal_set (principle_ideal_by a) b ↔ a ∣ b.
    intros a b.
    split.
    -   intros [l eq].
        subst b.
        induction l as [|b l] using ulist_induction.
        +   rewrite ulist_image_end, ulist_sum_end.
            apply divides_zero.
        +   rewrite ulist_image_add, ulist_sum_add.
            apply plus_stays_divides.
            *   destruct b as [[b1 b2] [b3 b3_eq]]; cbn.
                unfold singleton in b3_eq; subst b3.
                exists (b1 * b2).
                do 2 rewrite <- mult_assoc.
                apply f_equal.
                apply mult_comm.
            *   exact IHl.
    -   intros [c eq].
        exists (((c, 1), [a|Logic.eq_refl]) ::: ulist_end).
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_rid, plus_rid.
        symmetry; exact eq.
Qed.

Theorem principle_ideal_associates : ∀ a b,
        principle_ideal_by a = principle_ideal_by b ↔ associates a b.
    intros a b.
    split.
    -   intros eq.
        assert (ideal_set (principle_ideal_by a) b) as ab.
        {
            rewrite eq.
            rewrite principle_ideal_div.
            apply refl.
        }
        assert (ideal_set (principle_ideal_by b) a) as ba.
        {
            rewrite <- eq.
            rewrite principle_ideal_div.
            apply refl.
        }
        rewrite principle_ideal_div in ab, ba.
        split; assumption.
    -   intros [ab ba].
        apply ideal_eq.
        intros x.
        do 2 rewrite principle_ideal_div.
        split; intros x_div.
        +   exact (trans ba x_div).
        +   exact (trans ab x_div).
Qed.

Class PrincipleIdealDomain := {
    ideal_principle : ∀ I : Ideal U, principle_ideal I
}.

(* begin hide *)
End PrincipleIdealDef.
Section PrincipleIdeal.

Context {U} `{
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
    @MultRid U UM UO,
    @MultLcancel U UZ UM,
    @PrincipleIdealDomain U UP UZ UN UM UPA UPC UPZ UPN UL UR UMA
}.

(* end hide *)
Theorem pid_noetherian : ∀ I : nat → Ideal U,
        (∀ n, ideal_set (I n) ⊆ ideal_set (I (nat_suc n))) →
        ∃ n0, ∀ n, n0 <= n → I n0 = I n.
    intros In I_sub.
    assert (∀ m n, m <= n → ideal_set (In m) ⊆ ideal_set (In n)) as I_sub2.
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
    pose (I x := ∃ n, ideal_set (In n) x).
    assert (∃ a, I a) as I_nempty.
    {
        destruct (ideal_nempty (In 0)) as [a Ia].
        exists a.
        exists 0.
        exact Ia.
    }
    assert (∀ a b, I a → I b → I (a + b)) as I_plus.
    {
        intros a b [m Ia] [n Ib].
        exists (max m n).
        apply ideal_plus.
        -   apply (I_sub2 m); [>|exact Ia].
            apply lmax.
        -   apply (I_sub2 n); [>|exact Ib].
            apply rmax.
    }
    assert (∀ a b, I b → I (a * b)) as I_lmult.
    {
        intros a b [n Ib].
        exists n.
        apply ideal_lmult.
        exact Ib.
    }
    assert (∀ a b, I a → I (a * b)) as I_rmult.
    {
        intros a b [n Ia].
        exists n.
        apply ideal_rmult.
        exact Ia.
    }
    pose (I' := make_ideal I I_nempty I_plus I_lmult I_rmult).
    pose proof (ideal_principle I') as [a0 I'_eq].
    assert (ideal_set I' a0) as [n0 Ia0].
    {
        rewrite I'_eq.
        exists (((1, 1), [a0|Logic.eq_refl]) ::: ulist_end).
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid.
        rewrite mult_lid, mult_rid.
        reflexivity.
    }
    exists n0.
    intros n n_ge.
    apply ideal_eq_set.
    apply antisym.
    1: apply (I_sub2 _ _ n_ge).
    assert (ideal_set (In n) ⊆ I) as sub1.
    {
        intros a Ia.
        exists n.
        exact Ia.
    }
    apply (trans sub1).
    intros a Ia.
    assert (ideal_set I' a) as I'a by exact Ia.
    rewrite I'_eq in I'a.
    destruct I'a as [l a_eq].
    rewrite a_eq; clear a Ia a_eq.
    induction l as [|a l] using ulist_induction.
    -   rewrite ulist_image_end, ulist_sum_end.
        apply ideal_zero.
    -   rewrite ulist_image_add, ulist_sum_add; cbn.
        apply ideal_plus; [>clear IHl|exact IHl].
        destruct a as [[a1 a2] [a3 a3_eq]]; cbn.
        apply ideal_rmult.
        apply ideal_lmult.
        unfold singleton in a3_eq; subst.
        exact Ia0.
Qed.

Program Instance pid_gcd : GCDDomain U := {
    gcd a b := ex_val (ideal_principle
        (ideal_generated_by (singleton a ∪ singleton b)))
}.
Next Obligation.
    rewrite_ex_val d d_eq.
    split.
    -   rewrite <- principle_ideal_div.
        rewrite <- d_eq.
        cbn.
        exists (((1, 1), [a|make_lor Logic.eq_refl]) ::: ulist_end).
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid.
        rewrite mult_lid, mult_rid.
        reflexivity.
    -   rewrite <- principle_ideal_div.
        rewrite <- d_eq.
        cbn.
        exists (((1, 1), [b|make_ror Logic.eq_refl]) ::: ulist_end).
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid.
        rewrite mult_lid, mult_rid.
        reflexivity.
Qed.
Next Obligation.
    destruct H5 as [da db].
    rewrite_ex_val d' d'_eq.
    assert (ideal_set (principle_ideal_by d') d') as d'_in.
    {
        rewrite principle_ideal_div.
        apply refl.
    }
    rewrite <- d'_eq in d'_in.
    destruct d'_in as [l eq].
    subst d'.
    clear d'_eq.
    induction l as [|c l] using ulist_induction.
    -   rewrite ulist_image_end, ulist_sum_end.
        apply divides_zero.
    -   rewrite ulist_image_add, ulist_sum_add.
        apply plus_stays_divides; [>clear IHl|exact IHl].
        destruct c as [[c1 c2] [c3 c3_eq]]; cbn.
        apply mult_factors_extend.
        rewrite mult_comm.
        apply mult_factors_extend.
        unfold singleton, union in c3_eq; cbn in c3_eq.
        destruct c3_eq; subst c3; assumption.
Qed.

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
    rename H4 into a_nz.
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
(* begin hide *)

End PrincipleIdeal.
(* end hide *)
