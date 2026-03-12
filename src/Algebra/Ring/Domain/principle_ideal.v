Require Import init.

Require Export ring_ideal.
Require Export domain_category.
Require Import factorization.

Require Import gcd.
Require Import mult_div.
Require Import nat.
Require Import set.
Require Import unordered_list.
Require Import order_minmax.

Section PrincipleIdealDef.

Context {U : IntegralDomain}.

Definition principle_ideal_by (x : domain_to_cring U)
    := cideal_generated_by ❴x❵.

Definition principle_ideal (I : CIdeal (domain_to_cring U))
    := ∃ x, I = principle_ideal_by x.

Theorem principle_ideal_div :
    ∀ a b, principle_ideal_by a b ↔ a ∣ b.
Proof.
    intros a b.
    split.
    -   intros [l eq].
        subst b.
        induction l as [|b l] using ulist_induction.
        +   rewrite ulist_image_end, ulist_sum_end.
            apply divides_zero.
        +   rewrite ulist_image_add, ulist_sum_add.
            apply plus_stays_divides.
            *   destruct b as [b1 [b2 b2_eq]]; cbn.
                rewrite singleton_eq in b2_eq; subst b2.
                apply mult_div_lself.
            *   exact IHl.
    -   intros [c eq].
        exists ((c, [a|Logic.eq_refl]) ː ulist_end).
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid, mult_comm.
        symmetry; exact eq.
Qed.

Theorem principle_ideal_sub : ∀ a b,
    principle_ideal_by a ⊆ principle_ideal_by b ↔ b ∣ a.
Proof.
    intros a b.
    split.
    -   intros sub.
        apply principle_ideal_div.
        apply sub.
        apply principle_ideal_div.
        apply refl.
    -   intros div x.
        do 2 rewrite principle_ideal_div.
        intros div2.
        exact (trans div div2).
Qed.

Theorem principle_ideal_associates : ∀ a b,
    principle_ideal_by a = principle_ideal_by b ↔ associates a b.
Proof.
    intros a b.
    split.
    -   intros eq.
        split.
        all: rewrite <- principle_ideal_sub.
        all: rewrite eq.
        all: apply refl.
    -   intros [ab ba].
        apply cideal_eq_set.
        apply antisym.
        all: rewrite principle_ideal_sub.
        all: assumption.
Qed.

Class PrincipleIdealDomain := {
    ideal_principle : ∀ I : CIdeal (domain_to_cring U), principle_ideal I
}.

Class Noetherian := {
    noetherian : ∀ I : nat → CIdeal (domain_to_cring U),
        (∀ n, cideal_set (I n) ⊆ cideal_set (I (nat_suc n))) →
        ∃ n, ∀ m, n ≤ m → I n = I m
}.

End PrincipleIdealDef.

Arguments PrincipleIdealDomain U : clear implicits.
Arguments Noetherian U : clear implicits.

Section Noetherian.

Context {U : IntegralDomain} `{Noetherian U}.

Theorem noetherian_div : ∀ f : nat → div_type U,
    (∀ n, f (nat_suc n) ∣ f n) →
    ∃ n, ∀ m, n ≤ m → f n = f m.
Proof.
    intros f f_div.
    pose proof (noetherian
        (λ n, principle_ideal_by (ex_val (sur to_div (f n))))) as n_ex.
    prove_parts n_ex.
    {
        intros n.
        specialize (f_div n).
        rewrite_ex_val fn fn_eq.
        rewrite_ex_val fSn fSn_eq.
        rewrite <- fn_eq, <- fSn_eq in f_div.
        rewrite <- div_equiv_div in f_div.
        rewrite principle_ideal_sub.
        exact f_div.
    }
    destruct n_ex as [n n_eq].
    exists n.
    intros m leq.
    specialize (n_eq m leq).
    rewrite_ex_val fn fn_eq.
    rewrite_ex_val fm fm_eq.
    rewrite principle_ideal_associates in n_eq.
    rewrite <- fn_eq, <- fm_eq.
    unfold to_div; equiv_simpl.
    exact n_eq.
Qed.

Let interesting (x : div_type U) := 0 ≠ x ∧ x ≠ 1.

Lemma noetherian_irreducible_ex :
    ∀ x : div_type U, interesting x → ∃ p, irreducible p ∧ p ∣ x.
Proof.
    assert (∀ x : set_type interesting, ¬irreducible [x|] →
        ∃ a b : set_type interesting, [x|] = [a|] * [b|]) as factor_ex.
    {
        intros [x [x_nz x_no]] x_red; cbn in *.
        unfold irreducible in x_red.
        do 2 rewrite not_and_impl in x_red.
        rewrite div_equiv_unit in x_red.
        specialize (x_red x_nz x_no).
        rewrite not_all in x_red.
        destruct x_red as [a x_red].
        rewrite not_all in x_red.
        destruct x_red as [b x_red].
        do 2 rewrite not_impl in x_red.
        do 2 rewrite div_equiv_unit in x_red.
        rewrite not_not in x_red.
        destruct x_red as [a_no [b_no x_eq]].
        assert (interesting a) as a_int.
        {
            split; [>|exact a_no].
            intros contr; subst a.
            rewrite mult_lanni in x_eq.
            symmetry in x_eq; contradiction.
        }
        assert (interesting b) as b_int.
        {
            split; [>|exact b_no].
            intros contr; subst b.
            rewrite mult_ranni in x_eq.
            symmetry in x_eq; contradiction.
        }
        exists [a|a_int], [b|b_int].
        exact x_eq.
    }
    intros x x_int.
    pose (f := fix f n :=
        match n with
        | nat_zero => [x|x_int]
        | nat_suc n' =>
            IfH irreducible [f n'|]
            then λ _, f n'
            else λ H, ex_val (factor_ex _ H)
        end).
    pose proof (noetherian_div (λ n, [f n|])) as n_ex.
    prove_parts n_ex.
    {
        intros n.
        cbn.
        classic_case (irreducible [f n|]) as [fn_irr|fn_red].
        -   apply refl.
        -   rewrite_ex_val a [b eq].
            rewrite eq.
            apply mult_div_lself.
    }
    destruct n_ex as [n n_eq].
    exists [f n|].
    split.
    -   specialize (n_eq (nat_suc n) (nat_le_suc n)).
        cbn in n_eq.
        classic_case (irreducible [f n|]) as [fn_irr|fn_red].
        1: exact fn_irr.
        rewrite_ex_val a [b eq].
        rewrite n_eq in eq.
        rewrite <- (mult_rid [a|]) in eq at 1.
        apply mult_lcancel in eq; [>|apply [|a]].
        destruct b as [b [b_nz b_no]].
        symmetry in eq; contradiction.
    -   clear n_eq.
        nat_induction n.
        +   unfold zero; cbn.
            apply refl.
        +   cbn.
            classic_case (irreducible [f n|]) as [fn_irr|fn_red].
            *   exact IHn.
            *   rewrite_ex_val a [b eq].
                apply (trans2 IHn).
                rewrite eq.
                apply mult_div_lself.
Qed.

Theorem noetherian_factors : ∀ x : div_type U, 0 ≠ x →
    ∃ l, ulist_prop irreducible l ∧ x = ulist_prod l.
Proof.
    pose (get_p x H := ex_val (noetherian_irreducible_ex x H)).
    pose (get_x' x H
        := ex_val (rand (ex_proof (noetherian_irreducible_ex x H)))).
    assert (get_p_irr : ∀ x H, irreducible (get_p x H)).
    {
        intros x H'.
        unfold get_p.
        apply (ex_proof (noetherian_irreducible_ex x H')).
    }
    assert (get_px' : ∀ x H, get_x' x H * get_p x H = x).
    {
        intros x H'.
        unfold get_p, get_x'.
        exact (ex_proof (rand (ex_proof (noetherian_irreducible_ex x H')))).
    }
    intros x x_nz.
    pose (f := fix f n :=
        match n with
        | nat_zero => (⟦⟧, x)
        | nat_suc n' =>
            IfH interesting (snd (f n'))
            then λ H, (get_p _ H ː fst (f n'), get_x' _ H)
            else λ _, (fst (f n'), 1)
        end).
    pose (f1 n := fst (f n)).
    pose (f2 n := snd (f n)).
    assert (∀ n, ulist_prop irreducible (f1 n)) as f1_irr.
    {
        nat_induction n.
        +   unfold f1; cbn.
            unfold zero; cbn.
            apply ulist_prop_end.
        +   unfold f1; cbn.
            classic_case (interesting (snd (f n))) as [fn_int|fn_not]; cbn.
            *   rewrite ulist_prop_add.
                split; [>|exact IHn].
                apply get_p_irr.
            *   exact IHn.
    }
    assert (∀ n, ulist_prod (f1 n) * f2 n = x) as prod_eq.
    {
        nat_induction n.
        -   unfold zero; cbn.
            rewrite ulist_prod_end.
            apply mult_lid.
        -   unfold f1, f2 in *; cbn.
            classic_case (interesting (snd (f n))) as [fn_int|fn_not]; cbn.
            +   rewrite ulist_prod_add.
                rewrite mult_comm, mult_assoc.
                rewrite get_px'.
                rewrite mult_comm.
                exact IHn.
            +   unfold interesting in fn_not.
                rewrite not_and in fn_not.
                do 2 rewrite not_not in fn_not.
                destruct fn_not as [fn_z|fn_o].
                *   rewrite <- fn_z in IHn.
                    rewrite mult_ranni in IHn.
                    contradiction.
                *   rewrite fn_o in IHn.
                    exact IHn.
    }
    pose proof (noetherian_div f2) as n_ex.
    prove_parts n_ex.
    {
        intros n.
        unfold f2; cbn.
        classic_case (interesting (snd (f n))) as [fn_int|fn_not]; cbn.
        -   rewrite <- (get_px' _ fn_int).
            apply mult_div_lself.
        -   apply one_divides.
    }
    destruct n_ex as [n n_eq].
    assert (f2 n = 1) as f2_one.
    {
        specialize (n_eq (nat_suc n) (nat_le_suc n)).
        unfold f2 in *; cbn in n_eq.
        classic_case (interesting (snd (f n))) as [fn_int|fn_not].
        +   cbn in n_eq.
            pose proof fn_int as x'_int.
            rewrite n_eq in x'_int.
            rewrite <- (get_px' _ fn_int) in n_eq at 1.
            rewrite <- (mult_rid (get_x' _ _)) in n_eq at 2.
            apply mult_lcancel in n_eq; [>|apply x'_int].
            pose proof (get_p_irr _ fn_int) as [p_nz [p_nu]].
            rewrite div_equiv_unit in p_nu.
            contradiction.
        +   exact n_eq.
    }
    exists (f1 n).
    split.
    -   apply f1_irr.
    -   rewrite <- (prod_eq n).
        rewrite f2_one.
        apply mult_rid.
Qed.

End Noetherian.

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
        destruct (cideal_nempty (In 0)) as [a Ia].
        exists a.
        exists 0.
        exact Ia.
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
        exists ((1, [a0|Logic.eq_refl]) ː ulist_end).
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid.
        rewrite mult_rid.
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

Program Instance pid_gcd : GCDDomain (domain_to_cring U) := {
    gcd (a b : domain_to_cring U) := ex_val (ideal_principle
        (cideal_generated_by (❴a, b❵)))
}.
Next Obligation.
    rewrite_ex_val d d_eq.
    split.
    -   rewrite <- (principle_ideal_div d).
        rewrite <- d_eq.
        cbn.
        exists ((1, [a|make_lor Logic.eq_refl]) ː ulist_end).
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid.
        rewrite mult_rid.
        reflexivity.
    -   rewrite <- (principle_ideal_div d).
        rewrite <- d_eq.
        cbn.
        exists ((1, [b|make_ror Logic.eq_refl]) ː ulist_end).
        rewrite ulist_image_add, ulist_sum_add; cbn.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid.
        rewrite mult_rid.
        reflexivity.
Qed.
Next Obligation.
    destruct H1 as [da db].
    rewrite_ex_val d' d'_eq.
    assert (cideal_set (principle_ideal_by d') d') as d'_in.
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
        destruct c as [c1 [c2 c2_eq]]; cbn.
        apply mult_factors_extend.
        unfold list_to_set, union in c2_eq; cbn in c2_eq.
        destruct c2_eq; subst c2; assumption.
Qed.

Instance pid_factorization : UniqueFactorizationDomain U.
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
