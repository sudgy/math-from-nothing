Require Import init.

Require Export ring_ideal.
Require Export domain_category.

Require Import nat.
Require Import mult_div.
Require Import unordered_list.

Class Noetherian (U : IntegralDomain) := {
    noetherian : ∀ I : nat → CIdeal (domain_to_cring U),
        (∀ n, cideal_set (I n) ⊆ cideal_set (I (nat_suc n))) →
        ∃ n, ∀ m, n ≤ m → I n = I m
}.

Section Noetherian.

Context {U : IntegralDomain} `{Noetherian U}.
Local Existing Instances div_zero_class div_one_class div_mult_class
    div_mult_comm div_mult_assoc div_mult_lid div_mult_lanni div_mult_lcancel
    div_not_trivial to_div_zero to_div_one to_div_mult to_div_sur.

Theorem noetherian_div : ∀ f : nat → div_type U,
    (∀ n, f (nat_suc n) ∣ f n) →
    ∃ n, ∀ m, n ≤ m → f n = f m.
Proof.
    intros f f_div.
    pose proof (noetherian
        (λ n, principle_ideal_by (U := domain_to_cring U)
        (ex_val (sur to_div (f n))))) as n_ex.
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

Lemma ring_factor_ex : ∀ x : set_type interesting, ¬irreducible [x|] →
    ∃ a b : set_type interesting, [x|] = [a|] * [b|].
Proof.
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
Qed.

Lemma noetherian_irreducible_ex :
    ∀ x : div_type U, interesting x → ∃ p, irreducible p ∧ p ∣ x.
Proof.
    intros x x_int.
    pose (f := fix f n :=
        match n with
        | nat_zero => [x|x_int]
        | nat_suc n' =>
            IfH irreducible [f n'|]
            then λ _, f n'
            else λ H, ex_val (ring_factor_ex _ H)
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
            else λ _, f n'
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
            +   exact IHn.
    }
    pose proof (noetherian_div f2) as n_ex.
    prove_parts n_ex.
    {
        intros n.
        unfold f2; cbn.
        classic_case (interesting (snd (f n))) as [fn_int|fn_not]; cbn.
        -   rewrite <- (get_px' _ fn_int).
            apply mult_div_lself.
        -   apply refl.
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
        +   unfold interesting in fn_not.
            rewrite not_and in fn_not.
            do 2 rewrite not_not in fn_not.
            destruct fn_not as [fn_z|fn_o].
            2: exact fn_o.
            specialize (prod_eq n).
            rewrite <- fn_z in prod_eq.
            rewrite mult_ranni in prod_eq.
            contradiction.
    }
    exists (f1 n).
    split.
    -   apply f1_irr.
    -   rewrite <- (prod_eq n).
        rewrite f2_one.
        apply mult_rid.
Qed.

End Noetherian.
