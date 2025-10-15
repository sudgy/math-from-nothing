Require Import init.

Require Export mult_div.
Require Import gcd.
Require Import relation.
Require Import set.
Require Import order_minmax.

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

Definition div_factorization x x_nz := ex_val (div_factorization_unique x x_nz).

Theorem div_factorization_prime :
    ∀ x x_nz, ulist_prop prime (div_factorization x x_nz).
Proof.
    intros x x_nz.
    apply (ex_proof (div_factorization_unique x x_nz)).
Qed.

Theorem div_factorization_irreducible :
    ∀ x x_nz, ulist_prop irreducible (div_factorization x x_nz).
Proof.
    intros x x_nz.
    apply (ulist_prop_sub _ prime irreducible).
    -   intros p.
        apply prime_irreducible.
    -   apply div_factorization_prime.
Qed.

Theorem div_factorization_eq :
    ∀ x x_nz, x = ulist_prod (div_factorization x x_nz).
Proof.
    intros x x_nz.
    apply (ex_proof (div_factorization_unique x x_nz)).
Qed.

Theorem div_factorization_uni :
    ∀ x x_nz l', ulist_prop prime l' → x = ulist_prod l' →
    div_factorization x x_nz = l'.
Proof.
    intros x x_nz.
    apply (ex_proof (div_factorization_unique x x_nz)).
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

Theorem factorization_mult : ∀ x y x_nz y_nz,
    div_factorization (x*y) (mult_nz x y x_nz y_nz) =
    div_factorization x x_nz + div_factorization y y_nz.
Proof.
    intros x y x_nz y_nz.
    apply div_factorization_uni.
    -   apply ulist_prop_conc.
        split; apply div_factorization_prime.
    -   rewrite ulist_prod_conc.
        do 2 rewrite <- div_factorization_eq.
        reflexivity.
Qed.

Theorem factorization_in : ∀ (x p : div_type U) (x_nz : 0 ≠ x), prime p → p ∣ x
    → in_ulist (div_factorization x x_nz) p.
Proof.
    intros x p x_nz p_prime p_div.
    destruct p_div as [a eq].
    assert (0 ≠ a) as a_nz.
    {
        intro contr; subst a.
        rewrite mult_lanni in eq.
        contradiction.
    }
    assert (div_factorization x x_nz = p ː div_factorization a a_nz) as l_eq.
    {
        apply div_factorization_uni.
        -   apply ulist_prop_add; split.
            +   exact p_prime.
            +   apply div_factorization_prime.
        -   rewrite ulist_prod_add.
            rewrite <- div_factorization_eq.
            rewrite mult_comm.
            symmetry; exact eq.
    }
    rewrite l_eq.
    apply in_ulist_add.
Qed.

Open Scope nat_scope.

Definition factorization_powers (x : div_type U) (x_nz : 0 ≠ x) p
    := ulist_count (div_factorization x x_nz) p.

Theorem factorization_powers_div : ∀ x y x_nz y_nz,
    x ∣ y ↔
    (∀ p, factorization_powers x x_nz p ≤ factorization_powers y y_nz p).
Proof.
    intros x y x_nz y_nz.
    unfold factorization_powers.
    split.
    -   intros x_div p.
        destruct x_div as [c eq]; subst y.
        assert (0 ≠ c) as c_nz.
        {
            intro; subst c.
            rewrite mult_lanni in y_nz.
            contradiction.
        }
        rewrite (proof_irrelevance y_nz (mult_nz _ _ c_nz x_nz)).
        rewrite factorization_mult.
        rewrite ulist_count_conc.
        apply le_plus_0_a_b_ab.
        apply all_pos.
    -   intros x_div.
        remember (ulist_size (div_factorization x x_nz)) as n.
        revert x y x_nz y_nz x_div Heqn.
        nat_induction n; intros.
        +   remember (div_factorization x x_nz) as xl.
            rewrite (div_factorization_eq x x_nz).
            rewrite <- Heqxl.
            clear - Heqn.
            destruct xl as [|p xl] using ulist_destruct.
            *   rewrite ulist_prod_end.
                apply one_divides.
            *   rewrite ulist_size_add in Heqn.
                contradiction (nat_zero_suc Heqn).
        +   remember (div_factorization x x_nz) as xl.
            destruct xl as [|p xl] using ulist_destruct.
            {
                rewrite ulist_size_end in Heqn.
                symmetry in Heqn.
                apply nat_zero_suc in Heqn.
                contradiction Heqn.
            }
            pose proof (div_factorization_prime x x_nz) as all_prime.
            rewrite <- Heqxl in all_prime.
            apply ulist_prop_add in all_prime.
            destruct all_prime as [p_prime xl_prime].
            assert (p ∣ y) as [y' y'_eq].
            {
                specialize (x_div p).
                rewrite ulist_count_add_eq in x_div.
                rewrite nat_le_suc_lt in x_div.
                classic_case (in_ulist (div_factorization y y_nz) p)
                        as [p_in|p_nin].
                -   apply in_ulist_split in p_in as [yl yl_eq].
                    rewrite (div_factorization_eq y y_nz).
                    rewrite yl_eq.
                    rewrite ulist_prod_add.
                    apply mult_div_lself.
                -   rewrite ulist_count_nin in p_nin.
                    rewrite <- p_nin in x_div.
                    contradiction (not_neg x_div).
            }
            pose (x' := ulist_prod xl).
            assert (0 ≠ x') as x'_nz.
            {
                unfold x'.
                clear - xl_prime.
                ulist_prop_induction xl xl_prime as p p_prime IHxl.
                -   rewrite ulist_prod_end.
                    apply not_trivial_one.
                -   rewrite ulist_prod_add.
                    apply mult_nz; [>|exact IHxl].
                    apply p_prime.
            }
            assert (0 ≠ y') as y'_nz.
            {
                intro; subst y'.
                rewrite mult_lanni in y'_eq.
                contradiction.
            }
            assert (div_factorization x' x'_nz = xl) as xl_eq.
            {
                apply div_factorization_uni.
                -   pose proof (div_factorization_prime x x_nz) as x_prime.
                    rewrite <- Heqxl in x_prime.
                    rewrite ulist_prop_add in x_prime.
                    apply x_prime.
                -   reflexivity.
            }
            assert (div_factorization y y_nz = p ː div_factorization y' y'_nz)
                as yl_eq.
            {
                apply div_factorization_uni.
                -   rewrite ulist_prop_add.
                    split; [>exact p_prime|].
                    apply div_factorization_prime.
                -   rewrite ulist_prod_add.
                    rewrite <- div_factorization_eq.
                    rewrite mult_comm.
                    symmetry; exact y'_eq.
            }
            specialize (IHn x' y' x'_nz y'_nz).
            prove_parts IHn.
            {
                intros q.
                rewrite yl_eq in x_div.
                specialize (x_div q).
                rewrite <- xl_eq in x_div.
                do 2 rewrite ulist_count_add in x_div.
                apply le_plus_lcancel in x_div.
                exact x_div.
            }
            {
                rewrite xl_eq.
                rewrite ulist_size_add in Heqn.
                rewrite nat_suc_eq in Heqn.
                exact Heqn.
            }
            rewrite <- y'_eq.
            rewrite (div_factorization_eq x x_nz).
            rewrite <- Heqxl.
            rewrite ulist_prod_add.
            fold x'.
            rewrite mult_comm.
            apply div_rmult.
            exact IHn.
Qed.

Lemma ufd_gcd_ex_div : ∀ x y : div_type U, 0 ≠ x → ∃ d, is_gcd x y d.
Proof.
    intros x y x_nz.
    classic_case (0 = y) as [y_z|y_nz].
    {
        subst y.
        exists x.
        split.
        -   split.
            +   apply refl.
            +   apply divides_zero.
        -   intros d' [d'_div1 d'_div2].
            exact d'_div1.
    }
    remember (div_factorization x x_nz) as xl.
    remember (div_factorization y y_nz) as yl.
    pose (dl := ulist_flatten
        (ulist_image (λ p, ulist_constant p (min
                                (factorization_powers x x_nz p)
                                (factorization_powers y y_nz p)))
                     (ulist_make_unique xl))).
    assert (ulist_prop prime dl) as dl_prime.
    {
        unfold dl.
        pose proof (div_factorization_prime x x_nz) as xl_prime.
        rewrite <- Heqxl in xl_prime.
        clear - xl_prime.
        ulist_prop_induction xl xl_prime as p p_prime IHxl.
        -   rewrite ulist_make_unique_end.
            rewrite ulist_image_end.
            rewrite ulist_flatten_end.
            apply ulist_prop_end.
        -   classic_case (in_ulist xl p) as [p_in|p_nin].
            +   rewrite (ulist_make_unique_add_in p_in).
                exact IHxl.
            +   rewrite (ulist_make_unique_add_nin p_nin).
                rewrite ulist_image_add.
                rewrite ulist_flatten_add.
                rewrite ulist_prop_conc.
                split; [>|exact IHxl].
                remember (min _ _) as n.
                clear - p_prime.
                nat_induction n.
                *   rewrite ulist_constant_zero.
                    apply ulist_prop_end.
                *   rewrite ulist_constant_suc.
                    rewrite ulist_prop_add.
                    split; [>|exact IHn].
                    exact p_prime.
    }
    pose (d := ulist_prod dl).
    assert (0 ≠ d) as d_nz.
    {
        unfold d.
        clearbody dl.
        clear - dl_prime.
        ulist_prop_induction dl dl_prime as p p_prime IHdl.
        -   rewrite ulist_prod_end.
            apply not_trivial_one.
        -   rewrite ulist_prod_add.
            apply mult_nz; [>|exact IHdl].
            apply p_prime.
    }
    assert (dl = div_factorization d d_nz) as d_eq.
    {
        symmetry; apply div_factorization_uni.
        -   exact dl_prime.
        -   reflexivity.
    }
    assert (∀ p, factorization_powers d d_nz p =
        min (factorization_powers x x_nz p) (factorization_powers y y_nz p))
        as p_eq.
    {
        intros p.
        unfold factorization_powers at 1.
        rewrite <- d_eq.
        unfold dl.
        classic_case (in_ulist (ulist_make_unique xl) p) as [p_in|p_nin].
        -   apply in_ulist_split in p_in as [xl' xl'_eq].
            rewrite xl'_eq.
            rewrite ulist_image_add.
            rewrite ulist_flatten_add.
            rewrite ulist_count_conc.
            rewrite ulist_count_constant.
            rewrite <- (plus_rid (min _ _)) at 2.
            apply lplus.
            symmetry; apply ulist_count_nin.
            intros contr.
            apply in_ulist_flatten in contr as [pl [pl_in p_in]].
            apply image_in_ulist in pl_in as [q [q_eq q_in]].
            rewrite <- q_eq in p_in.
            apply in_ulist_constant in p_in.
            subst q.
            clear - xl'_eq q_in.
            pose proof (ulist_make_unique_unique xl) as xl_uni.
            rewrite xl'_eq in xl_uni.
            rewrite ulist_unique_add in xl_uni.
            destruct xl_uni; contradiction.
        -   unfold factorization_powers at 3.
            pose proof p_nin as p_zero.
            rewrite <- ulist_make_unique_in in p_zero.
            apply ulist_count_nin in p_zero.
            rewrite Heqxl in p_zero.
            rewrite <- p_zero.
            rewrite min_leq by apply all_pos.
            symmetry; apply ulist_count_nin.
            intros contr.
            apply in_ulist_flatten in contr as [pl [pl_in p_in]].
            apply image_in_ulist in pl_in as [q [q_eq q_in]].
            rewrite <- q_eq in p_in.
            apply in_ulist_constant in p_in.
            subst q.
            contradiction.
    }
    exists d.
    split.
    -   split.
        +   apply (factorization_powers_div d x d_nz x_nz).
            intros p.
            rewrite p_eq.
            apply lmin.
        +   apply (factorization_powers_div d y d_nz y_nz).
            intros p.
            rewrite p_eq.
            apply rmin.
    -   intros d' [d'_div1 d'_div2].
        assert (0 ≠ d') as d'_nz.
        {
            intro; subst d'.
            apply div_zero in d'_div1.
            contradiction.
        }
        rewrite (factorization_powers_div d' x d'_nz x_nz) in d'_div1.
        rewrite (factorization_powers_div d' y d'_nz y_nz) in d'_div2.
        apply (factorization_powers_div d' d d'_nz d_nz).
        intros p.
        specialize (d'_div1 p).
        specialize (d'_div2 p).
        rewrite p_eq.
        unfold min.
        case_if; assumption.
Qed.

Lemma ufd_gcd_ex : ∀ x y : U, 0 ≠ x → ∃ d, is_gcd x y d.
Proof.
    intros x y x_nz.
    assert (0 ≠ to_div x) as x_nz'.
    {
        intros contr.
        unfold zero in contr; cbn in contr.
        unfold to_div in contr; equiv_simpl in contr.
        apply associates_zero in contr.
        contradiction.
    }
    pose proof (ufd_gcd_ex_div (to_div x) (to_div y) x_nz') as [d d_gcd].
    equiv_get_value d.
    exists d.
    unfold is_gcd in d_gcd.
    unfold common_divisor in d_gcd.
    change (to_equiv div_equiv) with (to_div (U := U)) in d_gcd.
    do 2 rewrite <- div_equiv_div in d_gcd.
    destruct d_gcd as [d_gcd1 d_gcd2].
    split.
    -   exact d_gcd1.
    -   intros d'.
        specialize (d_gcd2 (to_div d')).
        do 3 rewrite <- div_equiv_div in d_gcd2.
        exact d_gcd2.
Qed.

Definition ufd_gcd (a b : U) :=
    IfH 0 ≠ a then
    λ H, ex_val (ufd_gcd_ex a b H)
    else λ _, IfH 0 ≠ b then
    λ H, ex_val (ufd_gcd_ex b a H)
    else λ _, 1.

Theorem ufd_gcd_gcd : ∀ a b, (0 ≠ a ∨ 0 ≠ b) → is_gcd a b (ufd_gcd a b).
Proof.
    intros a b ab.
    unfold ufd_gcd.
    classic_case (0 ≠ a) as [a_nz|a_z].
    -   rewrite_ex_val d d_gcd.
        exact d_gcd.
    -   rewrite not_not in a_z.
        destruct ab as [|b_nz]; [>contradiction|].
        classic_case (0 ≠ b) as [b_nz'|b_z]; [>|contradiction].
        rewrite_ex_val d d_gcd.
        apply is_gcd_comm.
        exact d_gcd.
Qed.

#[refine]
Global Instance ufd_gcd_class : GCDDomain U := {
    gcd := ufd_gcd
}.
Proof.
    -   intros a b.
        classic_case (0 ≠ a ∨ 0 ≠ b) as [ab_nz|ab_z].
        +   apply (ufd_gcd_gcd a b ab_nz).
        +   rewrite not_or in ab_z.
            do 2 rewrite not_not in ab_z.
            destruct ab_z; subst a b.
            split; apply divides_zero.
    -   intros a b ab_nz.
        apply (ufd_gcd_gcd a b ab_nz).
Qed.

End UniqueFactorization.

Close Scope nat_scope.
