Require Import init.

Require Export ring_ideal.

Require Import euclidean_domain.
Require Import gcd.
Require Import mult_div.
Require Import nat.
Require Import set.
Require Import unordered_list.
Require Import order_minmax.

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

End PrincipleIdealDef.
Section PrincipleIdeal.

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
    @MultLid U UM UO,
    @MultRid U UM UO,
    @EuclideanDomain U UP UZ UM
}.

Program Instance euclidean_principle_ideal : PrincipleIdealDomain.
Next Obligation.
    classic_case (∀ x, ideal_set I x → 0 = x) as [I_z|I_nz].
    {
        exists 0.
        apply ideal_eq.
        intros x.
        split.
        -   intros Ix.
            apply I_z in Ix.
            rewrite <- Ix.
            apply ideal_zero.
        -   intros [l x_eq].
            assert (0 = x) as x_z.
            {
                rewrite x_eq.
                clear x_eq.
                induction l using ulist_induction.
                -   rewrite ulist_image_end, ulist_sum_end.
                    reflexivity.
                -   rewrite ulist_image_add, ulist_sum_add.
                    rewrite <- IHl.
                    rewrite plus_rid.
                    destruct a as [[a1 a2] [a3 a3_eq]].
                    unfold singleton in a3_eq.
                    rewrite <- a3_eq; cbn.
                    rewrite mult_ranni, mult_lanni.
                    reflexivity.
            }
            rewrite <- x_z.
            apply ideal_zero.
    }
    pose (S n := ∃ a, 0 ≠ a ∧ ideal_set I a ∧ euclidean_f a = n).
    assert (∃ n, S n) as S_ex.
    {
        rewrite not_all in I_nz.
        destruct I_nz as [a a_nz].
        rewrite not_impl in a_nz.
        exists (euclidean_f a).
        exists a.
        repeat split; apply a_nz.
    }
    pose proof (well_ordered S S_ex) as [n [[b [b_nz [Ib n_eq]]] n_min]].
    exists b.
    apply ideal_eq.
    intros a.
    split.
    -   intros Ia.
        cbn.
        unfold ideal_generated_by_set.
        pose proof (euclidean_division a b b_nz) as [q [r [eq ltq]]].
        classic_case (0 = r) as [r_z | r_nz].
        +   rewrite <- r_z in eq.
            rewrite plus_rid in eq.
            exists (((1, q), [b|Logic.eq_refl]) ::: ulist_end).
            rewrite ulist_image_add, ulist_sum_add; cbn.
            rewrite ulist_image_end, ulist_sum_end.
            rewrite plus_rid.
            rewrite mult_lid.
            exact eq.
        +   destruct ltq as [|ltq]; [>contradiction|].
            assert (S (euclidean_f r)) as Sr.
            {
                exists r.
                repeat split.
                -   exact r_nz.
                -   apply plus_rlmove in eq.
                    rewrite <- eq.
                    apply ideal_plus.
                    +   apply ideal_neg.
                        apply ideal_rmult.
                        exact Ib.
                    +   exact Ia.
            }
            specialize (n_min _ Sr).
            rewrite n_eq in ltq.
            destruct (le_lt_trans n_min ltq); contradiction.
    -   intros [l a_eq].
        rewrite a_eq; clear a_eq.
        induction l as [|c l] using ulist_induction.
        +   rewrite ulist_image_end, ulist_sum_end.
            apply ideal_zero.
        +   rewrite ulist_image_add, ulist_sum_add.
            apply ideal_plus; [>clear IHl|exact IHl].
            destruct c as [[c1 c2] [c3 c3_eq]]; cbn.
            unfold singleton in c3_eq.
            rewrite <- c3_eq.
            apply ideal_rmult.
            apply ideal_lmult.
            exact Ib.
Qed.

End PrincipleIdeal.

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
    @PrincipleIdealDomain U UP UZ UN UM UPA UPC UPZ UPN UL UR UMA
}.

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
    destruct H4 as [da db].
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

End PrincipleIdeal.
