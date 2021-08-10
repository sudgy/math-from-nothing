Require Import init.

Require Import nat0.

#[universes(template)]
Class EuclideanDomain U `{Plus U} `{Zero U} `{Mult U} := {
    euclidean_f : U → nat0;
    euclidean_division :
        ∀ a b, 0 ≠ b → ∃ q r, a = b*q + r ∧ euclidean_f r < euclidean_f b
}.

Definition divides {U} `{Mult U} a b := ∃ c, c * a = b.
(** Note that this is the unicode symbol '∣', not '|'!  It is the LaTeX \mid.
The reason for this is that using the normal '|' causes issues with things like
pattern matching.
*)
Infix "∣" := divides (at level 50).

Definition even {U} `{Plus U, Mult U, One U} a := 2 ∣ a.
Definition odd {U} `{Plus U, Mult U, One U} a := ¬(2 ∣ a).

(* begin hide *)
Lemma nat0_euclidean : ∀ a b, 0 ≠ b → ∃ q r, a = b*q + r ∧ r < b.
    intros a b b_nz.
    pose (S n := a < b * n).
    assert (∃ n, S n) as S_ex.
    {
        exists (nat0_suc a).
        unfold S.
        rewrite nat0_mult_rsuc.
        assert (a <= b * a) as eq.
        {
            rewrite <- (mult_lid a) at 1.
            apply nat0_le_rmult.
            nat0_destruct b; try contradiction.
            unfold one; cbn; rewrite nat0_sucs_le.
            apply nat0_le_zero.
        }
        assert (0 < b) as b_pos by (split; try assumption; apply nat0_le_zero).
        apply le_lplus with b in eq.
        apply lt_rplus with a in b_pos.
        rewrite plus_lid in b_pos.
        exact (lt_le_trans b_pos eq).
    }
    pose proof (nat0_wo _ S_ex) as [q [Sq q_min]].
    nat0_destruct q.
    {
        unfold S in Sq.
        rewrite mult_ranni in Sq.
        contradiction (nat0_lt_zero _ Sq).
    }
    assert (b * q <= a) as leq.
    {
        classic_contradiction contr.
        rewrite nle_lt in contr.
        specialize (q_min _ contr).
        rewrite <- nlt_le in q_min.
        contradiction (q_min (nat0_lt_suc q)).
    }
    apply nat0_le_ex in leq as [r r_eq].
    exists q, r.
    symmetry in r_eq.
    split.
    -   exact r_eq.
    -   unfold S in Sq.
        rewrite nat0_mult_rsuc in Sq.
        rewrite r_eq in Sq.
        rewrite plus_comm in Sq.
        apply lt_plus_rcancel in Sq.
        exact Sq.
Qed.
(* end hide *)
Instance nat0_euclidean_class : EuclideanDomain nat0 := {
    euclidean_f := λ x, x;
    euclidean_division := nat0_euclidean
}.

(* begin hide *)
Section Div.

Context {U} `{Up : Plus U,
                  @PlusAssoc U Up,
                  @PlusComm U Up,
              Uz : Zero U,
                  @PlusLid U Up Uz,
              Un : Neg U,
                  @PlusLinv U Up Uz Un,
              Um : Mult U,
                  @MultAssoc U Um,
                  @MultComm U Um,
                  @Ldist U Up Um,
                  @Rdist U Up Um,
                  @MultLanni U Uz Um,
                  @MultRanni U Uz Um,
              Uo : One U,
                  @MultLid U Um Uo,
                  @MultRid U Um Uo,
                  @MultLcancel U Uz Um,
                  @MultRcancel U Uz Um,
              Ul : Order U,
                  @Connex U le,
                  @Antisymmetric U le,
                  @Transitive U le
              }.

Lemma divides_refl : ∀ a, a ∣ a.
    intros a.
    exists 1.
    apply mult_lid.
Qed.
(* end hide *)
Global Instance divides_refl_class : Reflexive divides := {
    refl := divides_refl
}.

(* begin hide *)
Lemma divides_trans : ∀ a b c, a ∣ b → b ∣ c → a ∣ c.
    intros a b c [d eq1] [e eq2].
    exists (e * d).
    rewrite <- mult_assoc.
    rewrite eq1.
    rewrite eq2.
    reflexivity.
Qed.
(* end hide *)
Global Instance divides_trans_class : Transitive divides := {
    trans := divides_trans
}.

Theorem one_divides : ∀ n, 1 ∣ n.
    intros n.
    exists n.
    apply mult_rid.
Qed.

Theorem divides_zero : ∀ a, a ∣ 0.
    intros a.
    exists 0.
    apply mult_lanni.
Qed.

Theorem divides_neg : ∀ a b, a ∣ b → a ∣ -b.
    intros a b [c eq].
    exists (-c).
    rewrite mult_lneg.
    apply f_equal.
    exact eq.
Qed.

Theorem plus_stays_divides : ∀ p a b, p ∣ a → p ∣ b → p ∣ (a + b).
    intros p a b [c c_eq] [d d_eq].
    exists (c + d).
    rewrite <- c_eq, <- d_eq.
    apply rdist.
Qed.

Theorem plus_changes_divides : ∀ p a b,
                               p ∣ a → ¬(p ∣ b) → ¬(p ∣ (a + b)).
    intros p a b [c c_eq] not [d d_eq].
    rewrite <- c_eq in d_eq.
    apply lplus with (-(c * p)) in d_eq.
    rewrite plus_assoc, plus_linv, plus_lid in d_eq.
    rewrite <- mult_lneg in d_eq.
    rewrite <- rdist in d_eq.
    unfold divides in not.
    rewrite not_ex in not.
    specialize (not (-c + d)).
    contradiction.
Qed.

Theorem mult_factors_extend : ∀ p a b, p ∣ a → p ∣ a * b.
    intros p a b [c eq].
    exists (b * c).
    rewrite (mult_comm a).
    rewrite <- eq.
    symmetry; apply mult_assoc.
Qed.

Theorem mult_factors_back : ∀ a b c, a * b = c → a ∣ c ∧ b ∣ c.
    intros a b c eq.
    split.
    -   exists b.
        rewrite mult_comm.
        exact eq.
    -   exists a.
        exact eq.
Qed.

(* begin hide *)
End Div.
(* end hide *)
Theorem nat0_plus_changes_divides : ∀ p a b,
                                    p ∣ a → ¬(p ∣ b) → ¬(p ∣ (a + b)).
    intros p a b [c c_eq] not [d d_eq].
    rewrite <- c_eq in d_eq.
    destruct (trichotomy d c) as [[ltq|eq]|ltq].
    -   apply nat0_lt_ex in ltq.
        destruct ltq as [x [x_nz x_eq]].
        rewrite <- x_eq in d_eq.
        rewrite rdist, <- plus_assoc in d_eq.
        rewrite <- (plus_rid (d * p)) in d_eq at 1.
        apply plus_lcancel in d_eq.
        apply nat0_plus_zero in d_eq as [eq1 eq2].
        apply nat0_mult_zero in eq1 as [x_z|p_z]; try contradiction.
        subst.
        apply not.
        apply refl.
    -   subst.
        rewrite <- (plus_rid (c * p)) in d_eq at 1.
        apply plus_lcancel in d_eq.
        subst.
        apply not.
        apply divides_zero.
    -   apply nat0_lt_ex in ltq.
        destruct ltq as [x [x_nz x_eq]].
        rewrite <- x_eq in d_eq.
        rewrite rdist in d_eq.
        apply plus_lcancel in d_eq.
        subst.
        apply not.
        exists x.
        reflexivity.
Qed.

Theorem nat0_even_neq_odd : ∀ m n, m * 2 ≠ n * 2 + 1.
    intros m n eq.
    assert (even (m * 2)) as m_even by (exists m; reflexivity).
    assert (even (n * 2)) as n_even by (exists n; reflexivity).
    assert (¬2 ∣ (one (U := nat0))) as ndiv.
    {
        intros [c c_eq].
        nat0_destruct c.
        -   rewrite mult_lanni in c_eq.
            inversion c_eq.
        -   rewrite nat0_mult_lsuc in c_eq.
            assert ((one (U := nat0)) < 2) as leq.
            {
                split.
                -   unfold one; cbn.
                    unfold plus; cbn.
                    unfold le; cbn.
                    exact true.
                -   intro contr; inversion contr.
            }
            pose proof (nat0_le_zero (c * 2)) as leq2.
            apply le_lplus with 2 in leq2.
            rewrite plus_rid in leq2.
            pose proof (lt_le_trans leq leq2) as [C0 C1].
            symmetry in c_eq; contradiction.
    }
    pose proof (nat0_plus_changes_divides 2 (n * 2) 1 n_even ndiv).
    rewrite <- eq in H.
    contradiction.
Qed.

Theorem nat0_odd_plus_one : ∀ a, odd a → ∃ b, a = 2 * b + 1.
    intros a a_odd.
    assert (0 ≠ 2) as two_nz by (intro contr; inversion contr).
    pose proof (euclidean_division a 2 two_nz) as [q [r [eq ltq]]].
    cbn in ltq.
    exists q.
    assert (0 ≠ r) as r_nz.
    {
        intro contr.
        subst.
        rewrite plus_rid in a_odd.
        unfold odd, divides in a_odd.
        rewrite not_ex in a_odd.
        apply (a_odd q).
        apply mult_comm.
    }
    rewrite eq.
    apply lplus.
    apply antisym.
    -   change 2 with (nat0_suc 1) in ltq.
        rewrite nat0_lt_suc_le in ltq.
        exact ltq.
    -   classic_contradiction contr.
        rewrite nle_lt in contr.
        unfold one in contr; cbn in contr.
        rewrite nat0_lt_suc_le in contr.
        apply nat0_le_zero_eq in contr.
        contradiction.
Qed.

Theorem nat0_div_le : ∀ a b, 0 ≠ b → a ∣ b → a <= b.
    intros a b b_nz [c c_eq].
    rewrite <- c_eq.
    nat0_destruct a.
    -   rewrite mult_ranni.
        apply refl.
    -   rewrite <- (mult_lid (nat0_suc a)) at 1.
        apply nat0_le_rmult.
        classic_contradiction contr.
        rewrite nle_lt in contr.
        change 1 with (nat0_suc 0) in contr.
        rewrite nat0_lt_suc_le in contr.
        apply nat0_le_zero_eq in contr.
        subst c.
        rewrite mult_lanni in c_eq.
        contradiction.
Qed.
