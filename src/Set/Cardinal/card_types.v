Require Import init.

Require Import set.
Require Import card.
Require Import nat.
Require Import int.
Require Import rat.

(* begin hide *)
Open Scope card_scope.

Section EquivCard.

Context {U : Type}.
(* end hide *)
Theorem equiv_card_le : ∀ E : equivalence U, |equiv_type E| ≤ |U|.
Proof.
    intros E.
    unfold le; equiv_simpl.
    exists (λ (x : equiv_type E), ex_val [|x]).
    split.
    intros a b eq.
    destruct a as [a_set a_in], b as [b_set b_in].
    cbn in eq.
    apply set_type_eq; cbn.
    rewrite_ex_val a a_eq.
    rewrite_ex_val b b_eq.
    rewrite <- a_eq, <- b_eq.
    rewrite eq.
    reflexivity.
Qed.

(* begin hide *)
End EquivCard.

Section DenseInfinite.

Context {U} `{
    UO : Order U,
    @Connex U le,
    @Antisymmetric U le,
    @Transitive U le,
    @Dense U (strict le)
}.
(* end hide *)
Hypothesis distinct : ∃ a b : U, a ≠ b.

Theorem dense_open_infinite :
    ∀ a b, a < b → infinite (|set_type (open_interval a b)|).
Proof.
    intros a b ab.
    classic_contradiction contr.
    unfold infinite in contr.
    rewrite nle_lt in contr.
    pose proof (finite_well_ordered_set _ contr (dense a b ab)) as
        [m [[m_gt m_lt] m_min]].
    pose (S := (open_interval a b - ❴m❵)%set).
    assert (finite (|set_type S|)) as S_fin.
    {
        apply (le_lt_trans2 contr).
        unfold le; equiv_simpl.
        assert (∀ x : set_type S, open_interval a b [x|]) as x_in.
        {
            intros [x [[x_gt x_lt]]].
            split; assumption.
        }
        exists (λ x, [[x|]|x_in x]).
        split.
        intros x y eq.
        apply set_type_eq in eq; cbn in eq.
        apply set_type_eq in eq.
        exact eq.
    }
    assert (∃ x, S x) as S_ex.
    {
        pose proof (dense m b m_lt) as [x [x_gt x_lt]].
        exists x.
        split.
        -   split.
            +   exact (trans m_gt x_gt).
            +   exact x_lt.
        -   apply x_gt.
    }
    pose proof (finite_well_ordered_set _ S_fin S_ex) as
        [n [[[n_gt n_lt] neq] n_min]].
    assert (m < n) as mn.
    {
        split; try exact neq.
        apply m_min.
        split; assumption.
    }
    pose proof (dense m n mn) as [x [x_gt x_lt]].
    assert (S x) as Sx.
    {
        split.
        -   split.
            +   exact (trans m_gt x_gt).
            +   exact (trans x_lt n_lt).
        -   apply x_gt.
    }
    specialize (n_min x Sx).
    destruct (le_lt_trans n_min x_lt); contradiction.
Qed.

Theorem dense_closed_infinite :
    ∀ a b, a < b → infinite (|set_type (closed_interval a b)|).
Proof.
    intros a b ab.
    apply (trans (dense_open_infinite a b ab)).
    unfold le; equiv_simpl.
    assert (∀ x : set_type (open_interval a b), closed_interval a b [x|])
        as x_in.
    {
        intros [x [x_gt x_lt]].
        split.
        -   apply x_gt.
        -   apply x_lt.
    }
    exists (λ x, [[x|]|x_in x]).
    split.
    intros x y eq.
    apply set_type_eq in eq; cbn in eq.
    apply set_type_eq in eq.
    exact eq.
Qed.

(* begin hide *)
End DenseInfinite.
(* end hide *)
Theorem int_size : |int| = |nat|.
Proof.
    apply antisym.
    -   apply (trans (equiv_card_le _)).
        rewrite card_mult_type.
        rewrite nat_mult_nat.
        apply refl.
    -   unfold le; equiv_simpl.
        exists from_nat.
        exact from_nat_inj.
Qed.

Theorem rat_size : |rat| = |nat|.
Proof.
    apply antisym.
    -   apply (trans (equiv_card_le _)).
        rewrite card_mult_type.
        pose proof (card_sub_le int (λ x, 0 ≠ x)) as leq.
        apply card_le_lmult with (|int|) in leq.
        rewrite int_size in leq at 2 3.
        rewrite nat_mult_nat in leq.
        exact leq.
    -   unfold le; equiv_simpl.
        exists from_nat.
        apply from_nat_inj.
Qed.

(* begin hide *)
Close Scope card_scope.

(* end hide *)
Section CardArch.

Context {U} `{
    UP : Plus U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    UZ : Zero U,
    @PlusLid U UP UZ,
    @PlusRid U UP UZ,
    UN : Neg U,
    @PlusLinv U UP UZ UN,
    @PlusRinv U UP UZ UN,
    UM : Mult U,
    @MultComm U UM,
    @MultAssoc U UM,
    @Ldist U UP UM,
    @Rdist U UP UM,
    UE : One U,
    @MultLid U UM UE,
    @MultRid U UM UE,
    @MultLcancel U UZ UM,
    @MultRcancel U UZ UM,
    UO : Order U,
    @Antisymmetric U le,
    @Transitive U le,
    @Connex U le,
    @OrderLplus U UP UO,
    @OrderRplus U UP UO,
    @OrderMult U UZ UM UO,
    @OrderLmult U UZ UM UO,
    @OrderRmult U UZ UM UO,
    @OrderMultLcancel U UZ UM UO,
    @OrderMultRcancel U UZ UM UO,
    NotTrivial U,
    UD : Div U,
    @MultLinv U UZ UM UE UD,
    @MultRinv U UZ UM UE UD,
    @Archimedean U UP UZ UO
}.

Local Open Scope card_scope.

Theorem arch_ordered_size : |U| ≤ 2 ^ |nat|.
Proof.
    rewrite <- rat_size.
    rewrite <- power_set_size.
    unfold le; equiv_simpl.
    exists (λ x, (λ q, from_rat q < x)).
    cut (∀ a b, a ≤ b →
        ((λ q : rat, from_rat q < a) = (λ q : rat, from_rat q < b)
        → a = b)).
    {
        intros wlog.
        split.
        intros a b eq.
        destruct (connex a b) as [leq|leq].
        +   apply wlog; assumption.
        +   symmetry in eq.
            symmetry.
            apply wlog; assumption.
    }
    intros a b leq eq.
    classic_contradiction neq.
    pose proof (rat_dense_in_arch a b (make_and leq neq)) as [r [r_gt r_lt]].
    pose proof (func_eq _ _ eq r) as eq2.
    cbn in eq2.
    rewrite <- eq2 in r_lt.
    destruct (trans r_gt r_lt); contradiction.
Qed.

End CardArch.
