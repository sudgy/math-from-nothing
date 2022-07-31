Require Import init.

Require Import rat.
Require Import set.

Require Export dedekind_real_base.

Unset Keyed Unification.

(* begin hide *)
Open Scope set_scope.
(* end hide *)
Global Instance real_order : Order real := {
    le a b := [a|] ⊆ [b|]
}.

(* begin hide *)
Lemma real_le_connex : ∀ a b, {a <= b} + {b <= a}.
    intros [a a_cut] [b b_cut].
    unfold le; cbn.
    classic_case (a ⊆ b) as [ab|nab]; try (left; exact ab).
    right.
    unfold subset in nab; cbn in nab.
    rewrite not_all in nab.
    destruct nab as [u nab].
    rewrite not_impl in nab.
    destruct nab as [au nbu].
    intros l bl.
    apply (land (rand (rand a_cut)) l u au).
    apply (dedekind_lt b b_cut l u bl nbu).
Qed.
Global Instance real_le_connex_class : Connex le := {
    connex := real_le_connex
}.

Lemma real_le_antisymmetric : ∀ a b, a <= b → b <= a → a = b.
    intros [a a_cut] [b b_cut].
    unfold le; cbn.
    intros ab ba.
    apply set_type_eq; cbn.
    exact (antisym ab ba).
Qed.
Global Instance real_le_antisym_class : Antisymmetric le := {
    antisym := real_le_antisymmetric
}.

Lemma real_le_transitive : ∀ a b c, a <= b → b <= c → a <= c.
    intros a b c.
    unfold le; cbn.
    apply trans.
Qed.
Global Instance real_le_trans_class : Transitive le := {
    trans := real_le_transitive;
}.

Lemma real_sup_complete : ∀ S : real → Prop, (∃ x, S x) →
        has_upper_bound le S → has_supremum le S.
    intros S [[l l_cut] Sl] [[u u_cut] u_upper].
    pose (α a := ∃ x, S x ∧ [x|] a).
    assert (dedekind_cut α) as α_cut.
    {
        split.
        2: split.
        3: split.
        -   intro contr.
            pose proof (land u_cut) as u'_ex.
            apply not_all_not_ex in u'_ex as [u' u'u].
            assert (α u') as αu' by (rewrite contr; exact true).
            destruct αu' as [x [Sx xu']].
            apply u_upper in Sx.
            apply Sx in xu'.
            contradiction.
        -   apply ex_not_empty.
            unfold α.
            pose proof (land (rand l_cut)) as l'_ex.
            apply not_empty_ex in l'_ex.
            destruct l'_ex as [l' l'l].
            exists l', [l|l_cut].
            split; assumption.
        -   intros l' u' [[x x_cut] [Sx xu']] ltq.
            cbn in xu'.
            unfold α.
            exists [x|x_cut].
            split; try assumption.
            cbn.
            exact (land (rand (rand x_cut)) _ u' xu' ltq).
        -   intros l' [[x x_cut] [Sx xl']].
            cbn in xl'.
            pose proof (rand (rand (rand x_cut)) l' xl') as [u' [xu' ltq]].
            exists u'.
            split; try assumption.
            exists [x|x_cut].
            split; assumption.
    }
    exists [α|α_cut].
    split.
    -   intros [x x_cut] Sx a xa; cbn in *.
        exists [x|x_cut].
        split; assumption.
    -   intros [x x_cut] x_upper a [[y y_cut] [Sy ya]]; cbn in *.
        apply (x_upper [y|y_cut]); assumption.
Qed.
Global Instance real_sup_complete_class : SupremumComplete le := {
    sup_complete := real_sup_complete
}.
(* end hide *)

Theorem rat_to_real_le : ∀ a b, rat_to_real a <= rat_to_real b ↔ a <= b.
    intros a b; split; intro leq.
    -   unfold le in leq; cbn in leq.
        unfold rat_to_real_base in leq.
        classic_contradiction contr.
        rewrite nle_lt in contr.
        apply leq in contr.
        destruct contr; contradiction.
    -   intros x ax.
        cbn in *; unfold rat_to_real_base in *.
        exact (lt_le_trans ax leq).
Qed.

Theorem gt_rat_to_real_in : ∀ a b, rat_to_real a < b → [b|] a.
    intros a [b b_cut] [leq neq]; cbn.
    classic_contradiction contr.
    apply neq.
    apply antisym; try exact leq.
    intros x bx; cbn in *.
    exact (dedekind_lt _ b_cut _ _ bx contr).
Qed.

Theorem real_lt_ex_between : ∀ a b, a < b → ∃ x, ¬[a|] x ∧ [b|] x.
    intros a b ab.
    destruct ab as [leq neq].
    classic_contradiction contr.
    apply neq.
    apply antisym; try exact leq.
    intros x bx.
    rewrite not_ex in contr.
    specialize (contr x).
    not_simpl in contr.
    destruct contr as [ax|nbx].
    -   exact ax.
    -   contradiction.
Qed.
(* begin hide *)
Close Scope set_scope.
(* end hide *)
