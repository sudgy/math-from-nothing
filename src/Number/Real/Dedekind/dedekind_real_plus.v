Require Import init.

Require Import rat.
Require Import set.
Require Import order_minmax.

Require Export dedekind_real_base.
Require Import dedekind_real_order.

(* begin hide *)
Open Scope real_scope.
(* end hide *)
Definition real_plus_base a b := λ x, ∃ r s, a r ∧ b s ∧ x = r + s.
Infix "⊕" := real_plus_base : real_scope.

Theorem real_plus_dedekind : ∀ (a b : real), dedekind_cut ([a|] ⊕ [b|]).
Proof.
    intros [a a_cut] [b b_cut]; cbn.
    split.
    2: split.
    3: split.
    -   intros contr.
        pose proof (land a_cut) as a_n.
        pose proof (land b_cut) as b_n.
        apply not_all_not_ex in a_n as [x nax], b_n as [y nby].
        assert (all (x + y)) as eq by exact true.
        rewrite <- contr in eq.
        destruct eq as [r [s [ar [bs eq]]]].
        pose proof (dedekind_lt _ a_cut _ _ ar nax) as ltq1.
        pose proof (dedekind_lt _ b_cut _ _ bs nby) as ltq2.
        pose proof (lt_lrplus ltq1 ltq2) as ltq.
        symmetry in eq.
        destruct ltq; contradiction.
    -   apply ex_not_empty.
        pose proof (land (rand a_cut)) as a_n.
        pose proof (land (rand b_cut)) as b_n.
        apply not_empty_ex in a_n as [r ar].
        apply not_empty_ex in b_n as [s bs].
        exists (r + s), r, s.
        repeat split; trivial.
    -   intros l u [r [s [ar [bs eq]]]] lu.
        apply lt_rplus with u in lu.
        rewrite <- (mult_rid u) in lu at 2 3.
        rewrite <- ldist in lu.
        apply lt_rmult_pos with (div 2) in lu.
        2: apply div_pos; exact two_pos.
        rewrite mult_rrinv in lu by apply two_pos.
        rewrite eq in lu at 2.
        pose proof lu as eq2; rename lu into eq1.
        apply lt_plus_rrmove in eq1.
        apply lt_plus_rlmove in eq2.
        pose proof (land (rand (rand a_cut)) _ _ ar eq1) as al.
        pose proof (land (rand (rand b_cut)) _ _ bs eq2) as bl.
        exists ((l + u) * div 2 + -s), (-r + (l + u) * div 2).
        repeat split; try assumption.
        plus_bring_left ((l + u) * div 2).
        rewrite plus_assoc.
        rewrite plus_half.
        rewrite <- neg_plus.
        rewrite (plus_comm s).
        rewrite <- eq.
        rewrite plus_rrinv.
        reflexivity.
    -   intros l [r [s [ar [bs eq]]]].
        pose proof (rand (rand (rand a_cut)) _ ar) as [r' [ar' r_lt]].
        pose proof (rand (rand (rand b_cut)) _ bs) as [s' [bs' s_lt]].
        exists (r' + s').
        split.
        +   exists r', s'.
            repeat split; trivial.
        +   rewrite eq.
            apply lt_lrplus; assumption.
Qed.

Global Instance real_plus : Plus real := {
    plus a b := [_|real_plus_dedekind a b]
}.

Lemma real_plus_comm_ : ∀ a b, a + b = b + a.
Proof.
    intros [a a_cut] [b b_cut].
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply predicate_ext.
    intros x; split.
    -   intros [r [s [ar [bs eq]]]].
        exists s, r.
        rewrite plus_comm.
        repeat split; assumption.
    -   intros [r [s [br [as_ eq]]]].
        exists s, r.
        rewrite plus_comm.
        repeat split; assumption.
Qed.
Global Instance real_plus_comm : PlusComm real := {
    plus_comm := real_plus_comm_
}.

Lemma real_plus_assoc_ : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
    intros [a a_cut] [b b_cut] [c c_cut].
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply predicate_ext.
    intros x; split.
    -   intros [r1 [s1 [ar1 [[r2 [s2 [br2 [cs2 eq1]]]] eq2]]]].
        exists (r1 + r2), s2.
        split.
        +   exists r1, r2.
            repeat split; trivial.
        +   split; try exact cs2.
            rewrite eq2, eq1.
            apply plus_assoc.
    -   intros [r1 [s1 [[r2 [s2 [ar2 [bs2 eq1]]]] [cs1 eq2]]]].
        exists r2, (s1 + s2).
        split; try exact ar2.
        split.
        +   exists s2, s1.
            repeat split; try assumption.
            apply plus_comm.
        +   rewrite eq2, eq1.
            rewrite (plus_comm s1 s2).
            rewrite plus_assoc.
            reflexivity.
Qed.
Global Instance real_plus_assoc : PlusAssoc real := {
    plus_assoc := real_plus_assoc_
}.

Global Instance real_zero : Zero real := {
    zero := rat_to_real 0
}.

Lemma real_plus_lid_ : ∀ a, 0 + a = a.
Proof.
    intros [a a_cut].
    unfold plus, zero; cbn.
    unfold rat_to_real_base; cbn.
    apply set_type_eq; cbn.
    apply predicate_ext; intros x; split.
    -   intros [r [s [r_pos [as_ eq]]]].
        apply (land (rand (rand a_cut)) _ s as_).
        rewrite eq.
        rewrite <- (plus_lid s) at 2.
        apply lt_rplus.
        exact r_pos.
    -   intros ax.
        pose proof (rand (rand (rand a_cut)) x ax) as [y [ay ltq]].
        exists (x + -y), y.
        split.
        +   apply lt_plus_anb_0_a_b.
            exact ltq.
        +   split; try exact ay.
            rewrite plus_rlinv.
            reflexivity.
Qed.
Global Instance real_plus_lid : PlusLid real := {
    plus_lid := real_plus_lid_;
}.

Definition real_neg_base a := λ p, ∃ r, 0 < r ∧ ¬(a (-p + -r)).
Notation "⊖ a" := (real_neg_base a) : real_scope.

Lemma real_neg_dedekind : ∀ a : real, dedekind_cut (⊖ [a|]).
Proof.
    intros [a a_cut]; cbn.
    split.
    2: split.
    3: split.
    -   intro contr.
        pose proof (land (rand a_cut)) as x_ex.
        apply not_empty_ex in x_ex as [x ax].
        assert (all (-x)) as x_in by exact true.
        rewrite <- contr in x_in.
        destruct x_in as [r [r_pos nin]].
        rewrite neg_neg in nin.
        apply nin.
        apply (land (rand (rand a_cut)) _ _ ax).
        rewrite <- (plus_rid x) at 2.
        apply lt_lplus.
        apply pos_neg2.
        exact r_pos.
    -   apply ex_not_empty.
        pose proof (land a_cut) as x_ex.
        apply not_all_not_ex in x_ex.
        destruct x_ex as [x nax].
        exists (-x + -(1)), 1.
        split; try exact one_pos.
        rewrite neg_plus, neg_neg.
        rewrite plus_rlinv.
        exact nax.
    -   intros l u [r [r_pos na]] ltq.
        exists (u + r + -l).
        split.
        +   apply lt_plus_0_anb_b_a in ltq.
            pose proof (lt_lrplus r_pos ltq) as ltq2.
            rewrite plus_lid, plus_assoc in ltq2.
            rewrite (plus_comm r) in ltq2.
            exact ltq2.
        +   do 2 rewrite neg_plus.
            rewrite plus_comm.
            rewrite plus_rlinv.
            exact na.
    -   intros l [r [r_pos na]].
        assert (0 < r * div 2) as r2_pos.
        {
            apply lt_mult_rcancel_pos with 2; try apply two_pos.
            rewrite mult_lanni.
            rewrite mult_rlinv by apply two_pos.
            exact r_pos.
        }
        exists (l + r * div 2).
        split.
        +   exists (r * div 2).
            split; try exact r2_pos.
            rewrite neg_plus.
            rewrite <- plus_assoc, <- neg_plus.
            rewrite plus_half.
            exact na.
        +   rewrite <- (plus_rid l) at 1.
            apply lt_lplus.
            exact r2_pos.
Qed.

Global Instance real_neg : Neg real := {
    neg a := [_|real_neg_dedekind a]
}.
Lemma real_plus_linv_pos : ∀ a, 0 < a → -a + a = 0.
Proof.
    intros [a a_cut] a_pos'.
    assert (∀ x, x <= 0 → a x) as a_pos.
    {
        destruct a_pos' as [a_pos a_neq].
        unfold zero in a_pos; cbn in a_pos.
        unfold rat_to_real, le in a_pos; equiv_simpl in a_pos.
        unfold rat_to_real_base in a_pos.
        unfold zero in a_neq; cbn in a_neq.
        unfold rat_to_real in a_neq; equiv_simpl in a_neq.
        unfold rat_to_real_base in a_neq.
        intros x x_leq.
        classic_case (x = 0) as [xz|xnz].
        -   subst.
            classic_contradiction contr.
            apply a_neq.
            apply set_type_eq; cbn.
            apply antisym; try exact a_pos.
            intros x ax.
            exact (dedekind_lt _ a_cut _ _ ax contr).
        -   apply a_pos.
            split; assumption.
    }
    clear a_pos'.
    unfold plus, neg, zero; cbn.
    unfold rat_to_real; cbn.
    apply set_type_eq; cbn.
    unfold rat_to_real_base.
    apply predicate_ext; intros x; split.
    -   intros [r [s [[t [t_pos na]] [as_ eq]]]].
        pose proof (dedekind_lt _ a_cut _ _ as_ na) as ltq.
        apply lt_plus_rlmove in ltq.
        rewrite neg_neg in ltq.
        rewrite <- eq in ltq.
        apply pos_neg2 in t_pos.
        exact (trans ltq t_pos).
    -   intros x_neg.
        pose proof (land a_cut) as u_ex.
        apply not_all_not_ex in u_ex.
        destruct u_ex as [u nau].
        assert (0 < u) as u_pos.
        {
            classic_contradiction contr.
            rewrite nlt_le in contr.
            specialize (a_pos _ contr).
            contradiction.
        }
        apply neg_pos2 in x_neg.
        pose proof (archimedean u (-x) u_pos x_neg) as [n' eq].
        pose (S m := ¬a (m × -x)).
        assert (∃ m, S m) as S_ex.
        {
            exists n'.
            intros contr.
            pose proof (land (rand (rand a_cut)) _ _ contr eq).
            contradiction.
        }
        pose proof (well_ordered S S_ex) as [n [Sn n_least]].
        nat_destruct n.
        +   unfold zero, S in Sn; cbn in Sn.
            specialize (a_pos 0 (refl _)).
            contradiction.
        +   classic_case (∃ u, u < nat_suc n × -x ∧ ¬a u) as [not_cusp|cusp].
            *   exists (nat_suc n × x), (n × -x).
                repeat split.
                --  destruct not_cusp as [u' [u'_lt nau']].
                    apply lt_plus_0_anb_b_a in u'_lt.
                    exists (nat_suc n × -x + -u').
                    split; try exact u'_lt.
                    rewrite abstract_mult_rneg.
                    rewrite neg_plus.
                    rewrite plus_lrinv.
                    rewrite neg_neg.
                    exact nau'.
                --  classic_contradiction contr.
                    specialize (n_least _ contr).
                    pose proof (le_lt_trans n_least (nat_lt_suc _)) as [C0 C1].
                    contradiction.
                --  cbn.
                    rewrite <- abstract_mult_rneg.
                    rewrite plus_rrinv.
                    reflexivity.
            *   exists (nat_suc n × x + x * div 2), (n × -x + -x * div 2).
                repeat split.
                --  apply lt_rmult_pos with (div 2) in x_neg.
                    2: apply div_pos; exact two_pos.
                    rewrite mult_lanni in x_neg.
                    exists (-x * div 2).
                    split; try exact x_neg.
                    rewrite neg_plus.
                    rewrite abstract_mult_rneg.
                    rewrite mult_lneg.
                    rewrite plus_rrinv.
                    exact Sn.
                --  rewrite not_ex in cusp.
                    specialize (cusp (n × -x + -x * div 2)).
                    rewrite not_and, not_not, nlt_le in cusp.
                    destruct cusp as [cusp|cusp]; [>|exact cusp].
                    cbn in cusp.
                    rewrite plus_comm in cusp.
                    apply le_plus_lcancel in cusp.
                    apply le_neg in cusp.
                    rewrite mult_lneg in cusp.
                    do 2 rewrite neg_neg in cusp.
                    apply le_rmult_pos with 2 in cusp.
                    2: apply two_pos.
                    rewrite mult_rlinv in cusp by apply two_pos.
                    rewrite ldist in cusp.
                    rewrite mult_rid in cusp.
                    rewrite <- (plus_rid x) in cusp at 1.
                    apply le_plus_lcancel in cusp.
                    apply pos_neg in cusp.
                    destruct (le_lt_trans cusp x_neg); contradiction.
                --  cbn.
                    rewrite <- abstract_mult_rneg.
                    rewrite <- plus_assoc.
                    rewrite (plus_comm (-(n × x))).
                    rewrite mult_lneg.
                    rewrite plus_lrinv.
                    rewrite plus_rrinv.
                    reflexivity.
Qed.

Lemma real_plus_linv_ : ∀ a, -a + a = 0.
Proof.
    intros a.
    destruct (trichotomy 0 a) as [[a_pos|a_z]|a_neg].
    -   apply real_plus_linv_pos.
        exact a_pos.
    -   subst.
        rewrite plus_rid.
        unfold neg, zero; cbn.
        unfold rat_to_real; cbn.
        apply set_type_eq; cbn.
        unfold rat_to_real_base.
        apply predicate_ext; intros x; split.
        +   intros [r [r_pos eq]].
            rewrite nlt_le in eq.
            rewrite le_plus_0_anb_b_a in eq.
            pose proof (lt_le_trans r_pos eq) as ltq.
            apply pos_neg2 in ltq.
            rewrite neg_neg in ltq.
            exact ltq.
        +   intros x_neg.
            exists (-x).
            split.
            *   exact (neg_pos2 _ x_neg).
            *   intro contr.
                rewrite plus_rinv in contr.
                destruct contr; contradiction.
    -   assert (0 < -a) as a_pos.
        {
            classic_contradiction leq.
            rewrite nlt_le in leq.
            destruct a_neg as [ltq neq].
            destruct a as [a a_cut].
            unfold le, neg, zero in *; cbn in *.
            unfold rat_to_real, rat_to_real_base in *.
            apply neq; clear neq.
            apply set_type_eq; cbn.
            apply predicate_ext; intros x; split.
            -   apply ltq.
            -   intros x_neg.
                unfold subset in leq.
                classic_contradiction contr.
                assert (∃ r, 0 < r ∧ ¬a (-0 + -r)) as r_ex.
                {
                    exists (-x).
                    split.
                    -   exact (neg_pos2 _ x_neg).
                    -   rewrite neg_neg, neg_zero, plus_lid.
                        exact contr.
                }
                specialize (leq 0 r_ex) as [C0 C1]; contradiction.
        }
        assert (a = --a) as eq.
        {
            destruct a as [a a_cut].
            destruct a_neg as [leq neq].
            unfold le, neg, zero in leq; cbn in leq.
            unfold rat_to_real_base in leq.
            unfold neg; cbn.
            apply set_type_eq; cbn.
            apply predicate_ext; intros x; split.
            -   intros ax.
                pose proof ax as x_neg.
                apply leq in x_neg.
                assert (∃ u, u < 0 ∧ ¬a u) as [u [u_neg nau]].
                {
                    classic_contradiction contr.
                    apply neq.
                    unfold zero; cbn.
                    apply set_type_eq; cbn.
                    apply antisym; try exact leq.
                    intros y y_lt.
                    rewrite not_ex in contr.
                    specialize (contr y).
                    rewrite not_and_impl, not_not in contr.
                    apply contr.
                    exact y_lt.
                }
                pose proof (rand (rand (rand a_cut)) _ ax) as [x' [ax' lt]].
                exists (x' + -x).
                split.
                +   apply lt_plus_0_anb_b_a.
                    exact lt.
                +   intros [r [r_pos eq]].
                    apply eq.
                    do 2 rewrite neg_plus.
                    rewrite (plus_comm (-x')).
                    rewrite neg_plus.
                    rewrite plus_lrinv.
                    rewrite neg_neg.
                    apply (land (rand (rand a_cut)) _ _ ax').
                    rewrite <- (plus_rid x') at 2.
                    apply lt_lplus.
                    apply pos_neg2.
                    exact r_pos.
            -   intros [r [r_pos n]].
                classic_contradiction ax.
                apply n.
                exists r.
                split; try exact r_pos.
                rewrite neg_plus.
                rewrite plus_rlinv, neg_neg.
                exact ax.
        }
        rewrite eq at 2.
        rewrite plus_comm.
        apply real_plus_linv_pos.
        exact a_pos.
Qed.
Global Instance real_plus_linv : PlusLinv real := {
    plus_linv := real_plus_linv_;
}.

Lemma real_le_lplus_ : ∀ a b c, a <= b → c + a <= c + b.
Proof.
    intros [a a_cut] [b b_cut] [c c_cut].
    unfold le, plus; cbn.
    intros ab x [r [s [cr [as_ eq]]]].
    exists r, s.
    apply ab in as_.
    repeat split; assumption.
Qed.
Global Instance real_le_lplus : OrderLplus real := {
    le_lplus := real_le_lplus_;
}.
(* begin hide *)
Close Scope real_scope.
(* end hide *)
