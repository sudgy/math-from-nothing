Require Import init.

Require Export topology_basis.
Require Export topology_axioms.

(** This file contains the definition of the order topology and a few basic
 facts (like "closed intervals are closed").  Anything interesting about the
 order topology is in topology_order.
 *)

(* begin hide *)
Section OrderTopology.

Local Open Scope set_scope.

Context {U} `{
    Order U,
    Reflexive U le,
    Connex U le,
    Antisymmetric U le,
    Transitive U le,
    NotTrivial U
}.
(* end hide *)
Program Instance order_topology : TopologyBasis U := {
    top_basis S :=
        (∃ a b, S = open_interval a b) ∨
        (∃ a b, S = open_closed_interval a b ∧ ∀ x, x ≤ b) ∨
        (∃ a b, S = closed_open_interval a b ∧ ∀ x, a ≤ x)
}.
Next Obligation.
    specialize (not_trivial2 x) as [y neq].
    classic_case (∀ a, a ≤ x) as [x_max|x_nmax].
    2: classic_case (∀ b, x ≤ b) as [x_min|x_nmin].
    -   exists (open_closed_interval y x).
        split.
        +   right; left.
            exists y, x.
            split.
            *   reflexivity.
            *   exact x_max.
        +   split.
            *   split.
                --  apply x_max.
                --  rewrite neq_sym; exact neq.
            *   apply refl.
    -   exists (closed_open_interval x y).
        split.
        +   right; right.
            exists x, y.
            split.
            *   reflexivity.
            *   exact x_min.
        +   split.
            *   apply refl.
            *   split.
                --  apply x_min.
                --  exact neq.
    -   clear y neq.
        rewrite not_all in x_nmax, x_nmin.
        destruct x_nmax as [b b_ltq].
        destruct x_nmin as [a a_ltq].
        rewrite nle_lt in b_ltq, a_ltq.
        exists (open_interval a b).
        split.
        +   left.
            exists a, b.
            reflexivity.
        +   split; assumption.
Qed.
Next Obligation.
    rename H7 into x1.
    rename H8 into x2.
    destruct H5 as [ [a [b eq1]] |[ [a [b [eq1 b_max]]] | [a [b [eq1 a_min]]] ]].
    all: destruct H6 as [ [c [d eq2]] |[ [c [d [eq2 d_max]]] | [c [d [eq2 c_min]]] ]].
    all: subst.
    -   classic_case (a ≤ c) as [ac|ca].
        all: classic_case (b ≤ d) as [bd|db].
        +   exists (open_interval c b).
            split.
            2: split.
            *   left.
                exists c, b.
                reflexivity.
            *   split.
                --  apply x2.
                --  apply x1.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply (le_lt_trans ac).
                        apply y_in.
                    ++  apply y_in.
                --  split.
                    ++  apply y_in.
                    ++  apply (lt_le_trans2 bd).
                        apply y_in.
        +   rewrite nle_lt in db.
            exists (open_interval c d).
            split.
            2: split.
            *   left.
                exists c, d.
                reflexivity.
            *   split.
                --  apply x2.
                --  apply x2.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply (le_lt_trans ac).
                        apply y_in.
                    ++  apply (trans2 db).
                        apply y_in.
                --  split.
                    ++  apply y_in.
                    ++  apply y_in.
        +   rewrite nle_lt in ca.
            exists (open_interval a b).
            split.
            2: split.
            *   left.
                exists a, b.
                reflexivity.
            *   split.
                --  apply x1.
                --  apply x1.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply y_in.
                    ++  apply y_in.
                --  split.
                    ++  apply (trans ca).
                        apply y_in.
                    ++  apply (lt_le_trans2 bd).
                        apply y_in.
        +   rewrite nle_lt in ca, db.
            exists (open_interval a d).
            split.
            2: split.
            *   left.
                exists a, d.
                reflexivity.
            *   split.
                --  apply x1.
                --  apply x2.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply y_in.
                    ++  apply (trans2 db).
                        apply y_in.
                --  split.
                    ++  apply (trans ca).
                        apply y_in.
                    ++  apply y_in.
    -   classic_case (a ≤ c) as [ac|ca].
        +   exists (open_interval c b).
            split.
            2: split.
            *   left.
                exists c, b.
                reflexivity.
            *   split.
                --  apply x2.
                --  apply x1.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply (le_lt_trans ac).
                        apply y_in.
                    ++  apply y_in.
                --  split.
                    ++  apply y_in.
                    ++  apply d_max.
        +   rewrite nle_lt in ca.
            exists (open_interval a b).
            split.
            2: split.
            *   left.
                exists a, b.
                reflexivity.
            *   exact x1.
            *   intros y y_in.
                split.
                --  exact y_in.
                --  split.
                    ++  apply (trans ca).
                        apply y_in.
                    ++  apply d_max.
    -   classic_case (b ≤ d) as [bd|db].
        +   exists (open_interval a b).
            split.
            2: split.
            *   left.
                exists a, b.
                reflexivity.
            *   exact x1.
            *   intros y y_in.
                split.
                --  exact y_in.
                --  split.
                    ++  apply c_min.
                    ++  apply (lt_le_trans2 bd).
                        apply y_in.
        +   rewrite nle_lt in db.
            exists (open_interval a d).
            split.
            2: split.
            *   left.
                exists a, d.
                reflexivity.
            *   split.
                --  apply x1.
                --  apply x2.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply y_in.
                    ++  apply (trans2 db).
                        apply y_in.
                --  split.
                    ++  apply c_min.
                    ++  apply y_in.
    -   classic_case (a ≤ c) as [ac|ca].
        +   exists (open_interval c d).
            split.
            2: split.
            *   left.
                exists c, d.
                reflexivity.
            *   exact x2.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply (le_lt_trans ac).
                        apply y_in.
                    ++  apply b_max.
                --  apply y_in.
        +   rewrite nle_lt in ca.
            exists (open_interval a d).
            split.
            2: split.
            *   left.
                exists a, d.
                reflexivity.
            *   split.
                --  apply x1.
                --  apply x2.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply y_in.
                    ++  apply b_max.
                --  split.
                    ++  apply (trans ca).
                        apply y_in.
                    ++  apply y_in.
    -   classic_case (a ≤ c) as [ac|ca].
        +   exists (open_closed_interval c d).
            split.
            2: split.
            *   right; left.
                exists c, d.
                split.
                --  reflexivity.
                --  apply d_max.
            *   exact x2.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply (le_lt_trans ac).
                        apply y_in.
                    ++  apply b_max.
                --  exact y_in.
        +   rewrite nle_lt in ca.
            exists (open_closed_interval a d).
            split.
            2: split.
            *   right; left.
                exists a, d.
                split.
                --  reflexivity.
                --  apply d_max.
            *   split.
                --  apply x1.
                --  apply x2.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply y_in.
                    ++  apply b_max.
                --  split.
                    ++  apply (trans ca).
                        apply y_in.
                    ++  apply y_in.
    -   exists (open_interval a d).
        split.
        2: split.
        +   left.
            exists a, d.
            reflexivity.
        +   split.
            *   apply x1.
            *   apply x2.
        +   intros y y_in.
            split.
            *   split.
                --  apply y_in.
                --  apply b_max.
            *   split.
                --  apply c_min.
                --  apply y_in.
    -   classic_case (b ≤ d) as [bd|db].
        +   exists (open_interval c b).
            split.
            2: split.
            *   left.
                exists c, b.
                reflexivity.
            *   split.
                --  apply x2.
                --  apply x1.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply a_min.
                    ++  apply y_in.
                --  split.
                    ++  apply y_in.
                    ++  apply (lt_le_trans2 bd).
                        apply y_in.
        +   rewrite nle_lt in db.
            exists (open_interval c d).
            split.
            2: split.
            *   left.
                exists c, d.
                reflexivity.
            *   exact x2.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply a_min.
                    ++  apply (trans2 db).
                        apply y_in.
                --  exact y_in.
    -   exists (open_interval c b).
        split.
        2: split.
        +   left.
            exists c, b.
            reflexivity.
        +   split.
            *   apply x2.
            *   apply x1.
        +   intros y y_in.
            split.
            *   split.
                --  apply a_min.
                --  apply y_in.
            *   split.
                --  apply y_in.
                --  apply d_max.
    -   classic_case (b ≤ d) as [bd|db].
        +   exists (closed_open_interval a b).
            split.
            2: split.
            *   right; right.
                exists a, b.
                split.
                --  reflexivity.
                --  apply a_min.
            *   exact x1.
            *   intros y y_in.
                split.
                --  exact y_in.
                --  split.
                    ++  apply c_min.
                    ++  apply (lt_le_trans2 bd).
                        apply y_in.
        +   rewrite nle_lt in db.
            exists (closed_open_interval a d).
            split.
            2: split.
            *   right; right.
                exists a, d.
                split.
                --  reflexivity.
                --  apply a_min.
            *   split.
                --  apply x1.
                --  apply x2.
            *   intros y y_in.
                split.
                --  split.
                    ++  apply y_in.
                    ++  apply (trans2 db).
                        apply y_in.
                --  split.
                    ++  apply c_min.
                    ++  apply y_in.
Qed.

Theorem open_interval_open : ∀ a b, open (open_interval a b).
Proof.
    intros a b x x_in.
    exists (open_interval a b).
    split.
    2: split.
    -   left.
        exists a, b.
        reflexivity.
    -   exact x_in.
    -   apply refl.
Qed.

Theorem open_inf_interval_open : ∀ a, open (open_inf_interval a).
Proof.
    intros a.
    classic_case (∃ b, ∀ x, x ≤ b) as [b_max|no_max].
    -   destruct b_max as [b b_max].
        intros x x_in.
        exists (open_closed_interval a b).
        split.
        2: split.
        +   right; left.
            exists a, b.
            split.
            *   reflexivity.
            *   exact b_max.
        +   split.
            *   apply x_in.
            *   apply b_max.
        +   intros y y_in.
            apply y_in.
    -   rewrite not_ex in no_max.
        pose (SS S := ∃ b, S = open_interval a b).
        assert (open_inf_interval a = ⋃ SS) as eq.
        {
            apply predicate_ext.
            intros x.
            split.
            -   intros ax.
                specialize (no_max x).
                rewrite not_all in no_max.
                destruct no_max as [b b_gt].
                rewrite nle_lt in b_gt.
                exists (open_interval a b).
                split.
                +   exists b.
                    reflexivity.
                +   split.
                    *   exact ax.
                    *   exact b_gt.
            -   intros [S [[b S_eq] Sx]].
                rewrite S_eq in Sx.
                apply Sx.
        }
        rewrite eq.
        apply union_open.
        intros S [b S_eq].
        rewrite S_eq.
        apply open_interval_open.
Qed.

Theorem inf_open_interval_open : ∀ a, open (inf_open_interval a).
Proof.
    intros b.
    classic_case (∃ a, ∀ x, a ≤ x) as [a_min|no_min].
    -   destruct a_min as [a a_min].
        intros x x_in.
        exists (closed_open_interval a b).
        split.
        2: split.
        +   right; right.
            exists a, b.
            split.
            *   reflexivity.
            *   exact a_min.
        +   split.
            *   apply a_min.
            *   apply x_in.
        +   intros y y_in.
            apply y_in.
    -   rewrite not_ex in no_min.
        pose (SS S := ∃ a, S = open_interval a b).
        assert (inf_open_interval b = ⋃ SS) as eq.
        {
            apply predicate_ext.
            intros x.
            split.
            -   intros bx.
                specialize (no_min x).
                rewrite not_all in no_min.
                destruct no_min as [a a_lt].
                rewrite nle_lt in a_lt.
                exists (open_interval a b).
                split.
                +   exists a.
                    reflexivity.
                +   split.
                    *   exact a_lt.
                    *   exact bx.
            -   intros [S [[a S_eq] Sx]].
                rewrite S_eq in Sx.
                apply Sx.
        }
        rewrite eq.
        apply union_open.
        intros S [a S_eq].
        rewrite S_eq.
        apply open_interval_open.
Qed.

Theorem closed_interval_closed : ∀ a b, closed (closed_interval a b).
Proof.
    intros a b.
    unfold closed.
    assert (complement (closed_interval a b) =
        inf_open_interval a ∪ open_inf_interval b) as eq.
    {
        unfold complement, closed_interval, inf_open_interval,
            open_inf_interval, union.
        apply predicate_ext; intros x.
        rewrite not_and.
        do 2 rewrite nle_lt.
        reflexivity.
    }
    rewrite eq.
    apply union_open2.
    -   apply inf_open_interval_open.
    -   apply open_inf_interval_open.
Qed.

Theorem closed_inf_interval_closed : ∀ a, closed (closed_inf_interval a).
Proof.
    intros a.
    unfold closed.
    assert (complement (closed_inf_interval a) = inf_open_interval a) as eq.
    {
        unfold complement, closed_inf_interval, inf_open_interval.
        apply predicate_ext; intros x.
        rewrite nle_lt.
        reflexivity.
    }
    rewrite eq.
    apply inf_open_interval_open.
Qed.

Theorem inf_closed_interval_closed : ∀ a, closed (inf_closed_interval a).
Proof.
    intros a.
    unfold closed.
    assert (complement (inf_closed_interval a) = open_inf_interval a) as eq.
    {
        unfold complement, inf_closed_interval, open_inf_interval.
        apply predicate_ext; intros x.
        rewrite nle_lt.
        reflexivity.
    }
    rewrite eq.
    apply open_inf_interval_open.
Qed.

(* begin hide *)
Lemma order_hausdorff_wlog : ∀ a b, a < b →
    ∃ S1 S2, open S1 ∧ open S2 ∧ S1 a ∧ S2 b ∧ disjoint S1 S2.
Proof.
    intros a b ab.
    classic_case (∃ c, a < c ∧ c < b) as [between|near].
    -   destruct between as [c [ac cb]].
        exists (inf_open_interval c), (open_inf_interval c).
        split. 2: split. 3: split. 4: split.
        +   apply inf_open_interval_open.
        +   apply open_inf_interval_open.
        +   exact ac.
        +   exact cb.
        +   apply not_ex_empty.
            intros x [cx xc].
            unfold inf_open_interval in cx.
            unfold open_inf_interval in cx.
            pose proof (trans cx xc) as contr.
            destruct contr; contradiction.
    -   rewrite not_ex in near.
        exists (inf_open_interval b), (open_inf_interval a).
        split. 2: split. 3: split. 4: split.
        +   apply inf_open_interval_open.
        +   apply open_inf_interval_open.
        +   exact ab.
        +   exact ab.
        +   apply not_ex_empty.
            intros x [bx ax].
            unfold inf_open_interval in bx.
            unfold open_inf_interval in ax.
            specialize (near x).
            rewrite not_and_impl in near.
            specialize (near ax).
            contradiction.
Qed.
(* end hide *)
Program Instance order_hausdorff : HausdorffSpace U.
Next Obligation.
    rename H5 into neq.
    destruct (trichotomy x1 x2) as [[ltq|eq]|ltq].
    -   exact (order_hausdorff_wlog x1 x2 ltq).
    -   contradiction.
    -   pose proof (order_hausdorff_wlog x2 x1 ltq) as [S1 [S2 HH]].
        exists S2, S1.
        unfold disjoint.
        rewrite inter_comm.
        repeat split; apply HH.
Qed.
(* begin hide *)
End OrderTopology.
(* end hide *)
