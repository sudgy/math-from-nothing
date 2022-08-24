Require Import init.

Require Export topology_base.
Require Export topology_order.
Require Export topology_order2.
Require Export topology_connected.
Require Export real.
Require Import order_minmax.

Definition real_order_topology := order_topology (U := real).

(* begin hide *)
Section RealOrderTopology.

Existing Instance real_order_topology.
(* end hide *)
Theorem real_open_interval : ∀ B, top_basis B → ∃ a b, B = open_interval a b.
Proof.
    intros B B_basis.
    destruct B_basis as [B_basis|[B_basis|B_basis]].
    -   exact B_basis.
    -   destruct B_basis as [a [b [B_eq b_max]]].
        specialize (b_max (b + 1)).
        rewrite <- nlt_le in b_max.
        exfalso; apply b_max.
        apply plus_one_pos.
    -   destruct B_basis as [a [b [B_eq a_min]]].
        specialize (a_min (a - 1)).
        apply le_plus_rrmove in a_min.
        rewrite neg_neg in a_min.
        rewrite <- nlt_le in a_min.
        exfalso; apply a_min.
        apply plus_one_pos.
Qed.

Theorem real_open_interval_eq : ∀ B, top_basis B ↔ ∃ a b, B = open_interval a b.
Proof.
    intros B.
    split.
    -   apply real_open_interval.
    -   intros B_basis.
        left.
        exact B_basis.
Qed.

Theorem real_connected : connected real.
Proof.
    apply complete_connected.
Qed.

(* begin hide *)
End RealOrderTopology.

Section LowerLimit.
(* end hide *)
Program Instance real_lower_limit_topology : TopologyBasis real := {
    top_basis S := ∃ a b, S = closed_open_interval a b
}.
Next Obligation.
    exists (closed_open_interval x (x + 1)).
    split.
    -   exists x, (x + 1).
        reflexivity.
    -   split.
        +   apply refl.
        +   apply plus_one_pos.
Qed.
Next Obligation.
    rename H into a1, H5 into b1, H0 into a2, H3 into b2.
    rename H1 into S1, H2 into S2.
    exists (closed_open_interval (max a1 a2) (min b1 b2)).
    split.
    2: split.
    -   exists (max a1 a2), (min b1 b2).
        reflexivity.
    -   split.
        +   unfold max; case_if.
            *   apply S2.
            *   apply S1.
        +   unfold min; case_if.
            *   apply S1.
            *   apply S2.
    -   intros y [y_ge y_lt].
        split; split.
        +   exact (trans (lmax _ _) y_ge).
        +   exact (lt_le_trans y_lt (lmin _ _)).
        +   exact (trans (rmax _ _) y_ge).
        +   exact (lt_le_trans y_lt (rmin _ _)).
Qed.

(* begin hide *)
End LowerLimit.

Section KTop.
(* end hide *)
Definition real_K x := ∃ n, x = /(from_nat (nat_suc n)).

Program Instance real_k_topology : TopologyBasis real := {
    top_basis S := ∃ a b,
        (S = open_interval a b) ∨
        (S = (open_interval a b - real_K)%set)
}.
Next Obligation.
    exists (open_interval (x - 1) (x + 1)).
    split.
    -   exists (x - 1), (x + 1).
        left.
        reflexivity.
    -   split.
        1: apply lt_plus_rrmove.
        all: apply plus_one_pos.
Qed.
Next Obligation.
    rename H into a1, H5 into b1, H0 into a2, H3 into b2.
    rename H6 into B1_open, H4 into B2_open.
    rename H1 into B1x, H2 into B2x.
    assert (open_interval a1 b1 x) as x_in1 by
        (destruct B1_open; subst; apply B1x).
    assert (open_interval a2 b2 x) as x_in2 by
        (destruct B2_open; subst; apply B2x).
    classic_case (real_K x) as [Kx|nKx].
    -   destruct B1_open as [B1_open|contr].
        2: {
            rewrite contr in B1x.
            destruct B1x; contradiction.
        }
        destruct B2_open as [B2_open|contr].
        2: {
            rewrite contr in B2x.
            destruct B2x; contradiction.
        }
        subst; clear B1x B2x.
        exists (open_interval (max a1 a2) (min b1 b2)).
        split.
        2: split.
        +   exists (max a1 a2), (min b1 b2).
            left.
            reflexivity.
        +   split.
            *   unfold max; case_if.
                --  apply x_in2.
                --  apply x_in1.
            *   unfold min; case_if.
                --  apply x_in1.
                --  apply x_in2.
        +   intros y [y_gt y_lt].
            split; split.
            *   exact (le_lt_trans (lmax _ _) y_gt).
            *   exact (lt_le_trans y_lt (lmin _ _)).
            *   exact (le_lt_trans (rmax _ _) y_gt).
            *   exact (lt_le_trans y_lt (rmin _ _)).
    -   exists (open_interval (max a1 a2) (min b1 b2) - real_K)%set.
        split.
        2: split.
        +   exists (max a1 a2), (min b1 b2).
            right.
            reflexivity.
        +   split.
            1: split.
            *   unfold max; case_if.
                --  apply x_in2.
                --  apply x_in1.
            *   unfold min; case_if.
                --  apply x_in1.
                --  apply x_in2.
            *   exact nKx.
        +   intros y [[y_gt y_lt] nKy].
            assert (open_interval a1 b1 y) as y_in1.
            {
                split.
                -   exact (le_lt_trans (lmax _ _) y_gt).
                -   exact (lt_le_trans y_lt (lmin _ _)).
            }
            assert (open_interval a2 b2 y) as y_in2.
            {
                split.
                -   exact (le_lt_trans (rmax _ _) y_gt).
                -   exact (lt_le_trans y_lt (rmin _ _)).
            }
            split.
            *   destruct B1_open; subst.
                2: split.
                1, 2: exact y_in1.
                exact nKy.
            *   destruct B2_open; subst.
                2: split.
                1, 2: exact y_in2.
                exact nKy.
Qed.

(* begin hide *)
End KTop.
(* end hide *)
Theorem real_lower_limit_finer : topology_strictly_finer
    (@basis_topology _ real_lower_limit_topology)
    (@basis_topology _ real_order_topology).
Proof.
    apply topology_not_finer_strict.
    -   apply topology_basis_finer.
        intros x B2 B2_basis B2x.
        apply real_open_interval in B2_basis.
        destruct B2_basis as [a [b B2_eq]].
        subst B2.
        exists (closed_open_interval x b).
        split.
        2: split.
        +   exists x, b.
            reflexivity.
        +   split.
            *   apply refl.
            *   apply B2x.
        +   intros y [y_gt y_lt].
            split.
            *   exact (lt_le_trans (land B2x) y_gt).
            *   exact y_lt.
    -   intros contr.
        rewrite topology_basis_finer in contr.
        pose (B2 := closed_open_interval 0 1).
        assert (@top_basis real real_lower_limit_topology B2) as B2_basis.
        {
            exists 0, 1.
            reflexivity.
        }
        assert (B2 0) as B20.
        {
            split.
            -   apply refl.
            -   exact one_pos.
        }
        specialize (contr 0 B2 B2_basis B20) as [B1 [B1_basis [B10 B1_sub]]].
        apply real_open_interval in B1_basis.
        destruct B1_basis as [a [b B1_eq]]; subst B1.
        unfold B2 in *.
        clear B2 B2_basis B20.
        destruct B10 as [a_neg b_pos].
        assert (a/2 < 0) as a2_neg.
        {
            apply half_neg.
            exact a_neg.
        }
        assert (open_interval a b (a/2)) as a2_in.
        {
            split.
            -   apply lt_mult_rcancel_pos with 2; try exact two_pos.
                rewrite mult_rlinv by apply two_pos.
                rewrite ldist; rewrite mult_rid.
                rewrite <- (plus_rid a) at 3.
                apply lt_lplus.
                exact a_neg.
            -   exact (trans a2_neg b_pos).
        }
        apply B1_sub in a2_in.
        destruct a2_in as [a2_pos].
        destruct (lt_le_trans a2_neg a2_pos); contradiction.
Qed.

Theorem real_k_finer : topology_strictly_finer
    (@basis_topology _ real_k_topology)
    (@basis_topology _ real_order_topology).
Proof.
    apply topology_not_finer_strict.
    -   apply topology_basis_finer.
        intros x B2 B2_basis B2x.
        exists B2.
        split.
        2: split.
        +   apply real_open_interval in B2_basis.
            destruct B2_basis as [a [b B2_eq]]; subst B2.
            exists a, b.
            left.
            reflexivity.
        +   exact B2x.
        +   apply refl.
    -   intros contr.
        rewrite topology_basis_finer in contr.
        pose (B2 := (open_interval (-(1)) 1 - real_K)%set).
        assert (@top_basis real real_k_topology B2) as B2_basis.
        {
            unfold top_basis; cbn.
            exists (-(1)), 1.
            right.
            reflexivity.
        }
        assert (B2 0) as B20.
        {
            split.
            -   split.
                1: apply pos_neg2.
                all: exact one_pos.
            -   unfold real_K.
                rewrite not_ex.
                intros n.
                apply real_n_div_pos.
        }
        specialize (contr 0 B2 B2_basis B20) as [B1 [B1_basis [B1x B1_sub]]].
        apply real_open_interval in B1_basis.
        destruct B1_basis as [a [b B1_eq]]; subst B1.
        unfold B2 in B1_sub; clear B2 B2_basis B20.
        destruct B1x as [a_neg b_pos].
        pose proof (archimedean2 b b_pos) as [n n_ltq].
        assert (open_interval a b (/from_nat (nat_suc n))) as n_in.
        {
            split.
            -   apply (trans a_neg).
                apply real_n_div_pos.
            -   exact n_ltq.
        }
        apply B1_sub in n_in.
        destruct n_in as [n_in1 n_in2].
        apply n_in2.
        exists n.
        reflexivity.
Qed.

Theorem real_lower_limit_k_incomparable : ¬topology_comparable
    (@basis_topology _ real_lower_limit_topology)
    (@basis_topology _ real_k_topology).
Proof.
    intros [finer|finer].
    -   rewrite topology_basis_finer in finer.
        pose (B2 := (open_interval (-(1)) 1 - real_K)%set).
        assert (@top_basis real real_k_topology B2) as B2_basis.
        {
            unfold top_basis; cbn.
            exists (-(1)), 1.
            right.
            reflexivity.
        }
        assert (B2 0) as B20.
        {
            split.
            -   split.
                1: apply pos_neg2.
                all: exact one_pos.
            -   unfold real_K.
                rewrite not_ex.
                intros n.
                apply real_n_div_pos.
        }
        specialize (finer 0 B2 B2_basis B20) as [B1 [B1_basis [B1x B1_sub]]].
        destruct B1_basis as [a [b B1_eq]]; subst B1.
        unfold B2 in B1_sub; clear B2 B2_basis B20.
        destruct B1x as [a_neg b_pos].
        pose proof (archimedean2 b b_pos) as [n n_ltq].
        assert (closed_open_interval a b (/from_nat (nat_suc n))) as n_in.
        {
            split.
            -   apply (trans a_neg).
                apply real_n_div_pos.
            -   exact n_ltq.
        }
        apply B1_sub in n_in.
        destruct n_in as [n_in1 n_in2].
        apply n_in2.
        exists n.
        reflexivity.
    -   rewrite topology_basis_finer in finer.
        pose (B2 := closed_open_interval 0 1).
        assert (@top_basis real real_lower_limit_topology B2) as B2_basis.
        {
            exists 0, 1.
            reflexivity.
        }
        assert (B2 0) as B20.
        {
            split.
            -   apply refl.
            -   exact one_pos.
        }
        specialize (finer 0 B2 B2_basis B20) as [B1 [B1_basis [B10 B1_sub]]].
        destruct B1_basis as [a [b B1_eq]].
        assert (open_interval a b 0) as B10'.
        {
            destruct B1_eq; subst B1.
            -   exact B10.
            -   apply B10.
        }
        unfold B2 in *.
        clear B2 B2_basis B20 B10.
        destruct B10' as [a_neg b_pos].
        classic_case (real_K (a/2)) as [Ka|nKa].
        +   destruct Ka as [n n_eq].
            assert (0 < a) as a_pos.
            {
                apply lt_mult_rcancel_pos with (/2).
                1: apply div_pos; exact two_pos.
                rewrite mult_lanni.
                rewrite n_eq.
                apply real_n_div_pos.
            }
            destruct (trans a_neg a_pos); contradiction.
        +   assert (a/2 < 0) as a2_neg.
            {
                apply half_neg.
                exact a_neg.
            }
            assert (open_interval a b (a/2)) as a2_in'.
            {
                split.
                -   apply lt_mult_rcancel_pos with 2; try exact two_pos.
                    rewrite mult_rlinv by apply two_pos.
                    rewrite ldist; rewrite mult_rid.
                    rewrite <- (plus_rid a) at 3.
                    apply lt_lplus.
                    exact a_neg.
                -   exact (trans a2_neg b_pos).
            }
            assert (B1 (a/2)) as a2_in.
            {
                destruct B1_eq; subst B1.
                2: split.
                1, 2: exact a2_in'.
                exact nKa.
            }
            apply B1_sub in a2_in.
            destruct a2_in as [a2_pos].
            destruct (lt_le_trans a2_neg a2_pos); contradiction.
Qed.
