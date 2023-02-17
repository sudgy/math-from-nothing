Require Import init.

Require Export topology_base.
Require Export topology_basis.

#[universes(template)]
Class TopologySubbasis U := {
    top_subbasis : (U → Prop) → Prop;
    top_subbasis_union : ⋃ top_subbasis = all
}.

(* begin hide *)
Open Scope card_scope.
(* end hide *)
Global Program Instance subbasis_topology {U} `{TopologySubbasis U}
    : TopologyBasis U :=
{
    top_basis S := ∃ SS, SS ⊆ top_subbasis ∧ finite (|set_type SS|) ∧ S = ⋂ SS
}.
Next Obligation.
    assert (all x) as x_in by exact true.
    rewrite <- top_subbasis_union in x_in.
    destruct x_in as [B [B_sub Bx]].
    exists B.
    split; try exact Bx.
    exists ❴B❵.
    split.
    2: split.
    -   intros S SB.
        rewrite <- SB.
        exact B_sub.
    -   apply singleton_finite.
    -   symmetry; apply inter_singleton.
Qed.
Next Obligation.
    rename H0 into SS1, H1 into SS2, H8 into SS1_fin, H5 into SS2_fin.
    rename H7 into SS1_sub, H4 into SS2_sub.
    rename H2 into SS1_x, H3 into SS2_x.
    pose (SS := SS1 ∪ SS2).
    exists (⋂ SS).
    split.
    2: split.
    -   exists SS.
        split.
        2: split.
        +   intros S [SS1_S|SS2_S].
            *   apply SS1_sub.
                exact SS1_S.
            *   apply SS2_sub.
                exact SS2_S.
        +   unfold SS.
            apply (le_lt_trans (card_plus_union _ _)).
            apply fin_nat_ex in SS1_fin as [m m_eq].
            apply fin_nat_ex in SS2_fin as [n n_eq].
            rewrite <- m_eq, <- n_eq.
            rewrite nat_to_card_plus.
            apply nat_is_finite.
        +   reflexivity.
    -   intros S [SS1_S|SS2_S].
        +   apply SS1_x.
            exact SS1_S.
        +   apply SS2_x.
            exact SS2_S.
    -   unfold SS.
        intros S S_in.
        split.
        +   intros A SS1_A.
            exact (S_in A (make_lor SS1_A)).
        +   intros A SS2_A.
            exact (S_in A (make_ror SS2_A)).
Qed.

Theorem subbasis_basis {U} `{TopologySubbasis U} :
    ∀ S, top_subbasis S → top_basis S.
Proof.
    intros S S_sub.
    exists ❴S❵.
    split; [>|split].
    -   intros T T_eq.
        rewrite singleton_eq in T_eq.
        subst T.
        exact S_sub.
    -   apply singleton_finite.
    -   rewrite inter_singleton.
        reflexivity.
Qed.

Theorem subbasis_open {U} `{TopologySubbasis U} : ∀ S, top_subbasis S → open S.
Proof.
    intros S S_sub.
    apply basis_open.
    apply subbasis_basis.
    exact S_sub.
Qed.

Close Scope card_scope.
(* end hide *)
