Require Import init.

Require Export topology_order_base.
Require Import topology_subspace.
Require Import topology_connected.
Require Export relation.
Require Import order_minmax.

Unset Keyed Unification.

(* begin hide *)
Section OrderTopology.

Context {U} `{
    Order U,
    Reflexive U le,
    Connex U le,
    Antisymmetric U le,
    Transitive U le,
    NotTrivial U
}.
(* end hide *)
Definition top_convex (S : U → Prop) :=
    ∀ a b, S a → S b → closed_interval a b ⊆ S.

Theorem open_interval_convex : ∀ a b, top_convex (open_interval a b).
Proof.
    intros a b c d [ac cb] [ad db] x [cx dx].
    split.
    -   exact (lt_le_trans ac cx).
    -   exact (le_lt_trans dx db).
Qed.
Theorem open_closed_interval_convex:∀ a b,top_convex (open_closed_interval a b).
Proof.
    intros a b c d [ac cb] [ad db] x [cx dx].
    split.
    -   exact (lt_le_trans ac cx).
    -   exact (trans dx db).
Qed.
Theorem closed_open_interval_convex:∀ a b,top_convex (closed_open_interval a b).
Proof.
    intros a b c d [ac cb] [ad db] x [cx dx].
    split.
    -   exact (trans ac cx).
    -   exact (le_lt_trans dx db).
Qed.
Theorem closed_interval_convex : ∀ a b, top_convex (closed_interval a b).
Proof.
    intros a b c d [ac cb] [ad db] x [cx dx].
    split.
    -   exact (trans ac cx).
    -   exact (trans dx db).
Qed.
Theorem open_inf_interval_convex : ∀ a, top_convex (open_inf_interval a).
Proof.
    intros a b c ab ac x [bx xc].
    exact (lt_le_trans ab bx).
Qed.
Theorem closed_inf_interval_convex : ∀ a, top_convex (closed_inf_interval a).
Proof.
    intros a b c ab ac x [bx xc].
    exact (trans ab bx).
Qed.
Theorem inf_open_interval_convex : ∀ a, top_convex (inf_open_interval a).
Proof.
    intros a b c ab ac x [bx xc].
    exact (le_lt_trans xc ac).
Qed.
Theorem inf_closed_interval_convex : ∀ a, top_convex (inf_closed_interval a).
Proof.
    intros a b c ab ac x [bx xc].
    exact (trans xc ac).
Qed.

(* begin hide *)
Context `{SupremumComplete U le, Dense U (strict le)}.

Let order_top := order_topology.
Existing Instance order_top.
Existing Instance subspace_topology.

Lemma convex_connected_wlog : ∀ S, top_convex S →
    ∀ (A B : set_type S → Prop) a b, A a → B b → a < b → ¬(separation A B).
Proof.
    intros S S_convex A B a b Aa Bb ab.
    intros [A_empty [B_empty [A_open [B_open [AB_dis AB_all]]]]].
    pose (A' x := A x ∧ x < b).
    pose (A'' := from_set_type A').
    assert (∃ x, A'' x) as A'_ex.
    {
        exists [a|].
        split with [|a].
        rewrite set_type_simpl.
        split; assumption.
    }
    assert (has_upper_bound le A'') as A'_upper.
    {
        exists [b|].
        intros x' [Sx' [Ax' x_lt]].
        apply x_lt.
    }
    pose proof (sup_complete A'' A'_ex A'_upper) as [α [α_upper α_least]].
    assert (A = 𝐂 B) as A_compl.
    {
        apply antisym.
        -   intros x Ax Bx.
            assert ((A ∩ B) x) as x_in by (split; assumption).
            unfold disjoint in AB_dis.
            rewrite AB_dis in x_in.
            exact x_in.
        -   intros x nBx.
            assert (all x) as x_in by exact true.
            rewrite <- AB_all in x_in.
            destruct x_in as [Ax|Bx].
            +   exact Ax.
            +   contradiction.
    }
    assert (B = 𝐂 A) as B_compl.
    {
        rewrite A_compl.
        rewrite compl_compl.
        reflexivity.
    }
    assert (closed A) as A_closed.
    {
        unfold closed.
        rewrite <- B_compl.
        exact B_open.
    }
    assert (closed B) as B_closed.
    {
        unfold closed.
        rewrite <- A_compl.
        exact A_open.
    }
    assert (S α) as Sα.
    {
        apply (S_convex [a|] [b|] [|a] [|b]).
        split.
        -   apply α_upper.
            split with [|a].
            rewrite set_type_simpl.
            split; assumption.
        -   apply α_least.
            intros x [x' [x_eq Ax]].
            apply Ax.
    }
    assert (A [α|Sα]) as Aα.
    {
        classic_case (A [α|Sα]) as [A_in|A_nin]; try exact A_in.
        classic_case (a = [α|Sα]) as [a_eq|a_neq].
        {
            rewrite <- a_eq.
            exact Aa.
        }
        assert ([a|] < α) as a_lt.
        {
            split.
            -   apply α_upper.
                split with [|a].
                rewrite set_type_simpl.
                split; assumption.
            -   intro; subst.
                apply a_neq.
                apply set_type_eq; cbn.
                reflexivity.
        }
        rewrite closed_limit_points in A_closed.
        apply A_closed.
        intros SC SC_open SCα.
        apply empty_neq.
        destruct SC_open as [UC [UC_open C_eq]].
        rewrite C_eq in SCα.
        specialize (UC_open _ SCα) as [BC [BC_basis [BCα BC_sub]]].
        assert (∀ c d, open_closed_interval c d α → open_interval c d ⊆ UC →
            ∃ x, ((A - ❴[α | Sα]❵)%set ∩ SC) x) as wlog.
        {
            clear BCα BC_sub.
            intros c d BCα BC_sub.
            pose (m := max c [a|]).
            assert (S m) as Sm.
            {
                apply (S_convex [a|] α [|a] Sα).
                split.
                -   apply rmax.
                -   unfold m, max; case_if.
                    +   apply a_lt.
                    +   apply BCα.
            }
            classic_case (∃ n, m < [n|] ∧ [n|] < α ∧ A n) as [n_ex|m_max'].
            +   destruct n_ex as [n [mn [nα An]]].
                exists n.
                repeat split.
                *   exact An.
                *   rewrite singleton_eq; intro; subst n.
                    destruct nα; contradiction.
                *   rewrite C_eq.
                    unfold to_set_type.
                    apply BC_sub.
                    split.
                    --  apply (le_lt_trans (lmax c [a|])).
                        exact mn.
                    --  apply (lt_le_trans nα).
                        apply BCα.
            +   rewrite not_ex in m_max'.
                assert (is_upper_bound le A'' m) as m_max.
                {
                    intros x A''x.
                    pose proof (α_upper x A''x) as x_le.
                    destruct A''x as [Sx [Ax x_lt]].
                    specialize (m_max' [x|Sx]).
                    do 2 rewrite not_and in m_max'.
                    destruct m_max' as [leq|[leq|nAx]].
                    -   rewrite nlt_le in leq.
                        exact leq.
                    -   rewrite nlt_le in leq.
                        pose proof (antisym leq x_le).
                        subst α.
                        cbn in *.
                        rewrite (proof_irrelevance Sx Sα) in Ax.
                        contradiction.
                    -   contradiction.
                }
                specialize (α_least _ m_max).
                assert (m < α) as ltq.
                {
                    unfold m, max; case_if.
                    -   exact a_lt.
                    -   apply BCα.
                }
                rewrite <- nle_lt in ltq.
                contradiction.
        }
        destruct BC_basis as [BC_basis|[BC_basis|BC_basis]].
        -   destruct BC_basis as [c [d BC_eq]].
            subst BC.
            assert (open_closed_interval c d α) as BCα2.
            {
                split; apply BCα.
            }
            exact (wlog c d BCα2 BC_sub).
        -   destruct BC_basis as [c [d [BC_eq d_max]]].
            subst BC.
            assert (open_interval c d ⊆ UC) as BC_sub2.
            {
                apply (trans2 BC_sub).
                intros x x_in.
                split; apply x_in.
            }
            exact (wlog c d BCα BC_sub2).
        -   destruct BC_basis as [c [d [BC_eq c_min]]].
            subst BC.
            assert (open_closed_interval c d α) as BCα2.
            {
                split.
                -   split.
                    +   apply BCα.
                    +   intro; subst c.
                        specialize (c_min [a|]).
                        destruct (le_lt_trans c_min a_lt); contradiction.
                -   apply BCα.
            }
            assert (open_interval c d ⊆ UC) as BC_sub2.
            {
                apply (trans2 BC_sub).
                intros x x_in.
                split; apply x_in.
            }
            exact (wlog c d BCα2 BC_sub2).
    }
    assert (B [α|Sα]) as Bα.
    {
        classic_case (B [α|Sα]) as [B_in|B_nin]; try exact B_in.
        classic_case (b = [α|Sα]) as [b_eq|b_neq].
        {
            rewrite <- b_eq.
            exact Bb.
        }
        assert (α < [b|]) as a_lt.
        {
            split.
            -   apply α_least.
                intros x [Sx [Ax x_lt]].
                apply x_lt.
            -   intro; subst.
                apply b_neq.
                apply set_type_eq; cbn.
                reflexivity.
        }
        assert (∀ x, α < x → x < [b|] → S x) as in_S.
        {
            intros x x_lt1 x_lt2.
            apply (S_convex α [b|] Sα [|b]).
            split.
            -   apply x_lt1.
            -   apply x_lt2.
        }
        assert (∀ x (x_lt1 : α < x) (x_lt2 : x < [b|]),
            B [x|in_S x x_lt1 x_lt2]) as in_B.
        {
            intros x x_lt1 x_lt2.
            pose proof (in_S x x_lt1 x_lt2) as Sx.
            rewrite (proof_irrelevance _ Sx).
            classic_contradiction contr.
            assert (all [x|Sx]) as x_in by exact true.
            rewrite <- AB_all in x_in.
            destruct x_in as [Ax|Bx]; try contradiction.
            assert (A'' x) as Ax'.
            {
                split with Sx.
                split.
                -   exact Ax.
                -   split.
                    +   apply x_lt2.
                    +   intros contr2.
                        pose proof x_lt2 as x_lt2'.
                        rewrite <- contr2 in x_lt2'.
                        cbn in x_lt2'.
                        destruct x_lt2'; contradiction.
            }
            specialize (α_upper _ Ax').
            destruct (lt_le_trans x_lt1 α_upper); contradiction.
        }
        rewrite closed_limit_points in B_closed.
        apply B_closed.
        intros SC SC_open SCα.
        apply empty_neq.
        destruct SC_open as [UC [UC_open C_eq]].
        rewrite C_eq in SCα.
        specialize (UC_open _ SCα) as [BC [BC_basis [BCα BC_sub]]].
        assert (∀ c d, closed_open_interval c d α → open_interval c d ⊆ UC →
            ∃ x, ((B - ❴[α | Sα]❵)%set ∩ SC) x) as wlog.
        {
            clear BCα BC_sub.
            intros c d BCα BC_sub.
            pose (m := min [b|] d).
            assert (α < m) as m_gt.
            {
                unfold m, min; case_if.
                -   exact a_lt.
                -   apply BCα.
            }
            pose proof (dense _ _ m_gt) as [n [αn nm]].
            pose proof (lt_le_trans nm (lmin _ _)) as nb.
            exists [n|in_S n αn nb].
            repeat split.
            +   apply in_B.
            +   rewrite singleton_eq; intro contr.
                inversion contr.
                subst.
                destruct αn; contradiction.
            +   rewrite C_eq.
                apply BC_sub; cbn.
                split.
                *   apply (le_lt_trans (land BCα)).
                    exact αn.
                *   apply (lt_le_trans nm).
                    apply rmin.
        }
        destruct BC_basis as [BC_basis|[BC_basis|BC_basis]].
        -   destruct BC_basis as [c [d BC_eq]].
            subst BC.
            assert (closed_open_interval c d α) as BCα2.
            {
                split; apply BCα.
            }
            exact (wlog c d BCα2 BC_sub).
        -   destruct BC_basis as [c [d [BC_eq d_max]]].
            subst BC.
            assert (closed_open_interval c d α) as BCα2.
            {
                split.
                -   apply BCα.
                -   split.
                    +   apply BCα.
                    +   intro contr; subst d.
                        specialize (d_max [b|]).
                        destruct (lt_le_trans a_lt d_max); contradiction.
            }
            assert (open_interval c d ⊆ UC) as BC_sub2.
            {
                apply (trans2 BC_sub).
                intros x x_in.
                split; apply x_in.
            }
            exact (wlog c d BCα2 BC_sub2).
        -   destruct BC_basis as [c [d [BC_eq c_min]]].
            subst BC.
            assert (open_interval c d ⊆ UC) as BC_sub2.
            {
                apply (trans2 BC_sub).
                intros x x_in.
                split; apply x_in.
            }
            exact (wlog c d BCα BC_sub2).
    }
    unfold disjoint in AB_dis.
    assert ((A ∩ B) [α | Sα]) as AB by (split; assumption).
    rewrite AB_dis in AB.
    exact AB.
Qed.
(* end hide *)
Theorem convex_connected : ∀ S, top_convex S → connected (set_type S).
Proof.
    intros S S_convex A B AB_sep.
    pose proof (land AB_sep) as A_ex.
    pose proof (land (rand AB_sep)) as B_ex.
    apply empty_neq in A_ex, B_ex.
    destruct A_ex as [a Aa].
    destruct B_ex as [b Bb].
    destruct (trichotomy a b) as [[ab|ab]|ab].
    -   exact (convex_connected_wlog S S_convex A B a b Aa Bb ab AB_sep).
    -   subst.
        assert ((A ∩ B) b) as b_in by (split; assumption).
        rewrite (land (rand (rand (rand (rand AB_sep))))) in b_in.
        exact b_in.
    -   rewrite separation_comm in AB_sep.
        exact (convex_connected_wlog S S_convex B A b a Bb Aa ab AB_sep).
Qed.

Theorem open_interval_connected :
    ∀ a b, connected (set_type (open_interval a b)).
Proof.
    intros a b.
    apply convex_connected.
    apply open_interval_convex.
Qed.
Theorem open_closed_interval_connected :
    ∀ a b, connected (set_type (open_closed_interval a b)).
Proof.
    intros a b.
    apply convex_connected.
    apply open_closed_interval_convex.
Qed.
Theorem closed_open_interval_connected :
    ∀ a b, connected (set_type (closed_open_interval a b)).
Proof.
    intros a b.
    apply convex_connected.
    apply closed_open_interval_convex.
Qed.
Theorem closed_interval_connected :
    ∀ a b, connected (set_type (closed_interval a b)).
Proof.
    intros a b.
    apply convex_connected.
    apply closed_interval_convex.
Qed.
Theorem open_inf_interval_connected :
    ∀ a, connected (set_type (open_inf_interval a)).
Proof.
    intros a.
    apply convex_connected.
    apply open_inf_interval_convex.
Qed.
Theorem closed_inf_interval_connected :
    ∀ a, connected (set_type (closed_inf_interval a)).
Proof.
    intros a.
    apply convex_connected.
    apply closed_inf_interval_convex.
Qed.
Theorem inf_open_interval_connected :
    ∀ a, connected (set_type (inf_open_interval a)).
Proof.
    intros a.
    apply convex_connected.
    apply inf_open_interval_convex.
Qed.
Theorem inf_closed_interval_connected :
    ∀ a, connected (set_type (inf_closed_interval a)).
Proof.
    intros a.
    apply convex_connected.
    apply inf_closed_interval_convex.
Qed.
(* begin hide *)
End OrderTopology.
(* end hide *)
