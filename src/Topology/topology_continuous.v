Require Import init.

Require Export topology_base.
Require Import topology_basis.
Require Import topology_closure.
Require Import topology_limit.
Require Import topology_connected.
Require Import topology_compact.
Require Import topology_order.

(* begin hide *)
Open Scope card_scope.
Open Scope set_scope.
(* end hide *)
Definition continuous_at {U V} `{Topology U, Topology V} (f : U → V) x
    := ∀ T, neighborhood (f x) T →
       ∃ S, neighborhood x S ∧ image_under f S ⊆ T.
Definition continuous {U V} `{Topology U, Topology V} (f : U → V)
    := ∀ x, continuous_at f x.

(* begin hide *)
Module ContinuousImpl.
Section Continuous.

Context {U V} `{Topology U, Topology V}.

Let c1 (f : U → V) :=
    ∀ A, open A → open (inverse_image f A).
Let c2 (f : U → V) :=
    ∀ A, image_under f (closure A) ⊆ closure (image_under f A).
Let c3 (f : U → V) :=
    ∀ B, closed B → closed (inverse_image f B).

Lemma c1c2 : ∀ f, c1 f → c2 f.
Proof.
    unfold c1, c2; clear c1 c2 c3.
    intros f all_open A y y_in.
    destruct y_in as [x [Ax y_eq]].
    subst y.
    rewrite in_closure.
    intros B B_open Bfx.
    specialize (all_open B B_open).
    rewrite in_closure in Ax.
    specialize (Ax _ all_open Bfx).
    apply not_empty_ex in Ax as [y [Ay By]].
    apply ex_not_empty.
    exists (f y).
    split.
    -   exists y.
        split; trivial.
    -   exact By.
Qed.

Lemma c2c3 : ∀ f, c2 f → c3 f.
Proof.
    unfold c2, c3; clear c1 c2 c3.
    intros f cl_sub B B_closed.
    remember (inverse_image f B) as A.
    assert (closure A = A) as closure_eq.
    {
        apply (antisym (op := subset)).
        -   intros x cAx.
            specialize (cl_sub A).
            assert (image_under f (closure A) (f x)) as Afx.
            {
                exists x.
                split; trivial.
            }
            apply cl_sub in Afx.
            subst A.
            unfold inverse_image.
            apply (closure_sub_closure _ _ (image_inverse_sub _ _)) in Afx.
            rewrite <- closure_eq_if_closed in Afx by exact B_closed.
            exact Afx.
        -   apply closure_sub.
    }
    rewrite <- closure_eq.
    apply closure_closed.
Qed.

Lemma c3c1 : ∀ f, c3 f → c1 f.
Proof.
    unfold c1, c3; clear c1 c2 c3.
    intros f all_closed B B_open.
    specialize (all_closed (complement B) (open_complement_closed _ B_open)).
    rewrite inverse_complement in all_closed.
    unfold closed in all_closed.
    rewrite compl_compl in all_closed.
    exact all_closed.
Qed.

Lemma c1c : ∀ f, c1 f → continuous f.
Proof.
    unfold c1, continuous, continuous_at; clear c1 c2 c3.
    intros f all_open x B B_neigh.
    exists (inverse_image f B).
    split.
    -   split.
        +   apply all_open.
            apply B_neigh.
        +   apply B_neigh.
    -   intros y y_in.
        apply image_inverse_sub in y_in.
        exact y_in.
Qed.

Lemma cc1 : ∀ f, continuous f → c1 f.
Proof.
    unfold c1, continuous, continuous_at; clear c1 c2 c3.
    intros f f_cont B B_open.
    assert (∀ x : set_type (inverse_image f B),
            ∃ S, neighborhood [x|] S ∧ S ⊆ (inverse_image f B)) as S_ex.
    {
        intros [x fBx]; cbn.
        specialize (f_cont x B (make_and B_open fBx)) as [S [S_neigh S_sub]].
        exists S.
        split; try assumption.
        intros a Sa.
        apply S_sub.
        exists a.
        split; trivial.
    }
    pose (SS S := ∃ x, ex_val (S_ex x) = S).
    assert (⋃ SS = (inverse_image f B)) as eq.
    {
        apply (antisym (op := subset)).
        -   intros x [S [[y S_eq] Sx]].
            subst S.
            rewrite_ex_val S SH.
            destruct SH as [S_neigh S_sub].
            apply S_sub.
            exact Sx.
        -   intros x Bfx.
            exists (ex_val (S_ex [x|Bfx])).
            split.
            +   exists [x|Bfx].
                reflexivity.
            +   rewrite_ex_val S S_H.
                apply S_H.
    }
    rewrite <- eq.
    apply union_open.
    intros S [x S_eq].
    subst S.
    rewrite_ex_val S S_H.
    apply S_H.
Qed.

Lemma continuous_open : ∀ f, continuous f ↔ c1 f.
Proof.
    intros f; split; intro cont.
    -   apply cc1; exact cont.
    -   apply c1c; exact cont.
Qed.

Lemma continuous_closure : ∀ f, continuous f ↔ c2 f.
Proof.
    intros f.
    rewrite continuous_open.
    split; intro cont.
    -   apply c1c2; exact cont.
    -   apply c3c1; apply c2c3; exact cont.
Qed.

Lemma continuous_closed : ∀ f, continuous f ↔ c3 f.
Proof.
    intros f; split; intro cont.
    -   apply c2c3; apply continuous_closure; exact cont.
    -   apply continuous_open; apply c3c1; exact cont.
Qed.

End Continuous.
End ContinuousImpl.

Section Continuous.

Context {U V} `{Topology U, Topology V}.
(* end hide *)
Theorem continuous_open : ∀ f : U → V,
    continuous f ↔ (∀ A, open A → open (inverse_image f A)).
Proof.
    exact ContinuousImpl.continuous_open.
Qed.

Theorem continuous_closure : ∀ f : U → V,
    continuous f ↔ (∀ A, image_under f (closure A) ⊆ closure (image_under f A)).
Proof.
    exact ContinuousImpl.continuous_closure.
Qed.

Theorem continuous_closed : ∀ f : U → V,
    continuous f ↔ (∀ B, closed B → closed (inverse_image f B)).
Proof.
    exact ContinuousImpl.continuous_closed.
Qed.

Theorem constant_continuous : ∀ (y : V), continuous (λ x : U, y).
Proof.
    intros y x T T_neigh.
    exists all.
    repeat split.
    -   apply all_open.
    -   intros z [C0 [C1 eq]]; clear C0 C1.
        subst.
        apply T_neigh.
Qed.

Theorem identity_continuous : continuous (λ x : U, x).
Proof.
    intros x T T_neigh.
    exists T.
    split.
    -   apply T_neigh.
    -   intros y [y' [Ty eq]].
        rewrite eq; exact Ty.
Qed.

Theorem continuous_seq : ∀ (f : U → V) x, continuous_at f x →
    ∀ a, seq_lim a x → seq_lim (λ n, f (a n)) (f x).
Proof.
    intros f x cont a lim.
    intros T T_open Tfx.
    specialize (cont T (make_and T_open Tfx)) as [S [[S_open Sx] sub]].
    specialize (lim S S_open Sx) as [N lim].
    exists N.
    intros n n_gt.
    specialize (lim n n_gt).
    apply sub.
    exists (a n).
    split; trivial.
Qed.

Theorem continuous_connected : ∀ (f : U → V), continuous f → surjective f →
    connected U → connected V.
Proof.
    intros f f_cont f_sur f_con A B
        [A_empty [B_empty [A_open [B_open [AB_dis AB_all]]]]].
    apply (f_con (inverse_image f A) (inverse_image f B)).
    repeat split.
    -   apply ex_not_empty.
        apply not_empty_ex in A_empty.
        destruct A_empty as [y Ay].
        destruct (f_sur y) as [x eq].
        exists x.
        unfold inverse_image.
        rewrite eq.
        exact Ay.
    -   apply ex_not_empty.
        apply not_empty_ex in B_empty.
        destruct B_empty as [y By].
        destruct (f_sur y) as [x eq].
        exists x.
        unfold inverse_image.
        rewrite eq.
        exact By.
    -   pose proof (continuous_open).
        apply continuous_open; assumption.
    -   apply continuous_open; assumption.
    -   unfold disjoint.
        apply not_ex_empty.
        intros x [Ax Bx].
        unfold disjoint in AB_dis.
        assert ((A ∩ B) (f x)) as ABfx by (split; assumption).
        rewrite AB_dis in ABfx.
        exact ABfx.
    -   apply antisym; try apply sub_all.
        intros x C0; clear C0.
        assert ((A ∪ B) (f x)) as [Afx|Bfx].
        {
            rewrite AB_all.
            exact true.
        }
        +   left.
            exact Afx.
        +   right.
            exact Bfx.
Qed.

(* begin hide *)
Context {W} `{Topology W}.
(* end hide *)
Theorem comp_continuous_at : ∀ (f : U → V) (g : V → W) a,
    continuous_at f a → continuous_at g (f a) →
    continuous_at (λ x, g (f x)) a.
Proof.
    intros f g a f_cont g_cont.
    intros T T_neigh.
    specialize (g_cont T T_neigh) as [S [S_neigh S_sub]].
    specialize (f_cont S S_neigh) as [R [R_neigh R_sub]].
    exists R.
    split; try exact R_neigh.
    intros c [b [Rb c_eq]]; subst c.
    apply S_sub.
    exists (f b).
    split; try reflexivity.
    apply R_sub.
    exists b.
    split; trivial.
Qed.

Theorem comp_continuous : ∀ (f : U → V) (g : V → W),
    continuous f → continuous g → continuous (λ x, g (f x)).
Proof.
    intros f g f_cont g_cont x.
    apply comp_continuous_at.
    -   apply f_cont.
    -   apply g_cont.
Qed.

(* begin hide *)
End Continuous.
Section Continuous.

Context {U V} `{Topology U, Topology V}.

Existing Instance subspace_topology.
(* end hide *)
Theorem continuous_connected_image : ∀ (f : U → V), continuous f →
    connected U → connected (set_type (image f)).
Proof.
    intros f f_cont U_con.
    assert (∀ x, (image f) (f x)) as f_in
        by (intros x; exists x; reflexivity).
    pose (f' x := [f x|f_in x]).
    apply (continuous_connected f').
    -   rewrite continuous_open in f_cont.
        rewrite continuous_open.
        intros S [T [T_open S_eq]].
        specialize (f_cont T T_open).
        assert (inverse_image f T = inverse_image f' S) as eq.
        {
            apply antisym.
            -   intros x fx.
                unfold inverse_image in *.
                rewrite S_eq.
                unfold f'; cbn.
                exact fx.
            -   intros x fx.
                unfold inverse_image in *.
                rewrite S_eq in fx.
                apply fx.
        }
        rewrite <- eq.
        exact f_cont.
    -   unfold f'.
        intros [y [x eq]].
        exists x.
        apply set_type_eq; cbn.
        symmetry; exact eq.
    -   exact U_con.
Qed.

Theorem continuous_compact_image : ∀ (f : U → V), continuous f →
    compact U → compact (set_type (image f)).
Proof.
    intros f f_cont U_comp.
    apply compact_subspace.
    intros VSS [VSS_sub VSS_open].
    pose (SS S := ∃ S', VSS S' ∧ inverse_image f S' = S).
    assert (open_covering SS) as SS_cover.
    {
        split.
        -   intros x C0; clear C0.
            assert (image f (f x)) as ffx by (exists x; reflexivity).
            apply VSS_sub in ffx.
            destruct ffx as [B [VSS_B Afx]].
            exists (inverse_image f B).
            split.
            +   exists B.
                split; trivial.
            +   exact Afx.
        -   intros A [B [VSS_B A_eq]].
            subst A.
            apply continuous_open.
            1: exact f_cont.
            apply VSS_open.
            exact VSS_B.
    }
    specialize (U_comp SS SS_cover) as [SS' [SS'_sub [SS'_fin sub_SS']]].
    pose (VSS' S := ∃ S', S = ex_val (SS'_sub [S'|] [|S'])).
    exists VSS'.
    split.
    2: split.
    -   intros B [[A SS'_A] B_eq].
        subst B.
        rewrite_ex_val B B_H.
        apply B_H.
    -   apply (le_lt_trans2 SS'_fin).
        unfold le; equiv_simpl.
        exists (λ VS : set_type VSS', ex_val [|VS]).
        intros [VS1 VS1_in] [VS2 VS2_in] eq; cbn in *.
        rewrite_ex_val S1 VS1_eq.
        rewrite_ex_val_with VS2_in S2 VS2_eq.
        subst.
        apply set_type_eq; cbn.
        reflexivity.
    -   intros y [x y_eq]; subst y.
        specialize (sub_SS' x) as [A [SS'_A Ax]].
        exists (ex_val (SS'_sub A SS'_A)).
        split.
        +   exists [A|SS'_A].
            reflexivity.
        +   rewrite_ex_val B B_H.
            destruct B_H as [VSS_B A_eq].
            subst A.
            exact Ax.
Qed.

Theorem continuous_subspace : ∀ (f : U → V) (S : U → Prop) x,
    continuous_at f [x|] → continuous_at (λ x : set_type S, f [x|]) x.
Proof.
    intros f S x f_cont T T_neigh.
    specialize (f_cont T T_neigh) as [R [Rx R_sub]].
    exists (to_set_type S R).
    split; [>split|].
    -   exists R.
        split; [>apply Rx|reflexivity].
    -   apply Rx.
    -   intros z [y [Ry z_eq]].
        apply R_sub.
        exists [y|].
        split; assumption.
Qed.

Theorem continuous_subspace2 : ∀ (S : V → Prop) (f : U → set_type S) x,
    continuous_at (λ x, [f x|]) x → continuous_at f x.
Proof.
    intros S f x f_cont T' [T_open Tx].
    destruct T_open as [T [T_open T'_eq]]; subst T'.
    specialize (f_cont T (make_and T_open Tx)) as [R [Rx R_sub]].
    exists R.
    split; [>split|].
    -   apply Rx.
    -   apply Rx.
    -   intros z [y [Ry z_eq]].
        apply R_sub.
        exists y.
        split; [>exact Ry|].
        apply eq_set_type.
        exact z_eq.
Qed.

(* begin hide *)
End Continuous.

Section ContinuousBasis.

Context {U V} `{Topology U, TopologyBasis V}.
(* end hide *)
Theorem basis_continuous_at : ∀ (f : U → V) x,
    continuous_at f x ↔
    (∀ T, top_basis T → T (f x) →
        ∃ S, neighborhood x S ∧ image_under f S ⊆ T).
Proof.
    intros f x.
    split.
    -   intros cont T T_basis Tfx.
        specialize (cont T (make_and (basis_open _ T_basis) Tfx))
            as [S [[S_open Sx] sub]].
        exists S.
        repeat split; assumption.
    -   intros all_T T' [T'_open T'fx].
        specialize (T'_open (f x) T'fx) as [T [T_basis [Tfx T_sub]]].
        specialize (all_T T T_basis Tfx) as [S [S_neigh S_sub]].
        exists S.
        split.
        +   exact S_neigh.
        +   exact (trans S_sub T_sub).
Qed.

Theorem basis_continuous_open : ∀ f,
    continuous f ↔ (∀ B, top_basis B → open (inverse_image f B)).
Proof.
    intros f.
    rewrite continuous_open.
    split.
    -   intros cont B B_basis.
        apply cont.
        apply basis_open.
        exact B_basis.
    -   intros cont B B_open.
        rewrite basis_open_unions in B_open.
        destruct B_open as [SS [SS_basis SS_eq]].
        rewrite <- SS_eq.
        rewrite inverse_union.
        apply union_open.
        intros A' [A [SSA A_eq]]; subst A'.
        apply cont.
        apply SS_basis.
        exact SSA.
Qed.

(* begin hide *)
End ContinuousBasis.
(* end hide *)
Section IVT.

(* begin hide *)
Context {U V} `{
    Topology U,
    Order V,
    Reflexive V le,
    Connex V le,
    Antisymmetric V le,
    Transitive V le,
    NotTrivial V
}.
(* end hide *)
Hypothesis con : connected U.

(* begin hide *)
Existing Instance order_topology.
(* end hide *)
Theorem ivt : ∀ f : U → V, continuous f →
    ∀ a b r, f a < r → r < f b → ∃ c, f c = r.
Proof.
    intros f f_cont a b r r_gt r_lt.
    classic_contradiction contr.
    rewrite not_ex in contr.
    apply continuous_connected_image in f_cont; try exact con.
    pose (A := inf_open_interval r).
    pose (B := open_inf_interval r).
    apply (f_cont (to_set_type _ A) (to_set_type _ B)).
    assert (∀ x, (image f) (f x)) as f_in by (intros x; exists x; reflexivity).
    repeat split.
    -   apply ex_not_empty.
        exists [f a|f_in a].
        exact r_gt.
    -   apply ex_not_empty.
        exists [f b|f_in b].
        exact r_lt.
    -   exists A.
        split.
        +   apply inf_open_interval_open.
        +   apply antisym.
            *   intros [x fx] Ax.
                exact Ax.
            *   intros x Ax.
                exact Ax.
    -   exists B.
        split.
        +   apply open_inf_interval_open.
        +   apply antisym.
            *   intros [x fx] Bx.
                assumption.
            *   intros x Bx.
                exact Bx.
    -   apply not_ex_empty.
        intros [y [x eq]] [Ay By].
        unfold to_set_type in Ay, By; cbn in *.
        unfold A, B in Ay, By.
        unfold inf_open_interval, open_inf_interval in Ay, By.
        destruct (trans Ay By); contradiction.
    -   apply antisym; try apply sub_all.
        intros [y [x eq]] C0; clear C0.
        subst.
        destruct (trichotomy (f x) r) as [[leq|neq]|leq].
        +   left.
            exact leq.
        +   contradiction (contr _ neq).
        +   right.
            exact leq.
Qed.

End IVT.

Section EVT.

(* begin hide *)
Context {U V} `{
    Topology U,
    Order V,
    Reflexive V le,
    Connex V le,
    Antisymmetric V le,
    Transitive V le,
    NotTrivial V
}.
(* end hide *)
Hypothesis com : compact U.
Hypothesis U_inhab : U.

(* begin hide *)
Existing Instance order_topology.
(* end hide *)
Theorem evt : ∀ f : U → V, continuous f → ∃ c d, ∀ x, f c ≤ f x ∧ f x ≤ f d.
Proof.
    intros f f_cont.
    pose (A := image f).
    pose proof (continuous_compact_image f f_cont com) as A_compact.
    fold A in A_compact.
    classic_case (∃ M : set_type A, ∀ x, x ≤ M) as [M_ex|M_nex].
    2: {
        exfalso.
        rewrite not_ex in M_nex.
        pose (SS S := ∃ a : set_type A, S = inf_open_interval [a|]).
        assert (open_covering_of SS A) as SS_cover.
        {
            split.
            -   intros x Ax.
                specialize (M_nex [x|Ax]).
                rewrite not_all in M_nex.
                destruct M_nex as [[a Aa] a_lt].
                unfold le in a_lt; cbn in a_lt.
                rewrite nle_lt in a_lt.
                exists (inf_open_interval a).
                split.
                +   exists [a|Aa].
                    reflexivity.
                +   exact a_lt.
            -   intros S [a S_eq]; subst S.
                apply inf_open_interval_open.
        }
        rewrite compact_subspace in A_compact.
        specialize (A_compact SS SS_cover) as [SS' [SS'_sub [SS'_fin sub_SS']]].
        pose (A' a := ∃ S : set_type SS', a = ex_val (SS'_sub _ [|S])).
        assert (finite (|set_type A'|)) as A'_fin.
        {
            apply (le_lt_trans2 SS'_fin).
            unfold le; equiv_simpl.
            exists (λ a : set_type A', ex_val [|a]).
            intros [a A'a] [b A'b] eq; cbn in *.
            rewrite_ex_val S1 a_eq.
            rewrite_ex_val_with A'b S2 b_eq.
            subst.
            apply set_type_eq; cbn.
            reflexivity.
        }
        assert (∃ a : set_type A', ∀ a', A' a' → a' ≤ [a|]) as a_ex.
        {
            assert (∃ x, A' x) as A'_ex.
            {
                rename U_inhab into x.
                assert (A (f x)) as Af by (exists x; reflexivity).
                apply sub_SS' in Af as [B [SS'_B Bfx]].
                exists (ex_val (SS'_sub _ SS'_B)).
                exists [_|SS'_B].
                reflexivity.
            }
            pose proof (finite_well_ordered_set_max _ A'_fin A'_ex)
                as [a [A'a a_max]].
            exists [a|A'a].
            intros a' A'a'.
            apply a_max.
            exact A'a'.
        }
        destruct a_ex as [[[a Aa] [[S SS'_S] a_eq]] a_max]; cbn in *.
        pose proof Aa as Aa2.
        apply sub_SS' in Aa2.
        destruct Aa2 as [B [SS'_B Ba]].
        pose (a' := ex_val (SS'_sub B SS'_B)).
        assert (A' a') as A'a'.
        {
            exists [B|SS'_B].
            reflexivity.
        }
        unfold a' in *; clear a'.
        rewrite_ex_val a' B_eq.
        subst B.
        specialize (a_max _ A'a').
        unfold inf_open_interval in Ba.
        unfold le in a_max; cbn in a_max.
        destruct (lt_le_trans Ba a_max); contradiction.
    }
    classic_case (∃ m : set_type A, ∀ x, m ≤ x) as [m_ex|m_nex].
    2: {
        exfalso.
        rewrite not_ex in m_nex.
        pose (SS S := ∃ a : set_type A, S = open_inf_interval [a|]).
        assert (open_covering_of SS A) as SS_cover.
        {
            split.
            -   intros x Ax.
                specialize (m_nex [x|Ax]).
                rewrite not_all in m_nex.
                destruct m_nex as [[a Aa] a_lt].
                unfold le in a_lt; cbn in a_lt.
                rewrite nle_lt in a_lt.
                exists (open_inf_interval a).
                split.
                +   exists [a|Aa].
                    reflexivity.
                +   exact a_lt.
            -   intros S [a S_eq]; subst S.
                apply open_inf_interval_open.
        }
        rewrite compact_subspace in A_compact.
        specialize (A_compact SS SS_cover) as [SS' [SS'_sub [SS'_fin sub_SS']]].
        pose (A' a := ∃ S : set_type SS', a = ex_val (SS'_sub _ [|S])).
        assert (finite (|set_type A'|)) as A'_fin.
        {
            apply (le_lt_trans2 SS'_fin).
            unfold le; equiv_simpl.
            exists (λ a : set_type A', ex_val [|a]).
            intros [a A'a] [b A'b] eq; cbn in *.
            rewrite_ex_val S1 a_eq.
            rewrite_ex_val_with A'b S2 b_eq.
            subst.
            apply set_type_eq; cbn.
            reflexivity.
        }
        assert (∃ a : set_type A', ∀ a', A' a' → [a|] ≤ a') as a_ex.
        {
            assert (∃ x, A' x) as A'_ex.
            {
                rename U_inhab into x.
                assert (A (f x)) as Af by (exists x; reflexivity).
                apply sub_SS' in Af as [B [SS'_B Bfx]].
                exists (ex_val (SS'_sub _ SS'_B)).
                exists [_|SS'_B].
                reflexivity.
            }
            pose proof (finite_well_ordered_set _ A'_fin A'_ex)
                as [a [A'a a_min]].
            exists [a|A'a].
            intros a' A'a'.
            apply a_min.
            exact A'a'.
        }
        destruct a_ex as [[[a Aa] [[S SS'_S] a_eq]] a_max]; cbn in *.
        pose proof Aa as Aa2.
        apply sub_SS' in Aa2.
        destruct Aa2 as [B [SS'_B Ba]].
        pose (a' := ex_val (SS'_sub B SS'_B)).
        assert (A' a') as A'a'.
        {
            exists [B|SS'_B].
            reflexivity.
        }
        unfold a' in *; clear a'.
        rewrite_ex_val a' B_eq.
        subst B.
        specialize (a_max _ A'a').
        unfold inf_open_interval in Ba.
        unfold le in a_max; cbn in a_max.
        destruct (lt_le_trans Ba a_max); contradiction.
    }
    destruct m_ex as [[fc [c c_eq]] c_min]; subst fc.
    destruct M_ex as [[fd [d d_eq]] d_max]; subst fd.
    unfold le in d_max, c_min; cbn in *.
    exists c, d.
    intros x.
    assert (A (f x)) as Afx by (exists x; reflexivity).
    split.
    -   exact (c_min [_|Afx]).
    -   exact (d_max [_|Afx]).
Qed.

End EVT.
(* begin hide *)
Close Scope card_scope.
Close Scope set_scope.
(* end hide *)
