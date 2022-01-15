Require Import init.

Require Export topology_base.
Require Export topology_basis.
Require Import topology_axioms.
Require Import topology_closure.
Require Import topology_subspace.
Require Import order_minmax.

Unset Keyed Unification.

Open Scope set_scope.

Definition limit_point {U} `{Topology U} A x := ∀ S, open S → S x →
    intersects (A - singleton x) S.

Definition seq_lim {U} `{Topology U} (f : sequence U) x :=
    ∀ S, open S → S x → ∃ N, ∀ n, N <= n → S (f n).
Definition seq_converges {U} `{Topology U} (f : sequence U) := ∃ x, seq_lim f x.

Definition f_seq_lim {U V} `{Topology U, Topology V} (fn : sequence (U → V)) f:=
    ∀ x, seq_lim (λ n, (fn n x)) (f x).
Definition f_seq_converges {U V} `{Topology U, Topology V}
    (fn : sequence (U → V)) := ∃ f, f_seq_lim fn f.

(* begin hide *)
Section LimitPoint.

Context {U} `{Topology U}.
(* end hide *)
Theorem closure_limit_points : ∀ A, closure A = A ∪ limit_point A.
    intros A.
    apply predicate_ext; intros x; split.
    -   intros CAx.
        classic_case (A x) as [Ax|Ax].
        +   left; exact Ax.
        +   right.
            intros S S_open Sx.
            rewrite in_closure in CAx.
            specialize (CAx S S_open Sx).
            assert (A - singleton x = A) as eq.
            {
                apply predicate_ext; intros y; split.
                -   intros [Ay C0]; exact Ay.
                -   intros Ay.
                    split; try exact Ay.
                    unfold singleton; intro contr; subst.
                    contradiction.
            }
            rewrite eq.
            exact CAx.
    -   intros [Ax|x_lim].
        +   apply closure_sub.
            exact Ax.
        +   rewrite in_closure.
            intros S S_open Sx.
            specialize (x_lim S S_open Sx).
            apply not_empty_ex in x_lim.
            apply ex_not_empty.
            destruct x_lim as [y y_in].
            exists y.
            split; apply y_in.
Qed.

Theorem closed_limit_points : ∀ A, closed A ↔ (∀ x, limit_point A x → A x).
    intros A.
    rewrite closed_if_closure.
    rewrite closure_limit_points.
    split.
    -   intros eq x x_lim.
        rewrite eq.
        right; exact x_lim.
    -   intros x_lims.
        apply predicate_ext; intros x; split.
        +   intros Ax; left; exact Ax.
        +   intros [Ax|x_lim].
            *   exact Ax.
            *   apply x_lims.
                exact x_lim.
Qed.

Theorem seq_closure :
        ∀ (A : U → Prop) x f, (∀ n, A (f n)) → seq_lim f x → closure A x.
    intros A x f Af lim.
    rewrite in_closure.
    intros S S_open Sx.
    specialize (lim S S_open Sx) as [N lim].
    specialize (lim N (refl _)).
    apply ex_not_empty.
    exists (f N).
    split.
    -   apply Af.
    -   exact lim.
Qed.

Theorem limit_point_closure : ∀ A x, limit_point A x → closure A x.
    intros A x x_lim.
    rewrite closure_limit_points.
    right.
    exact x_lim.
Qed.

Theorem limit_point_sub : ∀ A B x, A ⊆ B → limit_point A x → limit_point B x.
    intros A B x sub A_lim S S_open Sx.
    specialize (A_lim S S_open Sx).
    apply not_empty_ex in A_lim.
    destruct A_lim as [y [[Ay yx] Sy]].
    apply ex_not_empty.
    exists y.
    repeat split.
    -   exact (sub y Ay).
    -   exact yx.
    -   exact Sy.
Qed.

Existing Instance subspace_topology.

Theorem subspace_limit_point : ∀ X A x, A ⊆ X →
        limit_point A [x|] → limit_point (to_set_type X A) x.
    intros X A x sub lim S S_open Sx.
    unfold limit_point in lim.
    destruct S_open as [T [T_open S_eq]].
    pose proof Sx as Tx.
    rewrite S_eq in Tx.
    specialize (lim _ T_open Tx).
    apply not_empty_ex in lim.
    destruct lim as [y [[Ay y_neq] Ty]].
    apply ex_not_empty.
    exists [y|sub y Ay].
    repeat split.
    -   exact Ay.
    -   unfold singleton in *; cbn in *.
        intro contr.
        subst x.
        contradiction.
    -   subst S.
        exact Ty.
Qed.

Theorem constant_seq_lim : ∀ x, seq_lim (λ _, x) x.
    intros x S S_open Sx.
    exists 0.
    intros n n_ge.
    exact Sx.
Qed.

Theorem constant_seq_converges : ∀ x, seq_converges (λ _, x).
    intros x.
    exists x.
    apply constant_seq_lim.
Qed.

Theorem subsequence_lim_eq :
        ∀ a b x, seq_lim a x → subsequence a b → seq_lim b x.
    intros a b x a_lim [f [f_sub ab_eq]].
    intros S S_open Sx.
    specialize (a_lim S S_open Sx) as [N a_lim].
    exists N.
    intros n n_ge.
    rewrite <- ab_eq.
    pose proof (subsequence_seq_leq f f_sub n) as f_leq.
    exact (a_lim (f n) (trans n_ge f_leq)).
Qed.

(* begin hide *)
Close Scope set_scope.
(* end hide *)
Theorem seq_lim_part : ∀ a n x, seq_lim a x ↔ seq_lim (λ m, a (m + n)) x.
    intros a n x.
    split.
    -   intros x_lim S S_open Sx.
        specialize (x_lim S S_open Sx) as [N x_lim].
        exists N.
        intros m m_ge.
        apply x_lim.
        apply (trans m_ge).
        apply nat_le_self_rplus.
    -   intros x_lim S S_open Sx.
        specialize (x_lim S S_open Sx) as [N x_lim].
        exists (N + n).
        intros m m_ge.
        apply nat_le_ex in m_ge as [c m_eq]; subst m.
        rewrite <- plus_assoc, (plus_comm n c), plus_assoc.
        apply x_lim.
        apply nat_le_self_rplus.
Qed.

(* begin hide *)
Open Scope set_scope.

End LimitPoint.
(* end hide *)
Section HausdorffLimit.

Context {U} `{HausdorffSpace U}.

(* begin hide *)
Local Open Scope card_scope.
(* end hide *)
Theorem limit_point_inf : ∀ A x,
        limit_point A x ↔ ∀ S, open S → S x → infinite (|set_type (A ∩ S)|).
    intros A x.
    split.
    -   intros x_lim S S_open Sx.
        classic_contradiction fin.
        unfold infinite in fin.
        rewrite nle_lt in fin.
        pose (X := (A - singleton x) ∩ S).
        assert (finite (|set_type X|)) as X_fin.
        {
            apply (le_lt_trans2 fin).
            unfold X.
            unfold le; equiv_simpl.
            pose (f (a : set_type ((A - singleton x) ∩ S)) := [[a|] |
                make_and (land (land [|a])) (rand [|a])] : set_type (A ∩ S)).
            exists f.
            unfold f; clear f.
            intros a b eq.
            inversion eq as [eq2].
            apply set_type_eq; exact eq2.
        }
        apply finite_point_closed in X_fin.
        unfold closed in X_fin.
        rename X_fin into X'_open.
        pose (Y := S ∩ complement X).
        assert (open Y) as Y_open.
        {
            unfold Y.
            apply inter_open2; assumption.
        }
        assert (Y x) as Yx.
        {
            split.
            -   exact Sx.
            -   intros [[C0 contr] C1].
                unfold singleton in contr.
                contradiction.
        }
        specialize (x_lim Y Y_open Yx).
        apply not_empty_ex in x_lim.
        destruct x_lim as [a [[Aa nax] Ya]].
        unfold Y, X in Ya.
        unfold complement, intersection, set_minus, singleton in Ya.
        not_simpl in Ya.
        destruct Ya as [Sa [[Aa'|ax]|Sa']]; contradiction.
    -   intros all_S S S_open Sx.
        apply ex_not_empty.
        specialize (all_S S S_open Sx).
        unfold infinite in all_S.
        apply (lt_le_trans (nat_is_finite 2)) in all_S as [all_S C0]; clear C0.
        unfold nat_to_card, le in all_S; equiv_simpl in all_S.
        destruct all_S as [f f_inj].
        assert ((zero (U := nat)) < 2) as z_lt.
        {
            rewrite <- (plus_rid 0).
            apply lt_lrplus; apply nat_lt_suc.
        }
        pose (n2_type := nat_to_set_type 2).
        pose (n0 := [0|z_lt] : n2_type).
        pose proof (nat_lt_suc 0) as o_lt.
        apply lt_rplus with one in o_lt.
        rewrite plus_lid in o_lt.
        pose (n1 := [1|o_lt] : n2_type).
        classic_case ([f n0|] = x) as [eq|neq].
        +   exists [f n1|].
            repeat split; try apply [|f n1].
            unfold singleton; intros contr.
            subst.
            apply set_type_eq in contr.
            apply f_inj in contr.
            unfold n0, n1 in contr.
            inversion contr.
        +   exists [f n0|].
            repeat split; try apply [|f n0].
            unfold singleton; intros contr.
            subst.
            contradiction.
Qed.

Theorem seq_lim_unique : ∀ f x y, seq_lim f x → seq_lim f y → x = y.
    intros f x y x_lim y_lim.
    classic_contradiction neq.
    pose proof (hausdorff_space x y neq)
        as [S1 [S2 [S1_open [S2_open [S1x [S2y dis]]]]]].
    specialize (x_lim S1 S1_open S1x) as [N1 x_lim].
    specialize (y_lim S2 S2_open S2y) as [N2 y_lim].
    specialize (x_lim (max N1 N2) (lmax N1 N2)).
    specialize (y_lim (max N1 N2) (rmax N1 N2)).
    apply (empty_not_ex _ dis (f (max N1 N2))).
    split; assumption.
Qed.

End HausdorffLimit.

(* begin hide *)
Section BasisLimit.

Context {U} `{TopologyBasis U}.
(* end hide *)
Theorem basis_seq_lim : ∀ f x, seq_lim f x ↔
        ∀ S, top_basis S → S x → ∃ N, ∀ n, N <= n → S (f n).
    intros f x.
    split.
    -   intros f_lim S S_basis Sx.
        apply basis_open in S_basis.
        exact (f_lim S S_basis Sx).
    -   intros all_S S S_open Sx.
        specialize (S_open x Sx) as [B [B_basis [Bx sub]]].
        specialize (all_S B B_basis Bx) as [N lim].
        exists N.
        intros n n_gt.
        apply sub.
        apply lim.
        exact n_gt.
Qed.
(* begin hide *)
End BasisLimit.

Close Scope set_scope.
(* end hide *)
