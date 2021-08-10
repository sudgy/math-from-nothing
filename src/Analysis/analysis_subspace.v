Require Import init.

Require Export analysis_base.
Require Import analysis_topology.
Require Import analysis_sequence.

(* begin hide *)
Section SubspaceMetric.

Context {U} `{Metric U}.
(* end hide *)
Variable X : U → Prop.

Program Instance subspace_metric : Metric (set_type X) := {
    d x y := d [x|] [y|]
}.
Next Obligation.
    destruct x as [x Xx], y as [y Xy]; cbn.
    split.
    -   intros eq.
        apply set_type_eq; cbn.
        apply d_ind.
        exact eq.
    -   intros eq.
        inversion eq.
        rewrite d_zero.
        reflexivity.
Qed.
Next Obligation.
    destruct x as [x Xx], y as [y Xy]; cbn.
    apply d_sym.
Qed.
Next Obligation.
    destruct x as [x Xx], y as [y Xy], z as [z Xz]; cbn.
    apply d_tri.
Qed.

Theorem complete_sub_closed : complete U → closed X ↔ complete (set_type X).
    intros U_complete.
    split.
    -   intros X_closed Xf Xf_cauchy.
        pose (f n := [Xf n|]).
        specialize (U_complete f Xf_cauchy) as [x fx].
        rewrite metric_seq_closed in X_closed.
        assert (∀ n, X (f n)) as f_in_X.
        {
            intros n.
            unfold f.
            exact [|Xf n].
        }
        specialize (X_closed f x f_in_X fx) as Xx.
        exists [x|Xx].
        rewrite metric_seq_lim.
        rewrite metric_seq_lim in fx.
        apply fx.
    -   intros X_complete.
        apply metric_seq_closed.
        intros f x f_in_X fx.
        pose (Xf n := [f n|f_in_X n]).
        assert (seq_converges f) as f_cauchy by (exists x; exact fx).
        apply converges_cauchy in f_cauchy.
        specialize (X_complete Xf f_cauchy) as [[x' Xx'] Xfx'].
        assert (seq_lim f x') as fx'.
        {
            rewrite metric_seq_lim.
            rewrite metric_seq_lim in Xfx'.
            exact Xfx'.
        }
        rewrite (seq_lim_unique _ _ _ fx fx').
        exact Xx'.
Qed.

(* begin hide *)
End SubspaceMetric.

Section SubspaceMetricEquiv.

Existing Instance subspace_metric.
(* end hide *)
Theorem metric_subspace_topology {U} `{Metric U} : ∀ X,
        subspace_topology X = (basis_topology (b := metric_topology)).
    intros X.
    apply topology_equal.
    intros S.
    split.
    -   intros [T [T_open S_eq]]; subst S.
        intros [x Xx] Tx.
        specialize (T_open x Tx) as [B [[y [ε B_eq]] [Bx sub]]]; subst B.
        pose proof (open_ball_ex _ _ _ Bx) as [δ δ_sub].
        exists (to_set_type X (open_ball x δ)).
        split.
        2: split.
        +   unfold top_basis; cbn.
            exists [x|Xx], δ.
            reflexivity.
        +   apply open_ball_self.
        +   apply to_set_type_sub.
            exact (trans δ_sub sub).
    -   rewrite <- subspace_basis_eq.
        unfold open; cbn.
        intros S_open x Sx.
        specialize (S_open x Sx) as [B [[y [ε B_eq]] [Bx B_sub]]].
        subst B.
        exists (open_ball y ε).
        split.
        2: split.
        +   exists (open_ball [y|] ε).
            split.
            *   exists [y|], ε; reflexivity.
            *   reflexivity.
        +   exact Bx.
        +   exact B_sub.
Qed.
(* begin hide *)

End SubspaceMetricEquiv.
(* end hide *)
