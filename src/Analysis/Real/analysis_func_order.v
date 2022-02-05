Require Import init.

Require Export analysis_norm.
Require Import analysis_topology.
Require Import analysis_sequence.
Require Import analysis_function.
Require Import analysis_order.

(* begin hide *)
Section AnalysisOrder.

Context {U} `{Metric U}.

Existing Instance abs_metric.
(* end hide *)

Theorem func_lim_pos : ∀ (A : U → Prop) (xf : set_type A → real) c l,
        (∀ x, 0 <= xf x) → func_lim A xf c l → 0 <= l.
    intros A xf c l xf_pos x_lim.
    pose proof (land x_lim) as Ac.
    rewrite metric_func_seq_lim in x_lim by exact Ac.
    pose proof (limit_point_seq_ex _ _ Ac) as [xn [xn_eq xn_lim]].
    pose (xn' n := [xn n | xn_eq n] : set_type (A - singleton c)%set).
    specialize (x_lim xn' xn_lim).
    apply seq_lim_pos in x_lim; [>exact x_lim|].
    intros n.
    apply xf_pos.
Qed.

Theorem func_lim_le : ∀ (A : U → Prop) (xf yf : set_type A → real) c x y,
        (∀ x, xf x <= yf x) → func_lim A xf c x → func_lim A yf c y → x <= y.
    intros A xf yf c x y leq cx cy.
    pose proof (land cx) as Ac.
    rewrite metric_func_seq_lim in cx, cy by exact Ac.
    pose proof (limit_point_seq_ex _ _ Ac) as [xn [xn_eq xn_lim]].
    pose (xn' n := [xn n | xn_eq n] : set_type (A - singleton c)%set).
    specialize (cx xn' xn_lim).
    specialize (cy xn' xn_lim).
    eapply (seq_lim_le _ _ _ _ _ cx cy).
    Unshelve.
    intros n; cbn.
    apply leq.
Qed.

Theorem func_squeeze : ∀ (A : U → Prop) (af bf cf : set_type A → real) c l,
        (∀ x, c ≠ [x|] → af x <= bf x ∧ bf x <= cf x) →
        func_lim A af c l → func_lim A cf c l → func_lim A bf c l.
    intros A af bf cf c l leq al cl.
    pose proof (land al) as Ac.
    rewrite metric_func_seq_lim in * by exact Ac.
    intros xn xnc.
    specialize (al xn xnc).
    specialize (cl xn xnc).
    eapply (seq_squeeze _ _ _ _ _ al cl).
    Unshelve.
    intros n.
    apply leq.
    cbn.
    apply [|xn n].
Qed.
(* begin hide *)

End AnalysisOrder.
(* end hide *)
