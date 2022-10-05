Require Import init.

Require Export analysis_norm.
Require Import analysis_order.

(* begin hide *)
Section AnalysisOrder.

Context {U} `{Metric U}.

Existing Instance abs_metric.
(* end hide *)

Theorem func_lim_pos : ∀ (A : U → Prop) (xf : set_type A → real) c l,
    limit_point A c → (∀ x, 0 ≤ xf x) → func_lim_base xf c l → 0 ≤ l.
Proof.
    intros A xf c l Ac xf_pos x_lim.
    rewrite metric_func_seq_lim in x_lim.
    pose proof (limit_point_seq_ex _ _ Ac) as [xn [xn_eq xn_lim]].
    pose (xn' n := [xn n | xn_eq n] : set_type (A - ❴c❵)%set).
    specialize (x_lim xn' xn_lim).
    apply seq_lim_pos in x_lim; [>exact x_lim|].
    intros n.
    apply xf_pos.
Qed.

Theorem func_lim_le : ∀ (A : U → Prop) (xf yf : set_type A → real) c x y,
    limit_point A c → (∀ x, xf x ≤ yf x) →
    func_lim_base xf c x → func_lim_base yf c y → x ≤ y.
Proof.
    intros A xf yf c x y Ac leq cx cy.
    rewrite metric_func_seq_lim in cx, cy.
    pose proof (limit_point_seq_ex _ _ Ac) as [xn [xn_eq xn_lim]].
    pose (xn' n := [xn n | xn_eq n] : set_type (A - ❴c❵)%set).
    specialize (cx xn' xn_lim).
    specialize (cy xn' xn_lim).
    eapply (seq_lim_le _ _ _ _ _ cx cy).
    Unshelve.
    intros n; cbn.
    apply leq.
Qed.

Theorem func_squeeze : ∀ (A : U → Prop) (af bf cf : set_type A → real) c l,
    (∀ x, c ≠ [x|] → af x ≤ bf x ∧ bf x ≤ cf x) →
    func_lim_base af c l → func_lim_base cf c l → func_lim_base bf c l.
Proof.
    intros A af bf cf c l leq al cl.
    rewrite metric_func_seq_lim in *.
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
