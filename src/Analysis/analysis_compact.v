Require Import init.

Require Export analysis_base.
Require Import analysis_topology.
Require Import analysis_sequence.
Require Import analysis_subspace.
Require Import order_minmax.
Require Import set_induction.
(* begin hide *)

Module AnalysisCompact1.
Section AnalysisCompact1.

Local Open Scope card_scope.

Context {U} `{Metric U}.

Hypothesis U_comp : limit_point_compact U.

Section Proof.

Variable a : sequence U.

Definition A x := ∃ n, a n = x.

Section Finite.

Hypothesis A_fin : finite (|set_type A|).

Lemma x_ex : ∃ x, infinite (|set_type (λ n, a n = x)|).
Proof.
    classic_contradiction contr.
    rewrite not_ex in contr.
    assert (infinite (|set_type A|)) as A_inf.
    {
        pose (op x y := x = y ∨ ∃ n, (∀ n', a n' = x → n' ≤ n) ∧ a n = y).
        assert (Reflexive op).
        {
            split.
            intros x.
            left.
            reflexivity.
        }
        assert (Antisymmetric op).
        {
            split.
            intros x y [eq1|xy] [eq2|yx]; subst; try reflexivity.
            destruct xy as [n1 [n1_max y_eq]].
            destruct yx as [n2 [n2_max x_eq]].
            subst.
            apply f_equal.
            apply antisym.
            -   apply n1_max.
                reflexivity.
            -   apply n2_max.
                reflexivity.
        }
        assert (Transitive op).
        {
            split.
            intros x y z [eq1|xy] [eq2|yz]; subst.
            -   apply refl.
            -   right.
                exact yz.
            -   right.
                exact xy.
            -   right.
                destruct xy as [n1 [n1_max y_eq]].
                destruct yz as [n2 [n2_max z_eq]].
                exists n2.
                split; try exact z_eq.
                intros n' x_eq.
                specialize (n1_max _ x_eq).
                specialize (n2_max _ y_eq).
                exact (trans n1_max n2_max).
        }
        apply (all_greater_inf_set A).
        {
            exists (a 0).
            exists 0.
            reflexivity.
        }
        intros [x Ax].
        specialize (contr x).
        unfold infinite in contr.
        rewrite nle_lt in contr.
        pose proof (finite_well_ordered_set_max _ contr Ax) as [n n_max].
        pose (y := a (nat_suc n)).
        assert (A y) as Ay by (exists (nat_suc n); reflexivity).
        exists [y|Ay].
        cbn.
        destruct n_max as [n_eq n_max].
        split.
        -   right.
            exists (nat_suc n).
            split.
            +   intros n' n'_eq.
                apply (trans (n_max n' n'_eq)).
                apply nat_le_suc.
            +   reflexivity.
        -   intro eq.
            rewrite eq in *; clear eq.
            assert (a (nat_suc n) = y) as y_eq by reflexivity.
            specialize (n_max _ y_eq).
            clear - n_max.
            rewrite <- nat_lt_suc_le in n_max.
            destruct n_max; contradiction.
    }
    destruct (lt_le_trans A_fin A_inf); contradiction.
Qed.

Definition x := ex_val x_ex.
Definition X n := a n = x.
Lemma x_inf : infinite (|set_type X|).
Proof.
    unfold X, x.
    rewrite_ex_val x x_inf.
    exact x_inf.
Qed.

Lemma x_0 : set_type X.
Proof.
    apply infinite_ex.
    exact x_inf.
Qed.

Lemma n_gt : ∀ n : set_type X, ∃ n', n < n'.
Proof.
    intros [n Xn].
    unfold X in Xn.
    pose proof x_inf as x_inf.
    classic_contradiction contr.
    rewrite not_ex in contr.
    assert (|set_type X| ≤ nat_to_card (nat_suc n)) as leq.
    {
        unfold nat_to_card, le; equiv_simpl.
        assert (∀ x : set_type X, (λ x, x < nat_suc n) [x|]) as x_in.
        {
            intros x.
            specialize (contr x).
            rewrite nlt_le in contr.
            rewrite nat_lt_suc_le.
            apply contr.
        }
        exists (λ x, [_|x_in x]).
        intros x y eq.
        inversion eq as [eq2].
        apply set_type_eq in eq2.
        exact eq2.
    }
    pose proof (nat_is_finite (nat_suc n)) as ltq.
    pose proof (le_lt_trans leq ltq) as ltq2.
    destruct (le_lt_trans x_inf ltq2); contradiction.
Qed.

Fixpoint Xf n := match n with
    | nat_zero => x_0
    | nat_suc n' => ex_val (n_gt (Xf n'))
    end.
Definition f n := [Xf n|].

Lemma x_subseq : subsequence a (λ _, x).
Proof.
    exists f.
    split.
    -   intros n.
        unfold f.
        cbn.
        rewrite_ex_val n' n'_lt.
        split.
        *   apply n'_lt.
        *   intro contr.
            apply set_type_eq in contr.
            destruct n'_lt; contradiction.
    -   intros n.
        unfold f.
        exact [|Xf n].
Qed.

End Finite.

Section Infinite.

Hypothesis A_inf : infinite (|set_type A|).

Definition y := ex_val (U_comp A A_inf).
Lemma y_lim : ∀ S, open S → S y → infinite (|set_type (A ∩ S)|).
Proof.
    apply limit_point_inf.
    unfold y.
    rewrite_ex_val y y_H.
    exact y_H.
Qed.

Lemma b_ex : ∀ n ε, ∃ n', n < n' ∧ open_ball y ε (a n').
Proof.
    intros n ε.
    pose proof (y_lim (open_ball y ε) (open_ball_open y ε) (open_ball_self y ε))
        as ε_inf.
    classic_contradiction contr.
    rewrite not_ex in contr.
    unfold infinite in ε_inf.
    rewrite <- nlt_le in ε_inf.
    apply ε_inf.
    apply (le_lt_trans2 (nat_is_finite (nat_suc n))).
    unfold le, nat_to_card; equiv_simpl.
    assert (∀ x : set_type (A ∩ open_ball y ε),
        ∃ n : nat_to_set_type (nat_suc n), [x|] = a [n|]) as f_ex.
    {
        intros [x [Ax x_lt]]; cbn.
        destruct Ax as [n' x_eq].
        specialize (contr n').
        unfold open_ball in contr.
        rewrite not_and in contr.
        do 2 rewrite nlt_le in contr.
        destruct contr as [contr|contr].
        -   rewrite <- nat_lt_suc_le in contr.
            exists [n'|contr].
            symmetry; exact x_eq.
        -   rewrite <- x_eq in x_lt.
            destruct (le_lt_trans contr x_lt); contradiction.
    }
    exists (λ x, ex_val (f_ex x)).
    intros x y eq.
    rewrite_ex_val n1 x_eq.
    rewrite_ex_val n2 y_eq.
    subst.
    rewrite <- y_eq in x_eq.
    apply set_type_eq.
    exact x_eq.
Qed.

Lemma n_pos : ∀ n, 0 < / from_nat (nat_suc n).
Proof.
    intros n.
    apply div_pos.
    apply from_nat_pos.
Qed.

Fixpoint g n := match n with
    | nat_zero => ex_val (b_ex 0 [_|n_pos 0])
    | nat_suc n' => ex_val (b_ex (g n') [_|n_pos n'])
    end.
Definition b n := a (g n).

Lemma b_subseq : subsequence a b.
Proof.
    exists g.
    split.
    -   intros n.
        cbn.
        rewrite_ex_val n' n'_H.
        exact (land n'_H).
    -   intros n.
        reflexivity.
Qed.

Lemma b_converges : seq_converges b.
Proof.
    exists y.
    intros S S_open Sy.
    rewrite open_all_balls in S_open.
    specialize (S_open y Sy) as [[ε ε_pos] ε_sub].
    pose proof (archimedean2 ε ε_pos) as [N ltq].
    exists (nat_suc N).
    intros n n_geq.
    apply ε_sub.

    pose proof (n_pos N) as N_pos.
    assert ([_|N_pos] ≤ [_|ε_pos]) as leq.
    {
        unfold le; cbn.
        exact (land ltq).
    }
    apply (open_ball_le_sub _ _ _ leq _).
    apply nat_le_ex in n_geq.
    destruct n_geq as [c n_eq].
    subst n.
    rewrite nat_plus_lsuc.
    unfold b.
    cbn.
    rewrite_ex_val n n_H.
    destruct n_H as [n_lt an_in].
    eapply (open_ball_le_sub _ _ _ _ _ an_in).
    Unshelve.
    unfold le; cbn.
    apply le_div_pos.
    -   rewrite <- homo_zero.
        change (1 + from_nat N) with (from_nat (U := real) (nat_suc N)).
        rewrite <- homo_lt2.
        apply nat_pos2.
    -   apply le_lplus.
        rewrite <- homo_le2.
        rewrite <- (plus_rid N) at 1.
        apply le_lplus.
        apply nat_pos.
Qed.

End Infinite.

End Proof.

Lemma limit_point_sequentially_compact : sequentially_compact U.
Proof.
    intros a.
    pose (A x := ∃ n, a n = x).
    classic_case (finite (|set_type A|)) as [A_fin|A_inf].
    -   exists (λ _, x a A_fin).
        split.
        +   apply x_subseq.
        +   apply constant_seq_converges.
    -   unfold finite in A_inf.
        rewrite nlt_le in A_inf.
        exists (b a A_inf).
        split.
        +   apply b_subseq.
        +   apply b_converges.
Qed.

End AnalysisCompact1.
End AnalysisCompact1.

Module AnalysisCompact2.
Section AnalysisCompact2.

Context {U} `{Metric U}.
Hypothesis U_comp : sequentially_compact U.

Section Lebesgue.

Variable SS : (U → Prop) → Prop.
Hypothesis SS_cover : open_covering SS.

Lemma lebesgue_number_lemma : ∃ δ, ∀ x, ∃ S, SS S ∧ open_ball x δ ⊆ S.
Proof.
    classic_contradiction contr.
    rewrite not_ex in contr.
    assert (∀ n, ∃ x, ∀ S, SS S → ¬(open_ball x [_|real_n_div_pos n] ⊆ S))
        as x_ex.
    {
        intros n.
        specialize (contr [_|real_n_div_pos n]).
        rewrite not_all in contr.
        destruct contr as [x contr].
        exists x.
        intros S SS_S.
        rewrite not_ex in contr.
        specialize (contr S).
        rewrite not_and_impl in contr.
        exact (contr SS_S).
    }
    pose (x n := ex_val (x_ex n)).
    specialize (U_comp x) as [x' [x'_sub [a x'_lim]]].
    pose proof (land SS_cover a true) as [S [SS_S Sa]].
    pose proof SS_S as SS_S2.
    apply (rand SS_cover) in SS_S.
    rewrite open_all_balls in SS_S.
    specialize (SS_S a Sa) as [[ε ε_pos] ε_sub].
    pose proof (half_pos ε_pos) as ε2_pos.
    pose proof (archimedean2 (ε / 2) ε2_pos) as [N1 ltq].
    rewrite metric_seq_lim in x'_lim.
    specialize (x'_lim (ε / 2) ε2_pos) as [N2 x'_lim].
    pose (N := max N1 N2).
    destruct x'_sub as [f [f_eq x'_eq]].
    specialize (x'_lim N (rmax _ _)).
    rewrite <- x'_eq in x'_lim.
    unfold x in x'_lim.
    rewrite_ex_val y y_not.
    apply (y_not S SS_S2); clear y_not.
    apply (trans2 ε_sub).
    intros z z_lt.
    unfold open_ball in *; cbn in *.
    assert (/from_nat (nat_suc (f N)) ≤ /from_nat (nat_suc N1))
        as N_ltq.
    {
        apply le_div_pos.
        1:  apply from_nat_pos.
        rewrite <- homo_le2.
        rewrite nat_sucs_le.
        apply (trans (lmax N1 N2)).
        apply subsequence_seq_leq.
        exact f_eq.
    }
    pose proof (trans (lt_le_trans z_lt N_ltq) ltq) as yz_ltq.
    pose proof (lt_lrplus x'_lim yz_ltq) as eq.
    rewrite plus_half in eq.
    apply (le_lt_trans2 eq).
    apply d_tri.
Qed.

End Lebesgue.

Local Open Scope card_scope.

Let to_balls A ε := image_under (λ x, open_ball x ε) A.

Lemma compact_totally_bounded : totally_bounded all.
Proof.
    intros ε.
    classic_contradiction contr.
    rewrite not_ex in contr.
    assert (∀ A, finite (|set_type A|) → ∃ x, ¬((⋃ to_balls A ε) x)) as x_ex.
    {
        intros A A_fin.
        specialize (contr A).
        rewrite not_and_impl in contr.
        specialize (contr A_fin).
        unfold subset in contr.
        rewrite not_all in contr.
        destruct contr as [x contr].
        rewrite not_impl in contr.
        destruct contr as [C0 contr]; clear C0.
        exists x.
        exact contr.
    }
    clear contr.
    assert (∀ (n : nat) (f : set_type (λ x, x < n) → U),
        ∃ x, ¬((⋃ to_balls (image f) ε) x)) as x_ex2.
    {
        intros n nf.
        pose (A := image nf).
        assert (finite (|set_type A|)) as A_fin.
        {
            apply (le_lt_trans2 (nat_is_finite n)).
            unfold le, nat_to_card; equiv_simpl.
            exists (λ x : set_type A, ex_val [|x]).
            intros a b eq.
            revert eq.
            rewrite_ex_val m1 m1_eq.
            rewrite_ex_val m2 m2_eq.
            intros eq.
            rewrite eq in m1_eq.
            rewrite <- m2_eq in m1_eq.
            apply set_type_eq.
            exact m1_eq.
        }
        exact (x_ex A A_fin).
    }
    pose (h n f := ex_val (x_ex2 n f)).
    pose proof (transfinite_recursion U h) as [f f_gt].
    assert (∀ m n, m < n → [ε|] ≤ d (f m) (f n)) as ε_le_wlog.
    {
        intros m n mn.
        rewrite (f_gt n).
        unfold h.
        rewrite_ex_val x x_H; cbn in *.
        rewrite not_ex in x_H.
        specialize (x_H (open_ball (f m) ε)).
        rewrite not_and in x_H.
        destruct x_H as [x_H|x_H].
        -   exfalso.
            apply x_H; clear x_H.
            exists (f m).
            split; try reflexivity.
            exists [m|mn].
            reflexivity.
        -   unfold open_ball in x_H.
            rewrite nlt_le in x_H.
            exact x_H.
    }
    assert (∀ m n, m ≠ n → [ε|] ≤ d (f m) (f n)) as ε_le.
    {
        intros m n mn.
        destruct (trichotomy m n) as [[mn'|mn']|mn'].
        -   exact (ε_le_wlog m n mn').
        -   contradiction (mn mn').
        -   rewrite d_sym.
            exact (ε_le_wlog n m mn').
    }
    clear - ε_le U_comp.
    specialize (U_comp f) as [g [[h [h_sub fg_eq]] [x x_lim]]].
    rewrite metric_seq_lim in x_lim.
    destruct ε as [ε ε_pos]; cbn in ε_le.
    pose proof (half_pos ε_pos) as ε2_pos.
    specialize (x_lim (ε / 2) ε2_pos) as [N x_lim].
    pose proof (x_lim N (refl N)) as ltq1.
    pose proof (x_lim (nat_suc N) (nat_le_suc N)) as ltq2.
    rewrite d_sym in ltq1.
    pose proof (lt_lrplus ltq1 ltq2) as ltq.
    rewrite plus_half in ltq.
    apply (le_lt_trans (d_tri _ _ _)) in ltq.
    do 2 rewrite <- fg_eq in ltq.
    assert (h N ≠ h (nat_suc N)) as neq by apply h_sub.
    specialize (ε_le _ _ neq).
    destruct (le_lt_trans ε_le ltq); contradiction.
Qed.

Theorem sequentially_compact_compact : compact U.
Proof.
    intros SS SS_cover.
    pose proof (lebesgue_number_lemma SS SS_cover) as [[δ δ_pos] δ_leb].
    pose proof (compact_totally_bounded [δ|δ_pos]) as [A [A_fin A_sub]].
    pose (balls := to_balls A [δ|δ_pos]).
    assert (∀ B, balls B → ∃ S, SS S ∧ B ⊆ S) as S_ex.
    {
        intros B [x [Ax B_ball]].
        subst B.
        exact (δ_leb x).
    }
    exists (λ S, ∃ B, S = ex_val (S_ex [B|] [|B])).
    split.
    2:split.
    -   intros S [B S_eq]; subst S.
        rewrite_ex_val S S_H.
        exact (land S_H).
    -   apply (le_lt_trans2 A_fin).
        unfold le; equiv_simpl.
        exists (λ S : set_type (λ S, ∃ B, S = ex_val (S_ex [B|] [|B])),
            [ex_val [|ex_val [|S]] | land (ex_proof [|ex_val [|S]])]).
        intros [S B1_ex] [T B2_ex] eq; cbn in *.
        inversion eq as [eq2]; clear eq.
        apply set_type_eq; cbn.
        rewrite_ex_val a a_H.
        rewrite_ex_val_with [|ex_val B2_ex] b b_H.
        subst b.
        rewrite_ex_val B2 T_eq.
        rewrite_ex_val_with B1_ex B1 S_eq.
        destruct a_H as [Aa B1_eq].
        destruct b_H as [Aa' B2_eq].
        rewrite <- B2_eq in B1_eq.
        apply set_type_eq in B1_eq.
        subst B2.
        rewrite S_eq, T_eq.
        reflexivity.
    -   intros x.
        specialize (A_sub x true) as [B [B_H Bx]].
        exists (ex_val (S_ex B B_H)).
        split.
        +   exists [B|B_H].
            reflexivity.
        +   rewrite_ex_val S S_H.
            apply (rand S_H).
            exact Bx.
Qed.

End AnalysisCompact2.
End AnalysisCompact2.

Section AnalysisCompact.

Context {U} `{Metric U}.
Existing Instance subspace_metric.
(* end hide *)

Theorem metric_limit_point_compact : compact U ↔ limit_point_compact U.
Proof.
    split.
    -   exact compact_limit_point_compact.
    -   intros U_comp.
        apply AnalysisCompact2.sequentially_compact_compact.
        apply AnalysisCompact1.limit_point_sequentially_compact.
        exact U_comp.
Qed.

Theorem metric_sequentially_compact : compact U ↔ sequentially_compact U.
Proof.
    split.
    -   intros U_comp.
        apply AnalysisCompact1.limit_point_sequentially_compact.
        apply compact_limit_point_compact.
        exact U_comp.
    -   exact AnalysisCompact2.sequentially_compact_compact.
Qed.

Theorem lebesgue_number_lemma : compact U → ∀ SS, open_covering SS →
    ∃ δ, ∀ x, ∃ S, SS S ∧ open_ball x δ ⊆ S.
Proof.
    intros U_compact SS SS_cover.
    apply AnalysisCompact2.lebesgue_number_lemma.
    -   apply metric_sequentially_compact.
        exact U_compact.
    -   exact SS_cover.
Qed.

Theorem compact_totally_bounded_all : compact U → totally_bounded all.
Proof.
    intros U_comp.
    apply AnalysisCompact2.compact_totally_bounded.
    apply metric_sequentially_compact.
    exact U_comp.
Qed.

(* begin hide *)
End AnalysisCompact.
Section AnalysisCompact.

Context {U} `{Metric U}.
Existing Instance subspace_metric.

(* end hide *)
Theorem compact_totally_bounded : ∀ X, compact (set_type X) → totally_bounded X.
Proof.
    intros X X_compact.
    apply compact_totally_bounded_all in X_compact.
    intros ε.
    specialize (X_compact ε) as [A [A_fin sub_A]].
    exists (from_set_type A).
    split.
    -   apply (le_lt_trans2 A_fin).
        unfold le; equiv_simpl.
        exists (λ a : set_type (from_set_type A),
            [[[a|] | ldand [|a]] | rdand [|a]]).
        intros a b eq.
        inversion eq as [eq2]; clear eq.
        apply set_type_eq.
        exact eq2.
    -   intros a Xa.
        specialize (sub_A [a|Xa] true).
        destruct sub_A as [S [[x [Ax S_eq]] Sa]].
        subst S.
        exists (open_ball [x|] ε).
        split.
        +   unfold image_under.
            exists [x|].
            split; try reflexivity.
            split with [|x].
            rewrite set_type_simpl.
            exact Ax.
        +   exact Sa.
Qed.

Theorem metric_compact_closed : ∀ X, compact (set_type X) → closed X.
Proof.
    intros X X_comp.
    apply metric_sequentially_compact in X_comp.
    apply closed_limit_points.
    intros x x_lim.
    apply limit_point_seq_ex in x_lim as [f [Xf f_lim]].
    pose (f' n := [f n | land (Xf n)]).
    specialize (X_comp f') as [g' [g'_sub [y g'_lim]]].
    pose (g n := [g' n|]).
    assert (subsequence f g) as g_sub.
    {
        destruct g'_sub as [h [h_sub fg_eq]].
        exists h.
        split; try exact h_sub.
        intros n.
        specialize (fg_eq n).
        unfold f' in fg_eq.
        remember (g' n) as g'n.
        destruct g'n as [g'n g'n_in].
        inversion fg_eq as [eq].
        rewrite eq.
        unfold g.
        rewrite <- Heqg'n.
        reflexivity.
    }
    assert (seq_lim g [y|]) as g_lim.
    {
        unfold g.
        rewrite metric_seq_lim.
        rewrite metric_seq_lim in g'_lim.
        exact g'_lim.
    }
    clear g'_sub g'_lim.
    pose proof (subsequence_lim_eq f g x f_lim g_sub) as g_lim2.
    pose proof (seq_lim_unique g _ _ g_lim g_lim2) as eq.
    rewrite <- eq.
    exact [|y].
Qed.

Theorem metric_compact_closed_all : compact U → closed all.
Proof.
    intros U_comp.
    apply metric_compact_closed.
    rewrite <- metric_subspace_topology.
    apply compact_subspace.
    intros SS SS_cover.
    specialize (U_comp SS SS_cover) as [SS' [SS'_sub [SS'_fin sub_SS']]].
    exists SS'.
    split; try exact SS'_sub.
    split; try exact SS'_fin.
    intros x C0; clear C0.
    apply sub_SS'.
Qed.

Theorem compact_complete : compact U → complete U.
Proof.
    intros U_comp a a_cauchy.
    apply metric_sequentially_compact in U_comp.
    specialize (U_comp a) as [b [ab_sub [x b_lim]]].
    exists x.
    exact (cauchy_subseq_converge a b x a_cauchy ab_sub b_lim).
Qed.
(* begin hide *)

End AnalysisCompact.

Module AnalysisCompact3.
Section AnalysisCompact3.

Context {U} `{Metric U}.
Existing Instance subspace_metric.
Local Open Scope card_scope.

Hypothesis U_comp : complete U.
Variable X : U → Prop.
Hypothesis X_closed : closed X.
Hypothesis X_bound : totally_bounded X.
Variable XS : set_type X → Prop.
Hypothesis XS_inf : infinite (|set_type XS|).

Theorem ball_ex : ∀ S : set_type X → Prop, infinite (|set_type S|) →
    ∀ ε, ∃ x, infinite (|set_type (open_ball x ε ∩ S)|).
Proof.
    clear XS XS_inf.
    intros S S_inf ε.
    pose proof (half_pos [|ε]) as ε2_pos.
    specialize (X_bound [_|ε2_pos]) as [A [A_fin sub_A]].
    pose (A' (a : set_type A) :=
        ∃ x : set_type X, open_ball [a|] [_|ε2_pos] [x|]).
    pose (B x := ∃ a : set_type A', x = ex_val [|a]).
    assert (∀ c, ∃ x, B x ∧ open_ball x ε c) as X_sub.
    {
        intros [c Xc].
        specialize (sub_A c Xc) as [C [[a [Aa C_eq]] Cc]]; subst C.
        unfold B.
        assert (A' [a|Aa]) as A'a.
        {
            exists [c|Xc].
            exact Cc.
        }
        exists (ex_val A'a).
        split.
        -   exists [_|A'a].
            reflexivity.
        -   rewrite_ex_val x x_H; cbn in *.
            unfold open_ball in *; cbn in *.
            rewrite d_sym in x_H.
            pose proof (lt_lrplus x_H Cc) as ltq.
            rewrite plus_half in ltq.
            exact (le_lt_trans (d_tri _ _ _) ltq).
    }
    assert (finite (|set_type B|)) as B_fin.
    {
        apply (le_lt_trans2 A_fin).
        unfold le; equiv_simpl.
        exists (λ x : set_type B, [ex_val [|x]|]).
        intros a b eq.
        apply (land set_type_eq) in eq.
        rewrite_ex_val x a_eq.
        rewrite_ex_val_with [|b] y b_eq.
        subst.
        apply set_type_eq.
        rewrite a_eq, b_eq.
        reflexivity.
    }
    rename B into B'; remember B' as B.
    clear HeqB B' A' sub_A A A_fin.
    rename B into A, B_fin into A_fin.
    pose (B := image_under (λ a, open_ball a ε ∩ S) A).
    assert (S = ⋃ B) as S_eq.
    {
        apply antisym.
        -   intros x Sx.
            specialize (X_sub x) as [y [Ay x_in]].
            exists (open_ball y ε ∩ S).
            split.
            2: split.
            +   exists y.
                split; trivial.
            +   exact x_in.
            +   exact Sx.
        -   intros x [C [[y [Ay C_eq]] Cx]].
            rewrite C_eq in Cx.
            exact (rand Cx).
    }
    classic_contradiction contr.
    rewrite not_ex in contr.
    unfold infinite in S_inf.
    rewrite <- nlt_le in S_inf.
    apply S_inf.
    rewrite S_eq.
    apply finite_union_finite.
    -   apply (le_lt_trans (image_under_le _ _)).
        exact A_fin.
    -   intros C [x [Ax C_eq]].
        subst C.
        specialize (contr x).
        unfold infinite in contr.
        rewrite nle_lt in contr.
        exact contr.
Qed.

Let infs (S : set_type X → Prop) := infinite (|set_type S|).

Fixpoint S n : set_type infs :=
    let Sn :=
        match n with
        | nat_zero => [XS|XS_inf]
        | nat_suc n' => S n'
        end
    in
    let ε := [_|real_n_div_pos n] in
    let bex := ball_ex [Sn|] [|Sn] ε in
    [open_ball (ex_val bex) ε ∩ [Sn|] | ex_proof bex].

Lemma S_sub : ∀ n, [S n|] ⊆ XS.
Proof.
    nat_induction n.
    -   apply inter_rsub.
    -   apply (trans2 IHn).
        apply inter_rsub.
Qed.

Lemma S_sub2 : ∀ m n, m ≤ n → [S n|] ⊆ [S m|].
Proof.
    intros m n leq.
    apply nat_le_ex in leq.
    destruct leq as [c n_eq]; subst n.
    nat_induction c.
    -   rewrite plus_rid.
        apply refl.
    -   apply (trans2 IHc).
        rewrite nat_plus_rsuc.
        apply inter_rsub.
Qed.

Lemma S_bound : ∀ n x y, [S n|] x → [S n|] y →
    d x y ≤ 2 / from_nat (nat_suc n).
Proof.
    intros n x y Snx Sny.
    pose (ε := [_|real_n_div_pos n]).
    pose (Sn :=
        match n with
        | nat_zero => [XS|XS_inf]
        | nat_suc n' => S n'
        end
    ).
    pose (bex := ball_ex [Sn|] [|Sn] ε).
    nat_destruct n.
    -   assert (open_ball (ex_val bex) ε x) as x_in by apply Snx.
        assert (open_ball (ex_val bex) ε y) as y_in by apply Sny.
        unfold open_ball, ε in x_in, y_in; cbn in x_in, y_in.
        rewrite d_sym in x_in.
        pose proof (lt_lrplus x_in y_in) as ltq.
        apply (le_lt_trans (d_tri _ _ _)) in ltq.
        rewrite <- (mult_lid (/from_nat 1)) in ltq.
        rewrite <- rdist in ltq.
        apply ltq.
    -   assert (open_ball (ex_val bex) ε x) as x_in by apply Snx.
        assert (open_ball (ex_val bex) ε y) as y_in by apply Sny.
        unfold open_ball, ε in x_in, y_in; cbn in x_in, y_in.
        rewrite d_sym in x_in.
        pose proof (lt_lrplus x_in y_in) as ltq.
        apply (le_lt_trans (d_tri _ _ _)) in ltq.
        rewrite <- (mult_lid (/from_nat (nat_suc (nat_suc n)))) in ltq.
        rewrite <- rdist in ltq.
        apply ltq.
Qed.

Lemma x_ex : ∀ n, ∃ x, [S n|] x.
Proof.
    intros n.
    pose proof [|S n] as S_inf.
    apply infinite_ex in S_inf.
    destruct S_inf as [x x_in].
    exists x.
    exact x_in.
Qed.

Definition xn n := [ex_val (x_ex n)|].

Lemma xn_cauchy : cauchy_seq xn.
Proof.
    intros ε ε_pos.
    pose proof (half_pos ε_pos) as ε2_pos.
    pose proof (archimedean2 (ε / 2) ε2_pos) as [N N_lt].
    exists N.
    assert (∀ i j, N ≤ i → i ≤ j → d (xn i) (xn j) < ε) as wlog.
    {
        intros i j i_ge ij.
        pose proof (ex_proof (x_ex i)) as Si; cbn in Si.
        pose proof (ex_proof (x_ex j)) as Sj; cbn in Sj.
        pose proof (S_sub2 N i i_ge _ Si) as SNi.
        pose proof (S_sub2 N j (trans i_ge ij) _ Sj) as SNj.
        pose proof (S_bound N _ _ SNi SNj) as leq.
        apply (le_lt_trans leq).
        apply lt_rmult_pos with 2 in N_lt.
        2: exact two_pos.
        rewrite mult_rlinv in N_lt by apply two_pos.
        rewrite mult_comm.
        exact N_lt.
    }
    intros i j i_ge j_ge.
    destruct (connex i j) as [ij|ji].
    -   exact (wlog i j i_ge ij).
    -   rewrite d_sym.
        exact (wlog j i j_ge ji).
Qed.

Definition Ux := ex_val (U_comp xn xn_cauchy).

Lemma x_in : X Ux.
Proof.
    unfold Ux.
    rewrite_ex_val x x_H.
    pose proof X_closed as X_closed2.
    rewrite closed_if_closure in X_closed2.
    rewrite X_closed2; clear X_closed2.
    apply metric_seq_closure.
    exists xn.
    split; try exact x_H.
    intros n.
    unfold xn.
    exact [|ex_val (x_ex n)].
Qed.

Definition x := [Ux|x_in].

Lemma x2_ex : ∀ n, ∃ x2, [S n|] x2 ∧ x2 ≠ x.
Proof.
    intros n.
    pose proof [|S n] as Sn_inf.
    pose proof (infinite_seq_ex Sn_inf) as [f f_neq].
    classic_case ([f 0|] = x) as [x_eq|x_neq].
    -   exists [f 1|].
        split.
        +   exact [|f 1].
        +   intro contr.
            rewrite <- contr in x_eq.
            rewrite set_type_eq in x_eq.
            assert ((zero (U := nat)) ≠ 1) as neq by (intro C; inversion C).
            exact (f_neq 0 1 neq x_eq).
    -   exists [f 0|].
        split.
        +   exact [|f 0].
        +   exact x_neq.
Qed.

Definition xn2 n := ex_val (x2_ex n).

Lemma x2_lim : seq_lim xn2 x.
Proof.
    rewrite metric_seq_lim.
    intros ε ε_pos.
    unfold x, Ux.
    unfold d; cbn.
    rewrite_ex_val x x_lim.
    rewrite metric_seq_lim in x_lim.
    pose proof (half_pos ε_pos) as ε2_pos.
    specialize (x_lim (ε / 2) ε2_pos) as [N1 x_lim].
    pose proof (half_pos ε2_pos) as ε4_pos.
    pose proof (archimedean2 _ ε4_pos) as [N2 N2_eq].
    exists (max N1 N2).
    intros n n_ge.
    specialize (x_lim n (trans (lmax N1 N2) n_ge)).
    assert (X (xn n)) as xn_in by (exact [|ex_val (x_ex n)]).
    pose proof (ex_proof (x_ex n)) as Snx; cbn in Snx.
    pose proof (ex_proof (x2_ex n)) as Snx2; cbn in Snx2.
    pose proof (S_bound n _ _ Snx (land Snx2)) as leq.
    unfold d in leq; cbn in leq.
    change [ex_type_val (ex_to_type (x_ex n))|] with (xn n) in leq.
    change (ex_type_val (ex_to_type (x2_ex n))) with (xn2 n) in leq.
    clear - leq N2_eq n_ge x_lim.
    apply lt_lmult_pos with 2 in N2_eq.
    2: exact two_pos.
    rewrite (mult_comm 2 (ε / 2 / 2)) in N2_eq.
    rewrite mult_rlinv in N2_eq by apply two_pos.
    pose proof (trans (rmax N1 N2) n_ge) as n_ge2.
    rewrite <- nat_sucs_le in n_ge2.
    rewrite homo_le2 in n_ge2.
    apply le_div_pos in n_ge2.
    2: apply from_nat_pos.
    apply le_lmult_pos with 2 in n_ge2.
    2: apply two_pos.
    pose proof (trans leq n_ge2) as leq2.
    pose proof (le_lt_trans leq2 N2_eq) as ltq.
    clear - ltq x_lim.
    pose proof (lt_lrplus x_lim ltq) as eq.
    rewrite plus_half in eq.
    apply (le_lt_trans2 eq).
    apply d_tri.
Qed.

Lemma X_compact : limit_point XS x.
Proof.
    intros T T_open Tx.
    pose proof (x2_lim T T_open Tx) as [N x2_lim].
    specialize (x2_lim N (refl _)).
    apply empty_neq.
    exists (xn2 N).
    revert x2_lim.
    unfold xn2.
    rewrite_ex_val a a_H.
    intros x2_lim.
    destruct a_H as [Sa a_neq].
    repeat split.
    -   apply S_sub in Sa.
        exact Sa.
    -   rewrite singleton_eq.
        rewrite neq_sym.
        exact a_neq.
    -   exact x2_lim.
Qed.

End AnalysisCompact3.

Section AnalysisCompact3.

Context {U} `{Metric U}.
Existing Instance subspace_metric.

Theorem complete_closed_tbounded_compact : complete U → ∀ X,
    closed X → totally_bounded X → compact (set_type X).
Proof.
    intros U_comp X X_closed X_bound.
    apply metric_limit_point_compact.
    intros S S_inf.
    exists (x U_comp X X_closed X_bound S S_inf).
    apply X_compact.
Qed.

End AnalysisCompact3.
End AnalysisCompact3.

Section AnalysisCompact.

Context {U} `{Metric U}.
Existing Instance subspace_metric.
(* end hide *)

Theorem complete_closed_tbounded_compact : complete U → ∀ X,
    closed X → totally_bounded X → compact (set_type X).
Proof.
    intros U_comp X X_closed X_bound.
    apply AnalysisCompact3.complete_closed_tbounded_compact.
    all: assumption.
Qed.
(* begin hide *)
End AnalysisCompact.
(* end hide *)
