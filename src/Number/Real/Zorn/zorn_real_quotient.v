Require Import init.

Require Import zorn_real_zorn.
Require Import zorn_real_analysis.

Require Import polynomial_base.
Require Import linear_grade.
Require Import ring_ideal.

Require Import order_def.
Require Import order_self_abs.
Require Import order_minmax.
Require Import set.
Require Import mult_pow.
Require Import nat_abstract.

Section Quotient.

Let PP := polynomial_plus real_cring.
Let PZ := polynomial_zero real_cring.
Let PN := polynomial_neg real_cring.
Let PPC := polynomial_plus_comm real_cring.
Let PPA := polynomial_plus_assoc real_cring.
Let PPZ := polynomial_plus_lid real_cring.
Let PPN := polynomial_plus_linv real_cring.
Let PM := polynomial_mult real_cring.
Let PO := polynomial_one real_cring.
Let PL := polynomial_ldist real_cring.
Let PMA := polynomial_mult_assoc real_cring.
Let PMC := polynomial_mult_comm real_cring.
Let PMO := polynomial_mult_lid real_cring.
Let PSM := polynomial_scalar real_cring.
Let PSMO := polynomial_scalar_id real_cring.
Let PSML := polynomial_scalar_ldist real_cring.
Let PSMR := polynomial_scalar_rdist real_cring.
Let PSMC := polynomial_scalar_comp real_cring.
Let PML := polynomial_scalar_lmult real_cring.
Let PMR := polynomial_scalar_rmult real_cring.
Let PG := polynomial_grade real_cring.

Local Existing Instances PP PZ PN PPC PPA PPZ PPN PM PO PL PMA PMC PMO PSM PSMO
    PSML PSMR PSMC PML PMR PG.

Theorem top_of_cut_ex_wlog : ∀ (cut : real → Prop) b,
    cut 0 → ¬cut b → (∀ l u, cut u → l <= u → cut l) →
    ∀ δ, 0 < δ → ∃ x, cut x ∧ ¬cut (x + δ).
Proof.
    intros cut b z_in b_nin cut_lt δ δ_pos.
    pose (S n := ¬cut (n × δ)).
    assert (∃ n, S n) as S_ex.
    {
        assert (0 < b) as b_pos.
        {
            classic_contradiction b_neg.
            rewrite nlt_le in b_neg.
            pose proof (cut_lt _ _ z_in b_neg).
            contradiction.
        }
        pose proof (archimedean _ _ b_pos δ_pos) as [n n_gt].
        exists n.
        intros contr.
        pose proof (cut_lt _ _ contr (land n_gt)).
        contradiction.
    }
    pose proof (well_ordered _ S_ex) as [n [Sn n_least]].
    nat_destruct n.
    {
        unfold S in Sn.
        unfold zero in Sn; cbn in Sn.
        contradiction.
    }
    exists (n × δ).
    split.
    -   classic_contradiction contr.
        specialize (n_least n contr).
        rewrite <- nlt_le in n_least.
        apply n_least.
        apply nat_lt_suc.
    -   rewrite plus_comm.
        exact Sn.
Qed.

Variable cut : real → Prop.
Hypothesis cut_in : ∃ a, cut a.
Hypothesis cut_out : ∃ a, ¬cut a.
Hypothesis cut_lt : ∀ l u, cut u → l <= u → cut l.

Definition cut_gt := cut_gt cut cut_lt.
Definition cut_inout := cut_inout cut cut_lt.
Let top_of_cut δ x := cut x ∧ ¬cut (x + δ).
Definition top_of_cut_in := top_of_cut_in cut cut_lt.

Theorem top_of_cut_ex : ∀ δ, 0 < δ → ∃ x, top_of_cut δ x.
    classic_case (cut 0) as [z_in|z_nin].
    -   destruct cut_out as [b b_nin].
        apply (top_of_cut_ex_wlog _ b); try assumption.
    -   pose (cut' x := ¬cut (-x)).
        destruct cut_in as [b b_in].
        pose proof (top_of_cut_ex_wlog cut' (-b)) as wlog.
        prove_parts wlog.
        +   unfold cut'.
            rewrite neg_zero.
            exact z_nin.
        +   unfold cut'.
            rewrite neg_neg, not_not.
            exact b_in.
        +   intros l u u_in lu.
            unfold cut' in *.
            intros l_in.
            apply le_neg in lu.
            pose proof (cut_lt _ _ l_in lu).
            contradiction.
        +   intros δ δ_pos.
            specialize (wlog δ δ_pos) as [x [x_in x_nin]].
            exists (-(x + δ)).
            split.
            *   unfold cut' in x_nin.
                rewrite not_not in x_nin.
                exact x_nin.
            *   unfold cut' in x_in.
                rewrite neg_plus, plus_rlinv.
                exact x_in.
Qed.

Notation "| a |" := (abs a) (at level 30).

Definition zorn_real_ideal_set (c : polynomial real_cring) :=
    ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
        (∀ x, top_of_cut δ x → |polynomial_eval c x| < ε).

Theorem zorn_real_ideal_nempty : ∃ a, zorn_real_ideal_set a.
Proof.
    exists 0.
    intros ε ε_pos.
    exists 1.
    split; [>apply one_pos|].
    intros x x_in.
    rewrite polynomial_eval_zero.
    rewrite <- abs_zero.
    exact ε_pos.
Qed.

Theorem zorn_real_ideal_plus : ∀ a b,
    zorn_real_ideal_set a → zorn_real_ideal_set b → zorn_real_ideal_set (a + b).
Proof.
    intros a b a_in b_in ε ε_pos.
    pose proof (half_pos ε ε_pos) as ε2_pos.
    specialize (a_in _ ε2_pos) as [δ1 [δ1_pos a_in]].
    specialize (b_in _ ε2_pos) as [δ2 [δ2_pos b_in]].
    exists (min δ1 δ2).
    split.
    -   unfold min; case_if; assumption.
    -   intros x [x_cut x_ncut].
        pose proof (lmin δ1 δ2) as δ1_lt.
        pose proof (rmin δ1 δ2) as δ2_lt.
        apply le_lplus with x in δ1_lt.
        apply le_lplus with x in δ2_lt.
        apply (cut_gt _ _ x_ncut) in δ1_lt.
        apply (cut_gt _ _ x_ncut) in δ2_lt.
        specialize (a_in x (make_and x_cut δ1_lt)).
        specialize (b_in x (make_and x_cut δ2_lt)).
        pose proof (lt_lrplus a_in b_in) as eq.
        rewrite plus_half in eq.
        apply (le_lt_trans2 eq).
        rewrite polynomial_eval_plus.
        apply abs_tri.
Qed.

Theorem zorn_real_ideal_lmult : ∀ a b,
    zorn_real_ideal_set b → zorn_real_ideal_set (a * b).
Proof.
    intros f g g_in.
    intros ε ε_pos.
    destruct cut_in as [a a_in].
    destruct cut_out as [b b_out].
    pose proof (polynomial_bounded f (a - 1) b) as [M' M'_max].
    pose (M := max M' 1).
    assert (0 < M) as M_nz.
    {
        unfold M.
        apply (lt_le_trans2 (rmax M' 1)).
        apply one_pos.
    }
    assert (∀ x, a - 1 <= x → x <= b → |polynomial_eval f x| <= M) as M_max.
    {
        intros x ax xb.
        apply (trans (M'_max x ax xb)).
        apply lmax.
    }
    clearbody M.
    clear M' M'_max.
    pose proof (div_pos _ M_nz) as M'_nz.
    specialize (g_in _ (lt_mult _ _ ε_pos M'_nz)) as [δ [δ_pos g_in]].
    exists (min δ 1).
    split.
    -   unfold min; case_if.
        +   exact δ_pos.
        +   exact one_pos.
    -   intros x [x_in x_out].
        specialize (M_max x).
        specialize (g_in x).
        prove_parts M_max.
        {
            rewrite <- le_plus_rrmove.
            pose proof (rmin δ 1) as leq.
            apply le_lplus with x in leq.
            apply (trans2 leq).
            apply cut_inout; assumption.
        }
        {
            apply cut_inout; assumption.
        }
        prove_parts g_in.
        {
            pose proof (lmin δ 1) as leq.
            apply (top_of_cut_in _ _ _ leq).
            split; assumption.
        }
        rewrite polynomial_eval_mult.
        rewrite abs_mult.
        apply (le_rmult_pos (|polynomial_eval g x|)) in M_max.
        2: apply abs_pos.
        apply (lt_lmult_pos M) in g_in.
        2: exact M_nz.
        pose proof (le_lt_trans M_max g_in) as ltq.
        rewrite (mult_comm M) in ltq.
        rewrite mult_rlinv in ltq by apply M_nz.
        exact ltq.
Qed.

Theorem zorn_real_ideal_rmult : ∀ a b,
    zorn_real_ideal_set a → zorn_real_ideal_set (a * b).
Proof.
    intros a b a_in.
    rewrite mult_comm.
    apply zorn_real_ideal_lmult.
    exact a_in.
Qed.

Definition zorn_real_ideal := make_ideal
    zorn_real_ideal_set
    zorn_real_ideal_nempty
    zorn_real_ideal_plus
    zorn_real_ideal_lmult
    zorn_real_ideal_rmult.
Let I := ideal_set zorn_real_ideal.

Definition zorn_real_quotient := quotient_ring zorn_real_ideal.
Definition zorn_real_plus := quotient_ring_plus zorn_real_ideal.
Definition zorn_real_plus_assoc := quotient_ring_plus_assoc zorn_real_ideal.
Definition zorn_real_plus_comm := quotient_ring_plus_comm zorn_real_ideal.
Definition zorn_real_zero := quotient_ring_zero zorn_real_ideal.
Definition zorn_real_plus_lid := quotient_ring_plus_lid zorn_real_ideal.
Definition zorn_real_neg := quotient_ring_neg zorn_real_ideal.
Definition zorn_real_plus_linv := quotient_ring_plus_linv zorn_real_ideal.
Definition zorn_real_mult := quotient_ring_mult zorn_real_ideal.
Definition zorn_real_ldist := quotient_ring_ldist zorn_real_ideal.
Definition zorn_real_rdist := quotient_ring_rdist zorn_real_ideal.
Definition zorn_real_mult_assoc := quotient_ring_mult_assoc zorn_real_ideal.
Definition zorn_real_mult_comm := quotient_ring_mult_comm zorn_real_ideal.
Definition zorn_real_one := quotient_ring_one zorn_real_ideal.
Definition zorn_real_mult_lid := quotient_ring_mult_lid zorn_real_ideal.
Definition zorn_real_mult_rid := quotient_ring_mult_rid zorn_real_ideal.
Existing Instances zorn_real_plus zorn_real_plus_assoc zorn_real_plus_comm
    zorn_real_zero zorn_real_plus_lid zorn_real_neg zorn_real_plus_linv
    zorn_real_mult zorn_real_ldist zorn_real_rdist zorn_real_mult_assoc
    zorn_real_mult_comm zorn_real_one zorn_real_mult_lid zorn_real_mult_rid.

Lemma zorn_real_polynomial_nz : ∀ f, ¬zorn_real_ideal_set f →
    ∃ ε δ, 0 < ε ∧ 0 < δ ∧
    (∀ x, top_of_cut δ x → ε < |polynomial_eval f x|).
Proof.
    intros f f_nin.
    unfold zorn_real_ideal_set in f_nin.
    rewrite not_all in f_nin.
    destruct f_nin as [ε f_nin].
    rewrite not_impl, not_ex in f_nin.
    destruct f_nin as [ε_pos f_nin].
    setoid_rewrite not_and_impl in f_nin.
    setoid_rewrite not_all in f_nin.

    pose proof (half_pos ε ε_pos) as ε2_pos.
    exists (ε / 2).
    pose proof (polynomial_continuous cut cut_in cut_out cut_lt f _ ε2_pos)
        as [δ2 [δ2_pos f_cont]].
    classic_contradiction contr.
    rewrite not_ex in contr.
    specialize (contr δ2).
    rewrite not_and_impl in contr.
    rewrite not_and_impl in contr.
    rewrite not_all in contr.
    specialize (contr ε2_pos δ2_pos) as [x contr].
    rewrite not_impl in contr.
    destruct contr as [x_in x_lt].
    rewrite nlt_le in x_lt.
    specialize (f_nin δ2 δ2_pos) as [y f_nin].
    rewrite not_impl in f_nin.
    destruct f_nin as [y_in y_ge].
    rewrite nlt_le in y_ge.
    specialize (f_cont x y x_in y_in).
    remember (polynomial_eval f x) as fx.
    remember (polynomial_eval f y) as fy.
    clear - f_cont x_lt y_ge.

    apply le_neg in x_lt.
    pose proof (le_lrplus y_ge x_lt) as leq.
    rewrite <- (plus_half ε) in leq at 1.
    rewrite plus_rrinv in leq.
    pose proof (lt_le_trans f_cont leq) as ltq.
    apply (le_lt_trans (abs_reverse_tri fx fy)) in ltq.
    rewrite <- nle_lt in ltq.
    rewrite abs_minus in ltq.
    specialize (ltq (abs_le_pos _)).
    exact ltq.
Qed.

Lemma zorn_real_quotient_domain : ∀ a b : zorn_real_quotient,
    0 = a * b → 0 = a ∨ 0 = b.
Proof.
    intros a b.
    assert (∀ c, (0 = c) ↔ (c = 0)) as stupid.
    {
        intros c.
        split; intro; symmetry; assumption.
    }
    do 3 rewrite stupid; clear stupid.
    equiv_get_value a b.
    unfold zero, mult; equiv_simpl.
    pose (stupid a := equiv_eq (E := ideal_equiv zorn_real_ideal) a 0).
    do 3 rewrite stupid; clear stupid.
    cbn.
    rewrite neg_zero.
    do 3 rewrite plus_rid.
    intros ab.
    classic_case (zorn_real_ideal_set a) as [a_in|a_nin]; [>left; exact a_in|].
    right.

    intros ε ε_pos.
    pose proof (zorn_real_polynomial_nz a a_nin)
        as [ε' [δ1 [ε'_pos [δ1_pos a_gt]]]].
    unfold zorn_real_ideal_set in ab.
    specialize (ab _ (lt_mult _ _ ε'_pos ε_pos)) as [δ2 [δ2_pos ab]].
    exists (min δ1 δ2).
    split; [>unfold min; case_if; assumption|].
    intros x x_in.
    pose proof (top_of_cut_in _ _ _ (lmin _ _) x_in) as x_in1.
    pose proof (top_of_cut_in _ _ _ (rmin _ _) x_in) as x_in2.
    specialize (a_gt _ x_in1).
    specialize (ab _ x_in2).
    rewrite polynomial_eval_mult in ab.
    rewrite abs_mult in ab.
    remember (polynomial_eval a x) as ax.
    remember (polynomial_eval b x) as bx.
    clear - a_gt ab ε_pos ε'_pos.
    classic_case (0 = |bx|) as [bx_z|bx_nz].
    {
        rewrite <- bx_z.
        exact ε_pos.
    }
    apply lt_rmult_pos with (|bx|) in a_gt;
        [>|split; [>apply abs_pos|exact bx_nz]].
    pose proof (trans a_gt ab) as ltq.
    apply lt_mult_lcancel_pos in ltq; [>|exact ε'_pos].
    exact ltq.
Qed.
Local Program Instance zorn_real_mult_lcancel : MultLcancel zorn_real_quotient.
Next Obligation.
    rename H into c_nz.
    assert (c * a = c * b) as eq by (apply set_type_eq; exact H2).
    rewrite <- plus_0_anb_a_b in eq.
    rewrite <- mult_rneg in eq.
    rewrite <- ldist in eq.
    apply zorn_real_quotient_domain in eq as [c_z|ab_z].
    -   contradiction.
    -   rewrite plus_0_anb_a_b in ab_z.
        exact ab_z.
Qed.


Definition zorn_real_q_pos (a : polynomial real_cring) :=
    ∃ δ, 0 < δ ∧ ∀ x, top_of_cut δ x → 0 < polynomial_eval a x.

Definition zorn_real_q_le (a b : polynomial real_cring) :=
    zorn_real_q_pos (b - a) ∨ I (b - a).

Lemma zorn_real_q_le_trans_wlog : ∀ f g,
    zorn_real_q_pos f → I g → zorn_real_q_pos (f + g) ∨ I (f + g).
Proof.
    intros f g f_in g_in.
    classic_case (I f) as [f_in'|f_nin].
    {
        right.
        apply ideal_plus; assumption.
    }
    left.
    cbn in g_in, f_nin.
    destruct f_in as [δ1 [δ1_pos f_in]].
    pose proof (zorn_real_polynomial_nz f f_nin) as [ε [δ3 [ε_pos [δ3_pos f_pos]]]].
    specialize (g_in _ ε_pos) as [δ4 [δ4_pos g_in]].
    exists (min δ1 (min δ3 δ4)).
    split; [>unfold min; repeat case_if; assumption|].
    intros x x_in.
    assert (top_of_cut δ1 x) as x_in1.
    {
        eapply (top_of_cut_in _ _ _ _ x_in).
        Unshelve.
        apply lmin.
    }
    assert (top_of_cut δ3 x) as x_in3.
    {
        eapply (top_of_cut_in _ _ _ _ x_in).
        Unshelve.
        apply (trans (rmin _ _)).
        apply lmin.
    }
    assert (top_of_cut δ4 x) as x_in4.
    {
        eapply (top_of_cut_in _ _ _ _ x_in).
        Unshelve.
        apply (trans (rmin _ _)).
        apply rmin.
    }
    specialize (f_in x x_in1).
    specialize (f_pos x x_in3).
    specialize (g_in x x_in4).
    rewrite polynomial_eval_plus.
    remember (polynomial_eval f x) as fx.
    remember (polynomial_eval g x) as gx.
    clear - f_in f_pos g_in.
    rewrite abs_lt in g_in.
    destruct g_in as [g_gt g_lt].
    rewrite (abs_pos_eq _ (land f_in)) in f_pos.
    pose proof (lt_lrplus f_pos g_gt) as ltq.
    rewrite plus_rinv in ltq.
    exact ltq.
Qed.

Theorem zorn_real_q_le_trans : ∀ {x y z},
    zorn_real_q_le x y → zorn_real_q_le y z → zorn_real_q_le x z.
Proof.
    intros x y z xy yz.
    unfold zorn_real_q_le in *.
    remember (y - x) as f.
    remember (z - y) as g.
    assert (z - x = f + g) as eq.
    {
        rewrite (plus_comm f g).
        rewrite Heqf, Heqg.
        rewrite plus_assoc.
        rewrite plus_rlinv.
        reflexivity.
    }
    rewrite eq.
    clear eq x y z Heqf Heqg.
    destruct xy as [xy|xy], yz as [yz|yz].
    -   left.
        unfold zorn_real_q_pos in *.
        destruct xy as [δ1 [δ1_pos xy]].
        destruct yz as [δ2 [δ2_pos yz]].
        exists (min δ1 δ2).
        split; [>unfold min; case_if; assumption|].
        intros a a_in.
        specialize (xy a (top_of_cut_in _ _ _ (lmin _ _) a_in)).
        specialize (yz a (top_of_cut_in _ _ _ (rmin _ _) a_in)).
        pose proof (lt_lrplus xy yz) as ltq.
        rewrite polynomial_eval_plus.
        rewrite plus_lid in ltq.
        exact ltq.
    -   apply zorn_real_q_le_trans_wlog; assumption.
    -   rewrite plus_comm.
        apply zorn_real_q_le_trans_wlog; assumption.
    -   right.
        apply ideal_plus; assumption.
Qed.

Local Infix "~" := (eq_equal (ideal_equiv zorn_real_ideal)).

Lemma real_zorn_quotient_eq_le : ∀ a b, a ~ b → zorn_real_q_le a b.
    intros a b ab.
    right.
    apply ideal_eq_symmetric in ab.
    exact ab.
Qed.

Lemma real_zorn_quotient_le_wd1 : ∀ a b c d, a ~ b → c ~ d →
    zorn_real_q_le a c → zorn_real_q_le b d.
Proof.
    intros a b c d ab cd ac.
    apply ideal_eq_symmetric in ab.
    pose proof (real_zorn_quotient_eq_le b a ab) as ab2.
    pose proof (zorn_real_q_le_trans ab2 ac) as bc.
    pose proof (real_zorn_quotient_eq_le c d cd) as cd2.
    exact (zorn_real_q_le_trans bc cd2).
Qed.

Lemma real_zorn_quotient_le_wd : ∀ a b c d, a ~ b → c ~ d →
    (zorn_real_q_le a c) = (zorn_real_q_le b d).
Proof.
    intros a b c d ab cd.
    apply propositional_ext.
    split; [>apply real_zorn_quotient_le_wd1; assumption|].
    intros bd.
    apply ideal_eq_symmetric in ab, cd.
    exact (real_zorn_quotient_le_wd1 _ _ _ _ ab cd bd).
Qed.

Local Instance zorn_real_order : Order zorn_real_quotient := {
    le := binary_op real_zorn_quotient_le_wd;
}.

Local Program Instance zorn_real_order_le_connex : Connex le.
Next Obligation.
    equiv_get_value x y.
    unfold le; equiv_simpl.
    unfold zorn_real_q_le.
    rewrite <- (neg_neg (y - x)).
    rewrite neg_plus, neg_neg.
    rewrite (plus_comm _ x).
    remember (x - y) as f.
    clear x y Heqf.
    apply or_to_strong.
    classic_case (zorn_real_q_pos (-f)) as [f'_pos|f'_neg].
    1: left; left; exact f'_pos.
    classic_case (zorn_real_q_pos f) as [f_pos|f_neg].
    1: right; left; exact f_pos.
    right; right.
    unfold zorn_real_q_pos in *.

    intros ε ε_pos.
    pose proof (polynomial_continuous cut cut_in cut_out cut_lt f ε ε_pos)
        as [δ [δ_pos f_cont]].
    rewrite not_ex in f_neg, f'_neg.
    setoid_rewrite not_and_impl in f_neg.
    setoid_rewrite not_and_impl in f'_neg.
    specialize (f_neg δ δ_pos).
    specialize (f'_neg δ δ_pos).
    exists δ.
    split; [>exact δ_pos|].
    intros x x_in.
    unfold abs; case_if.
    -   rewrite not_all in f_neg.
        destruct f_neg as [y f_neg].
        rewrite not_impl, nlt_le in f_neg.
        destruct f_neg as [y_in y_neg].
        specialize (f_cont x y x_in y_in).
        remember (polynomial_eval f x) as fx.
        remember (polynomial_eval f y) as fy.
        clear - y_neg l f_cont.
        apply neg_pos in y_neg.
        pose proof (le_lrplus l y_neg) as pos.
        rewrite plus_lid in pos.
        rewrite (abs_pos_eq _ pos) in f_cont.
        apply le_lplus with fx in y_neg.
        rewrite plus_rid in y_neg.
        exact (le_lt_trans y_neg f_cont).
    -   rewrite not_all in f'_neg.
        destruct f'_neg as [y f'_neg].
        rewrite not_impl, nlt_le in f'_neg.
        destruct f'_neg as [y_in y_neg].
        specialize (f_cont y x y_in x_in).
        rewrite polynomial_eval_neg in y_neg.
        remember (polynomial_eval f x) as fx.
        remember (polynomial_eval f y) as fy.
        clear - y_neg n f_cont.
        rewrite nle_lt in n.
        apply neg_pos in y_neg.
        rewrite neg_neg in y_neg.
        destruct n as [l n].
        apply neg_pos in l.
        pose proof (le_lrplus y_neg l) as pos.
        rewrite plus_lid in pos.
        rewrite (abs_pos_eq _ pos) in f_cont.
        apply le_lplus with (-fx) in y_neg.
        rewrite plus_rid in y_neg.
        rewrite plus_comm in y_neg.
        exact (le_lt_trans y_neg f_cont).
Qed.

Local Program Instance zorn_real_order_le_antisym : Antisymmetric le.
Next Obligation.
    revert H H0.
    equiv_get_value x y.
    unfold le; equiv_simpl.
    pose (stupid := equiv_eq (E := ideal_equiv zorn_real_ideal)).
    rewrite stupid; clear stupid.
    intros xy yx.
    destruct xy as [xy|xy].
    2: {
        apply ideal_eq_symmetric.
        exact xy.
    }
    destruct yx as [yx|yx].
    2: exact yx.
    cbn.
    rewrite <- neg_neg in xy.
    rewrite neg_plus, neg_neg, plus_comm in xy.
    remember (x - y) as f.
    rewrite <- Heqf.
    clear Heqf x y.
    intros ε ε_pos.
    unfold zorn_real_q_pos in xy, yx.
    destruct xy as [δ1 [δ1_pos xy]].
    destruct yx as [δ2 [δ2_pos yx]].
    exists (min δ1 δ2).
    split; [>unfold min; case_if; assumption|].
    intros x x_in.
    specialize (xy x (top_of_cut_in _ _ _ (lmin _ _) x_in)).
    specialize (yx x (top_of_cut_in _ _ _ (rmin _ _) x_in)).
    rewrite polynomial_eval_neg in xy.
    apply pos_neg2 in yx.
    destruct (trans xy yx); contradiction.
Qed.

Local Program Instance zorn_real_order_le_trans : Transitive le.
Next Obligation.
    revert H H0.
    equiv_get_value x y z.
    unfold le; equiv_simpl.
    apply zorn_real_q_le_trans.
Qed.

Local Program Instance zorn_real_order_le_lplus : OrderLplus zorn_real_quotient.
Next Obligation.
    revert H.
    equiv_get_value a b c.
    unfold le, plus; equiv_simpl.
    unfold zorn_real_q_le.
    rewrite (plus_comm c b).
    rewrite neg_plus.
    rewrite plus_assoc.
    rewrite plus_rrinv.
    intros H; exact H.
Qed.

Local Program Instance zorn_real_order_le_mult : OrderMult zorn_real_quotient.
Next Obligation.
    classic_case (a = 0) as [a_z|a_nz].
    {
        rewrite a_z.
        rewrite mult_lanni.
        apply refl.
    }
    classic_case (b = 0) as [b_z|b_nz].
    {
        rewrite b_z.
        rewrite mult_ranni.
        apply refl.
    }
    revert H H0 a_nz b_nz.
    equiv_get_value a b.
    unfold zero, mult, le; equiv_simpl.
    pose (stupid := equiv_eq (E := ideal_equiv zorn_real_ideal)).
    do 2 rewrite stupid; clear stupid.
    intros a_pos b_pos a_nz b_nz.
    destruct a_pos as [a_pos|]; [>|contradiction].
    destruct b_pos as [b_pos|]; [>|contradiction].
    rewrite neg_zero, plus_rid in a_pos, b_pos.
    left.
    destruct a_pos as [δ1 [δ1_pos a_pos]].
    destruct b_pos as [δ2 [δ2_pos b_pos]].
    exists (min δ1 δ2).
    split; [>unfold min; case_if; assumption|].
    intros x x_in.
    rewrite neg_zero, plus_rid.
    rewrite polynomial_eval_mult.
    specialize (a_pos _ (top_of_cut_in _ _ _ (lmin _ _) x_in)).
    specialize (b_pos _ (top_of_cut_in _ _ _ (rmin _ _) x_in)).
    exact (lt_mult _ _ a_pos b_pos).
Qed.

Local Program Instance zorn_real_order_le_mult_lcancel : OrderMultLcancel zorn_real_quotient.
Next Obligation.
    destruct H as [c_pos c_nz].
    rewrite neq_sym in c_nz.
    revert c_pos c_nz H0.
    equiv_get_value a b c.
    unfold zero, mult, le; equiv_simpl.
    pose (stupid := equiv_eq (E := ideal_equiv zorn_real_ideal)).
    rewrite stupid; clear stupid.
    intros c_pos c_nz.
    unfold zorn_real_q_le.
    rewrite <- mult_rneg.
    rewrite <- ldist.
    remember (b - a) as f.
    clear Heqf a b.
    intros cf.
    destruct c_pos as [c_pos|c_z]; [>|contradiction].
    cbn in c_nz.
    rewrite neg_zero, plus_rid in c_pos, c_nz.
    destruct cf as [cf|cf].
    -   left.
        destruct c_pos as [δ1 [δ1_pos c_pos]].
        destruct cf as [δ2 [δ2_pos cf_pos]].
        exists (min δ1 δ2).
        split; [>unfold min; case_if; assumption|].
        intros x x_in.
        specialize (c_pos _ (top_of_cut_in _ _ _ (lmin _ _) x_in)).
        specialize (cf_pos _ (top_of_cut_in _ _ _ (rmin _ _) x_in)).
        rewrite polynomial_eval_mult in cf_pos.
        remember (polynomial_eval c x) as cx.
        remember (polynomial_eval f x) as fx.
        clear - c_pos cf_pos.
        rewrite <- (mult_ranni cx) in cf_pos.
        apply lt_mult_lcancel_pos in cf_pos; assumption.
    -   right.
        assert (∀ x, 0 = to_equiv_type (ideal_equiv zorn_real_ideal) x ↔ I x)
            as z_eq.
        {
            intros x.
            split; intros eq.
            -   symmetry in eq.
                unfold zero in eq; equiv_simpl in eq.
                rewrite neg_zero, plus_rid in eq.
                exact eq.
            -   symmetry.
                unfold zero; equiv_simpl.
                rewrite neg_zero, plus_rid.
                exact eq.
        }
        classic_contradiction contr.
        apply (mult_nz (to_equiv_type (ideal_equiv zorn_real_ideal) c)
                       (to_equiv_type (ideal_equiv zorn_real_ideal) f)).
        3: unfold mult; equiv_simpl.
        all: rewrite z_eq.
        all: assumption.
Qed.

Local Program Instance zorn_real_quotient_not_trivial
    : NotTrivial zorn_real_quotient :=
{
    not_trivial_a := 0;
    not_trivial_b := 1;
}.
Next Obligation.
    unfold zero, one; cbn.
    intros contr.
    pose (stupid := equiv_eq (E := ideal_equiv zorn_real_ideal)).
    apply stupid in contr; clear stupid.
    apply ideal_eq_symmetric in contr.
    rewrite neg_zero, plus_rid in contr.
    specialize (contr 1 one_pos) as [δ [δ_pos contr]].
    pose proof (top_of_cut_ex δ δ_pos) as [x x_in].
    specialize (contr x x_in).
    rewrite polynomial_eval_xn in contr.
    rewrite pow_0_nat in contr.
    rewrite abs_one in contr.
    destruct contr; contradiction.
Qed.

Lemma real_zorn_quotient_arch1 : ∀ x y : zorn_real_quotient, 0 < x → 0 < y →
    ∃ n, x <= n × y.
Proof.
    intros f g f_pos g_pos.
    destruct f_pos as [f_pos f_nz].
    destruct g_pos as [g_pos g_nz].
    rewrite neq_sym in f_nz, g_nz.
    equiv_get_value f g.
    revert f_pos f_nz g_pos g_nz.
    unfold zero, le; equiv_simpl.
    pose (stupid := equiv_eq (E := ideal_equiv zorn_real_ideal)).
    do 2 rewrite stupid.
    intros f_pos f_nz g_pos g_nz.
    destruct f_pos as [f_pos|f_z]; [>|contradiction].
    destruct g_pos as [g_pos|g_z]; [>|contradiction].
    cbn in f_nz, g_nz.
    rewrite neg_zero, plus_rid in f_pos, f_nz, g_pos, g_nz.
    pose proof (zorn_real_polynomial_nz g g_nz)
        as [ε [δ1 [ε_pos [δ1_pos g_gt]]]].
    pose proof (polynomial_continuous cut cut_in cut_out cut_lt f 1 one_pos)
        as [δ2 [δ2_pos f_cont]].
    destruct g_pos as [δ3 [δ3_pos g_pos]].
    destruct f_pos as [δ4 [δ4_pos f_pos]].
    pose (δ := min (min δ1 δ2) (min δ3 δ4)).
    assert (0 < δ) as δ_pos.
    {
        unfold δ, min; repeat case_if; assumption.
    }
    pose proof (top_of_cut_ex δ δ_pos) as [x x_in].
    pose proof (archimedean (polynomial_eval f x + 1) ε) as n_ex.
    assert (δ <= δ1) as δ_le1 by (apply (trans (lmin _ _)); apply lmin).
    assert (δ <= δ2) as δ_le2 by (apply (trans (lmin _ _)); apply rmin).
    assert (δ <= δ3) as δ_le3 by (apply (trans (rmin _ _)); apply lmin).
    assert (δ <= δ4) as δ_le4 by (apply (trans (rmin _ _)); apply rmin).
    prove_parts n_ex.
    {
        rewrite <- (plus_lid 0).
        apply lt_lrplus; [>|exact one_pos].
        apply f_pos.
        exact (top_of_cut_in _ _ _ δ_le4 x_in).
    }
    1: exact ε_pos.
    destruct n_ex as [n n_ltq].
    exists n.
    assert (n × to_equiv_type (ideal_equiv zorn_real_ideal) g =
        to_equiv_type (ideal_equiv zorn_real_ideal) (n × g)) as n_eq.
    {
        clear.
        nat_induction n.
        -   unfold zero; cbn.
            reflexivity.
        -   cbn.
            rewrite IHn.
            unfold plus at 1; equiv_simpl.
            reflexivity.
    }
    rewrite n_eq; clear n_eq.
    equiv_simpl.
    left.
    exists δ.
    split; [>exact δ_pos|].
    intros y y_in.
    specialize (f_cont y x (top_of_cut_in _ _ _ δ_le2 y_in)
                           (top_of_cut_in _ _ _ δ_le2 x_in)).
    apply (le_lt_trans (abs_le_pos _)) in f_cont.
    rewrite lt_plus_llmove in n_ltq.
    apply (trans f_cont) in n_ltq.
    rewrite plus_comm in n_ltq.
    apply lt_plus_lcancel in n_ltq.
    specialize (g_gt y (top_of_cut_in _ _ _ δ_le1 y_in)).
    specialize (g_pos y (top_of_cut_in _ _ _ δ_le3 y_in)).
    rewrite abs_pos_eq in g_gt by apply g_pos.
    rewrite <- nat_to_abstract_mult_abstract in n_ltq.
    destruct g_gt as [g_ge g_neq]; clear g_neq.
    apply (le_lmult_pos (nat_to_abstract n)) in g_ge.
    2: {
        (* TODO: Make this a new theorem *)
        nat_destruct n.
        -   rewrite nat_to_abstract_zero.
            apply refl.
        -   apply nat_to_abstract_pos.
    }
    apply (lt_le_trans2 g_ge) in n_ltq.
    rewrite polynomial_eval_plus, polynomial_eval_neg.
    rewrite lt_plus_0_anb_b_a.
    applys_eq n_ltq.
    rewrite <- nat_to_abstract_mult_abstract.
    rewrite polynomial_eval_mult.
    apply rmult.
    clear.
    nat_induction n.
    -   do 2 rewrite nat_to_abstract_zero.
        apply polynomial_eval_zero.
    -   cbn.
        rewrite polynomial_eval_plus.
        rewrite polynomial_eval_xn.
        rewrite pow_0_nat.
        rewrite IHn.
        reflexivity.
Qed.

Local Program Instance zorn_real_quotient_arch : Archimedean zorn_real_quotient.
Next Obligation.
    pose proof (real_zorn_quotient_arch1 x y H H0) as [n n_ge].
    exists (nat_suc n).
    cbn.
    apply (lt_rplus (n × y)) in H0.
    rewrite plus_lid in H0.
    exact (le_lt_trans n_ge H0).
Qed.

End Quotient.
