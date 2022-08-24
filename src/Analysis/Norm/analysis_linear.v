Require Import init.

Require Import order_minmax.

Require Export analysis_norm.
Require Import topology_continuous.

(* begin hide *)
Section AnalysisLinear.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,

    USM : ScalarMult real U,
    @ScalarId real U real_one USM,
    @ScalarLdist real U UP USM,
    @ScalarRdist real U real_plus UP USM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP,
    @AbsPositive U UA,
    @AbsScalar U UA USM,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    VSM : ScalarMult real V,
    @ScalarId real V real_one VSM,
    @ScalarLdist real V VP VSM,
    @ScalarRdist real V real_plus VP VSM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsScalar V VA VSM
}.
Existing Instance abs_metric.

(* end hide *)
(** Yes, I know [ModuleObjHomomorphism] is already just this, but that requires
[ModuleObj]s whereas this just requires a few typeclasses.
*)
Record linear_map := make_linear_map {
    linear_map_f : U → V;
    linear_map_scalar : ∀ a v, linear_map_f (a · v) = a · linear_map_f v;
    linear_map_plus : ∀ u v,
        linear_map_f (u + v) = linear_map_f u + linear_map_f v;
}.

Theorem linear_map_eq : ∀ f g : linear_map,
    (∀ x, linear_map_f f x = linear_map_f g x) → f = g.
Proof.
    intros [f f_scalar f_plus] [g g_scalar g_plus] eq.
    cbn in *.
    assert (f = g) as eq'.
    {
        apply functional_ext.
        exact eq.
    }
    subst g.
    rewrite (proof_irrelevance f_scalar g_scalar).
    rewrite (proof_irrelevance f_plus g_plus).
    reflexivity.
Qed.

Theorem linear_map_zero : ∀ f : linear_map, linear_map_f f 0 = 0.
Proof.
    intros f.
    rewrite <- (scalar_lanni 0).
    rewrite linear_map_scalar.
    apply scalar_lanni.
Qed.

Theorem linear_map_neg : ∀ f : linear_map, ∀ x,
    linear_map_f f (-x) = -linear_map_f f x.
Proof.
    intros f x.
    rewrite <- scalar_neg_one.
    rewrite linear_map_scalar.
    apply scalar_neg_one.
Qed.

Lemma zero_linear_map_scalar : ∀ a (v : U), 0 = a · 0.
Proof.
    intros a v.
    rewrite scalar_ranni.
    reflexivity.
Qed.
Lemma zero_linear_map_plus : ∀ (u v : U), 0 = 0 + 0.
Proof.
    intros a v.
    rewrite plus_lid.
    reflexivity.
Qed.

Definition zero_linear_map
    := make_linear_map (λ _, 0) zero_linear_map_scalar zero_linear_map_plus.

Lemma plus_linear_map_scalar (f g : linear_map) : ∀ a v,
    linear_map_f f (a · v) + linear_map_f g (a · v) =
    a · (linear_map_f f v + linear_map_f g v).
Proof.
    intros a v.
    do 2 rewrite linear_map_scalar.
    rewrite scalar_ldist.
    reflexivity.
Qed.
Lemma plus_linear_map_plus (f g : linear_map) : ∀ u v,
    linear_map_f f (u + v) + linear_map_f g (u + v) =
    (linear_map_f f u + linear_map_f g u) + (linear_map_f f v + linear_map_f g v).
Proof.
    intros u v.
    do 2 rewrite linear_map_plus.
    do 2 rewrite <- plus_assoc.
    apply lplus.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply plus_comm.
Qed.

Definition plus_linear_map (f g : linear_map)
    := make_linear_map (λ x, linear_map_f f x + linear_map_f g x)
        (plus_linear_map_scalar f g) (plus_linear_map_plus f g).

Definition bounded_linear_map (f : linear_map)
    := ∃ M : real, ∀ x : U, |linear_map_f f x| <= M * |x|.

Theorem zero_linear_bounded : bounded_linear_map zero_linear_map.
Proof.
    exists 0.
    intros x.
    cbn.
    rewrite <- abs_zero.
    rewrite mult_lanni.
    apply refl.
Qed.

Theorem plus_linear_bounded : ∀ f g : set_type bounded_linear_map,
    bounded_linear_map (plus_linear_map [f|] [g|]).
Proof.
    intros [f [M M_bound]] [g [N N_bound]]; cbn.
    unfold bounded_linear_map; cbn.
    exists (M + N).
    intros x.
    apply (trans (abs_tri _ _)).
    rewrite rdist.
    apply le_lrplus.
    -   apply M_bound.
    -   apply N_bound.
Qed.

Definition linear_map_bound_set (f : linear_map) (x : real)
    := x = 0 ∨ ∃ u, |linear_map_f f u| = x ∧ |u| = 1.

Theorem operator_norm_ex :
    ∀ f, bounded_linear_map f → has_supremum le (linear_map_bound_set f).
Proof.
    intros f [A fA].
    apply sup_complete.
    -   exists 0.
        left.
        reflexivity.
    -   classic_case (∀ x : U, 0 = x) as [all_z|nz].
        +   exists 0.
            intros x [x0|[u [x_eq u1]]].
            *   rewrite x0.
                apply refl.
            *   rewrite <- (all_z u) in u1.
                rewrite <- abs_zero in u1.
                apply not_trivial_one in u1.
                contradiction.
        +   exists A.
            intros x [x0|[u [x_eq u1]]].
            *   subst x.
                rewrite not_all in nz.
                destruct nz as [a a_nz].
                specialize (fA a).
                assert (0 ≠ |a|) as a_nz'.
                {
                    intros contr.
                    rewrite abs_def in contr.
                    contradiction.
                }
                apply le_mult_rrmove_pos in fA.
                2: split; [>apply abs_pos|exact a_nz'].
                apply (trans2 fA).
                apply le_mult.
                --  apply abs_pos.
                --  apply div_pos.
                    split; [>apply abs_pos|exact a_nz'].
            *   subst x.
                specialize (fA u).
                rewrite u1 in fA.
                rewrite mult_rid in fA.
                exact fA.
Qed.

Definition operator_norm (f : linear_map) (H : bounded_linear_map f)
    := ex_val (operator_norm_ex f H).

Theorem operator_norm_bound : ∀ f H, ∀ x,
    |linear_map_f f x| <= operator_norm f H * |x|.
Proof.
    intros f f_bound x.
    unfold operator_norm.
    rewrite_ex_val A [A_bound A_least].
    classic_case (0 = x) as [x_z|x_nz].
    {
        subst x.
        rewrite linear_map_zero.
        do 2 rewrite <- abs_zero.
        rewrite mult_ranni.
        apply refl.
    }
    assert (0 ≠ |x|) as x_nz'.
    {
        intros contr.
        rewrite abs_def in contr.
        contradiction.
    }
    specialize (A_bound (|linear_map_f f x| / |x|)).
    prove_parts A_bound.
    {
        right.
        exists (/|x| · x).
        split.
        -   rewrite linear_map_scalar.
            rewrite abs_scalar.
            rewrite mult_comm.
            rewrite <- abs_div by exact x_nz'.
            rewrite abs_abs.
            reflexivity.
        -   rewrite abs_scalar.
            rewrite <- abs_div by exact x_nz'.
            rewrite abs_abs.
            apply mult_linv.
            exact x_nz'.
    }
    rewrite <- le_mult_rrmove_pos in A_bound.
    2: split; [>apply abs_pos|exact x_nz'].
    exact A_bound.
Qed.

Theorem operator_norm_pos : ∀ f H, 0 <= operator_norm f H.
Proof.
    intros f f_bound.
    unfold operator_norm.
    rewrite_ex_val A [A_bound A_least].
    apply A_bound.
    left.
    reflexivity.
Qed.

Theorem operator_norm_zero : ∀ f H, 0 = operator_norm f H →
    ∀ x, 0 = linear_map_f f x.
Proof.
    intros f f_bound A_eq x.
    pose proof (operator_norm_bound f f_bound x) as leq.
    rewrite <- A_eq in leq.
    rewrite mult_lanni in leq.
    apply (antisym (abs_pos _)) in leq.
    rewrite abs_def in leq.
    exact leq.
Qed.

Theorem bounded_uniformly_continuous : ∀ f, bounded_linear_map f →
    uniformly_continuous (linear_map_f f).
Proof.
    intros f f_bound ε ε_pos.
    classic_case (0 = operator_norm f f_bound) as [A_z|A_nz].
    {
        exists 1.
        split; [>exact one_pos|].
        intros a x leq.
        do 2 rewrite <- (operator_norm_zero _ _ A_z).
        rewrite d_zero.
        exact ε_pos.
    }
    exists (ε / (operator_norm f f_bound)).
    split.
    -   apply lt_mult; [>exact ε_pos|].
        apply div_pos.
        split; [>apply operator_norm_pos|exact A_nz].
    -   cbn.
        intros a x ltq.
        rewrite <- linear_map_neg.
        rewrite <- linear_map_plus.
        apply (le_lt_trans (operator_norm_bound f f_bound _)).
        rewrite <- lt_mult_lrmove_pos in ltq.
        2: split; [>apply operator_norm_pos|exact A_nz].
        rewrite mult_comm.
        exact ltq.
Qed.

Theorem continuous_bounded : ∀ f,
    continuous_at (linear_map_f f) 0 → bounded_linear_map f.
Proof.
    intros f f_cont.
    rewrite metric_continuous_at in f_cont.
    specialize (f_cont 1 one_pos) as [δ [δ_pos δ_geq]].
    rewrite linear_map_zero in δ_geq.
    classic_case (δ < 1) as [δ_small|δ_large].
    -   exists (/(δ * δ)).
        intros x.
        classic_case (0 = x) as [x_z|x_nz].
        {
            subst x.
            rewrite linear_map_zero.
            do 2 rewrite <- abs_zero.
            rewrite mult_ranni.
            apply refl.
        }
        assert (0 ≠ |x|) as x_nz'.
        {
            intros contr.
            rewrite abs_def in contr.
            contradiction.
        }
        specialize (δ_geq ((δ * δ / |x|) · x)).
        do 2 rewrite (d_sym 0) in δ_geq.
        cbn in δ_geq.
        do 2 rewrite neg_zero in δ_geq.
        do 2 rewrite plus_rid in δ_geq.
        pose proof (lt_mult δ_pos δ_pos) as δ2_pos.
        prove_parts δ_geq.
        {
            rewrite abs_scalar.
            rewrite abs_mult.
            rewrite <- abs_div by exact x_nz'.
            rewrite abs_abs.
            rewrite mult_rlinv by exact x_nz'.
            rewrite abs_pos_eq by apply δ2_pos.
            rewrite <- (mult_rid δ) at 3.
            apply lt_lmult_pos; assumption.
        }
        rewrite linear_map_scalar in δ_geq.
        rewrite abs_scalar in δ_geq.
        rewrite (mult_comm (δ * δ)) in δ_geq.
        rewrite abs_mult in δ_geq.
        rewrite <- abs_div in δ_geq by exact x_nz'.
        rewrite abs_abs in δ_geq.
        rewrite <- mult_assoc in δ_geq.
        rewrite <- lt_mult_rlmove_pos in δ_geq.
        2: split; [>apply abs_pos|exact x_nz'].
        rewrite mult_rid in δ_geq.
        assert (0 < |δ|) as δ_pos'.
        {
            rewrite abs_pos_eq; apply δ_pos.
        }
        rewrite lt_mult_llmove_pos in δ_geq.
        2: {
            rewrite abs_mult.
            apply lt_mult; exact δ_pos'.
        }
        apply (lt_le_trans δ_geq).
        rewrite abs_pos_eq by apply δ2_pos.
        apply refl.
    -   exists (δ + 1).
        intros x.
        classic_case (0 = x) as [x_z|x_nz].
        {
            subst x.
            rewrite linear_map_zero.
            do 2 rewrite <- abs_zero.
            rewrite mult_ranni.
            apply refl.
        }
        assert (0 ≠ |x|) as x_nz'.
        {
            intros contr.
            rewrite abs_def in contr.
            contradiction.
        }
        specialize (δ_geq (/((δ + 1) * |x|) · x)).
        do 2 rewrite (d_sym 0) in δ_geq.
        cbn in δ_geq.
        do 2 rewrite neg_zero in δ_geq.
        do 2 rewrite plus_rid in δ_geq.
        assert (0 < δ + 1) as δ1_pos.
        {
            rewrite <- (plus_rid 0).
            apply lt_lrplus.
            -   exact δ_pos.
            -   apply one_pos.
        }
        assert (0 < |δ + 1|) as δ1_pos'.
        {
            rewrite abs_pos_eq; apply δ1_pos.
        }
        prove_parts δ_geq.
        {
            rewrite abs_scalar.
            rewrite div_mult; [>|apply δ1_pos|exact x_nz'].
            rewrite abs_mult.
            rewrite <- abs_div by apply δ1_pos.
            rewrite <- abs_div by exact x_nz'.
            rewrite abs_abs.
            rewrite mult_rlinv by exact x_nz'.
            rewrite <- (mult_rid (/ _)).
            rewrite <- lt_mult_rlmove_pos by exact δ1_pos'.
            rewrite abs_pos_eq by apply δ1_pos.
            rewrite rdist.
            rewrite mult_lid.
            rewrite nlt_le in δ_large.
            apply (le_lt_trans δ_large).
            rewrite <- (plus_lid δ) at 1.
            apply lt_rplus.
            apply lt_mult; exact δ_pos.
        }
        rewrite linear_map_scalar in δ_geq.
        rewrite abs_scalar in δ_geq.
        assert (0 < |x|) as x_pos by (split; [>apply abs_pos|exact x_nz']).
        rewrite <- abs_div in δ_geq; [>|apply (lt_mult δ1_pos x_pos)].
        rewrite <- lt_mult_rlmove_pos in δ_geq.
        2: rewrite abs_pos_eq; apply (lt_mult δ1_pos x_pos).
        apply (lt_le_trans δ_geq).
        rewrite abs_pos_eq by (apply (lt_mult δ1_pos x_pos)).
        rewrite mult_rid.
        apply refl.
Qed.

(* begin hide *)
End AnalysisLinear.

Arguments linear_map U V {UP USM VP VSM}.

Section AnalysisLinearCompose.

Context {U V W} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,

    USM : ScalarMult real U,
    @ScalarId real U real_one USM,
    @ScalarLdist real U UP USM,
    @ScalarRdist real U real_plus UP USM,

    UA : AbsoluteValue U,
    @AbsDefinite U UA UZ,
    @AbsNeg U UA UN,
    @AbsTriangle U UA UP,
    @AbsPositive U UA,
    @AbsScalar U UA USM,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    VSM : ScalarMult real V,
    @ScalarId real V real_one VSM,
    @ScalarLdist real V VP VSM,
    @ScalarRdist real V real_plus VP VSM,

    VA : AbsoluteValue V,
    @AbsDefinite V VA VZ,
    @AbsNeg V VA VN,
    @AbsTriangle V VA VP,
    @AbsPositive V VA,
    @AbsScalar V VA VSM,

    WP : Plus W,
    WZ : Zero W,
    WN : Neg W,
    @PlusComm W WP,
    @PlusAssoc W WP,
    @PlusLid W WP WZ,
    @PlusLinv W WP WZ WN,

    WSM : ScalarMult real W,
    @ScalarId real W real_one WSM,
    @ScalarLdist real W WP WSM,
    @ScalarRdist real W real_plus WP WSM,

    WA : AbsoluteValue W,
    @AbsDefinite W WA WZ,
    @AbsNeg W WA WN,
    @AbsTriangle W WA WP,
    @AbsPositive W WA,
    @AbsScalar W WA WSM
}.

(* end hide *)
Lemma linear_map_compose_plus : ∀ (f : linear_map V W) (g : linear_map U V),
    ∀ u v, linear_map_f f (linear_map_f g (u + v)) =
    linear_map_f f (linear_map_f g u) + linear_map_f f (linear_map_f g v).
Proof.
    intros f g u v.
    rewrite linear_map_plus.
    apply linear_map_plus.
Qed.

Lemma linear_map_compose_scalar : ∀ (f : linear_map V W) (g : linear_map U V),
    ∀ a v, linear_map_f f (linear_map_f g (a · v)) =
    a · linear_map_f f (linear_map_f g v).
Proof.
    intros f g a v.
    rewrite linear_map_scalar.
    apply linear_map_scalar.
Qed.

Definition linear_map_compose (f : linear_map V W) (g : linear_map U V)
    := make_linear_map
        (λ v, linear_map_f f (linear_map_f g v))
        (linear_map_compose_scalar f g)
        (linear_map_compose_plus f g).

Theorem linear_map_compose_bounded : ∀ f g,
    bounded_linear_map f → bounded_linear_map g →
    bounded_linear_map (linear_map_compose f g).
Proof.
    intros f g f_bound g_bound.
    exists (operator_norm f f_bound * operator_norm g g_bound).
    intros x.
    cbn.
    apply (trans (operator_norm_bound f f_bound _)).
    rewrite <- mult_assoc.
    apply le_lmult_pos; [>apply operator_norm_pos|].
    apply operator_norm_bound.
Qed.
(* begin hide *)

End AnalysisLinearCompose.
(* end hide *)
