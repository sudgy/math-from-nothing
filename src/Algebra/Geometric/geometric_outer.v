Require Import init.

Require Import order_minmax.

Require Import linear_extend.
Require Import linear_bilinear.

Require Export geometric_base.

Section GeometricOuter.

Context {F : CRingObj} {V : ModuleObj F}.
Context (B : set_type (bilinear_form (V := V))).

Let GG := geo_grade B.

Existing Instances GG.

Local Notation φ := (vector_to_geo B).
Local Notation σ := (scalar_to_geo B).
Local Notation E := (geo_to_ext B).
Local Notation G := (ext_to_geo B).
Local Notation geo := (geometric_algebra B).
Local Notation ext := (exterior_algebra V).

Local Open Scope geo_scope.
Local Open Scope nat_scope.

(* end hide *)
Definition geo_outer_base i j (a : grade_modules i) (b : grade_modules j)
    := grade_project (grade_modules_from a * grade_modules_from b) (i + j) :geo.

Lemma geo_outer_bilinear : ∀ i j, bilinear (geo_outer_base i j).
Proof.
    intros i j.
    unfold geo_outer_base.
    repeat split.
    -   intros a u v.
        rewrite module_homo_scalar.
        rewrite scalar_lmult.
        apply grade_project_scalar.
    -   intros a u v.
        rewrite module_homo_scalar.
        rewrite scalar_rmult.
        apply grade_project_scalar.
    -   intros a u v.
        rewrite module_homo_plus.
        rewrite rdist.
        apply grade_project_plus.
    -   intros a u v.
        rewrite module_homo_plus.
        rewrite ldist.
        apply grade_project_plus.
Qed.

Definition geo_outer := bilinear_extend (λ i j, [_|geo_outer_bilinear i j])
    : geo → geo → geo.

(** Note: Because Coq already uses ∧ for logical and, this symbol is actually
\bigwedge, not \wedge!
*)
(* begin show *)
Local Infix "⋀" := geo_outer (at level 34, left associativity).
(* end show *)

Theorem outer_ldist : ∀ a b c, a ⋀ (b + c) = a ⋀ b + a ⋀ c.
Proof.
    apply bilinear_extend_ldist.
Qed.

Theorem outer_rdist : ∀ a b c, (a + b) ⋀ c = a ⋀ c + b ⋀ c.
Proof.
    apply bilinear_extend_rdist.
Qed.

Theorem outer_lscalar : ∀ a u v, (a · u) ⋀ v = a · (u ⋀ v).
Proof.
    apply bilinear_extend_lscalar.
Qed.

Theorem outer_rscalar : ∀ a u v, u ⋀ (a · v) = a · (u ⋀ v).
Proof.
    apply bilinear_extend_rscalar.
Qed.

Theorem outer_lanni : ∀ a, 0 ⋀ a = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite outer_lscalar.
    apply scalar_lanni.
Qed.

Theorem outer_ranni : ∀ a, a ⋀ 0 = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite outer_rscalar.
    apply scalar_lanni.
Qed.

Lemma outer_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
    u ⋀ v = grade_project (u * v) (i + j).
Proof.
    intros i j u v ui vj.
    unfold geo_outer.
    rewrite (bilinear_extend_homo _ _ _ _ _ ui vj); cbn.
    unfold geo_outer_base.
    rewrite grade_modules_from_to by exact ui.
    rewrite grade_modules_from_to by exact vj.
    reflexivity.
Qed.

Let EG := exterior_grade V.
Let EGA := exterior_grade_mult V.

Existing Instances EG EGA.

Theorem outer_exterior : ∀ a b, a ⋀ b = G (E a * E b).
Proof.
    intros a' b'.
    rewrite <- (ext_to_geo_to_ext B a') at 1.
    rewrite <- (ext_to_geo_to_ext B b') at 1.
    remember (E a') as a.
    remember (E b') as b.
    clear a' b' Heqa Heqb.
    induction b as [|b b'] using grade_induction.
    {
        rewrite mult_ranni.
        do 2 rewrite ext_to_geo_zero.
        apply outer_ranni.
    }
    rewrite ldist.
    do 2 rewrite ext_to_geo_plus.
    rewrite outer_ldist.
    rewrite IHb; clear IHb.
    apply rplus; clear b'.
    pose proof (ext_sum V a) as [l l_eq]; subst a.
    induction l as [|[α al] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_lanni.
        do 2 rewrite ext_to_geo_zero.
        apply outer_lanni.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite rdist.
    do 2 rewrite ext_to_geo_plus.
    rewrite outer_rdist.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite scalar_lmult.
    do 2 rewrite ext_to_geo_scalar.
    rewrite outer_lscalar.
    apply lscalar; clear α.
    assert (of_grade (list_size al)
        (G (list_prod (list_image (vector_to_ext V) al)))) as al_grade.
    {
        apply ext_to_geo_of_grade.
        apply ext_list_grade.
    }
    destruct b as [b [n b_grade]]; cbn.
    apply (ext_to_geo_of_grade B b n) in b_grade.
    rewrite (outer_homo _ _ _ _ al_grade b_grade).
    clear al_grade.
    induction al as [|v al].
    {
        rewrite ext_to_geo_one.
        do 2 rewrite mult_lid.
        rewrite plus_lid.
        apply grade_project_of_grade.
        exact b_grade.
    }
    do 2 rewrite list_image_add; cbn.
    do 2 rewrite list_prod_add.
    remember (list_prod (list_image (vector_to_ext V) al)) as a.
    rewrite list_size_add.
    remember (list_size al) as m.
    assert (of_grade m a) as a_grade.
    {
        rewrite Heqa, Heqm.
        apply ext_list_grade.
    }
    clear al Heqa Heqm.
    rewrite ext_to_geo_add.
    rewrite rdist.
    rewrite grade_project_plus.
    assert (of_grade m (G a)) as a_grade'.
    {
        apply ext_to_geo_of_grade.
        exact a_grade.
    }
    rewrite mult_lneg.
    rewrite grade_project_neg.
    assert (grade_project (geo_mult_inner B v (G a) * G b) (nat_suc m + n) = 0)
        as eq.
    {
        nat_destruct m.
        -   apply ext_grade_zero_scalar in a_grade as [α α_eq]; subst a.
            rewrite ext_to_geo_of_scalar.
            rewrite geo_mult_inner_scalar.
            rewrite mult_lanni.
            apply grade_project_zero.
        -   pose proof (geo_mult_inner_grade B v (G a) _ a_grade') as am.
            apply (geo_mult_project_bigger _ _ _ _ _ am b_grade).
            do 2 rewrite nat_plus_lsuc.
            apply (trans (nat_lt_suc _)).
            apply nat_lt_suc.
    }
    rewrite eq; clear eq.
    rewrite neg_zero, plus_lid.
    rewrite <- mult_assoc.
    rewrite <- (ext_to_geo_to_ext B (φ v * _)).
    rewrite geo_to_ext_add.
    rewrite ext_to_geo_plus.
    rewrite grade_project_plus.
    rewrite ext_to_geo_inner.
    rewrite ext_to_geo_to_ext.
    rewrite mult_inner_grade_add.
    assert (m + n < nat_suc (nat_suc m + n)) as ltq.
    {
        rewrite nat_plus_lsuc.
        apply (trans (nat_lt_suc _)).
        apply nat_lt_suc.
    }
    rewrite (geo_mult_project_bigger _ _ _ _ _ a_grade' b_grade _ ltq).
    rewrite geo_mult_inner_rzero.
    rewrite plus_lid.
    rewrite ext_to_geo_project.
    rewrite nat_plus_lsuc.
    rewrite exterior_grade_add.
    rewrite geo_to_ext_project.
    rewrite IHal.
    rewrite geo_to_ext_to_geo.
    rewrite mult_assoc.
    reflexivity.
Qed.

Theorem outer_assoc : ∀ a b c : geo, a ⋀ (b ⋀ c) = (a ⋀ b) ⋀ c.
Proof.
    intros a b c.
    do 4 rewrite outer_exterior.
    do 2 rewrite geo_to_ext_to_geo.
    rewrite mult_assoc.
    reflexivity.
Qed.

Theorem outer_lid : ∀ a : geo, 1 ⋀ a = a.
Proof.
    intros a.
    rewrite outer_exterior.
    rewrite geo_to_ext_one.
    rewrite mult_lid.
    apply ext_to_geo_to_ext.
Qed.

Theorem outer_rid : ∀ a : geo, a ⋀ 1 = a.
Proof.
    intros a.
    rewrite outer_exterior.
    rewrite geo_to_ext_one.
    rewrite mult_rid.
    apply ext_to_geo_to_ext.
Qed.

Theorem outer_alternating : ∀ v, φ v ⋀ φ v = 0.
Proof.
    intros v.
    rewrite outer_exterior.
    rewrite geo_to_ext_vector.
    rewrite <- ext_alternating.
    apply ext_to_geo_zero.
Qed.

Theorem outer_anticomm : ∀ u v, φ u ⋀ φ v = -(φ v ⋀ φ u).
Proof.
    intros u v.
    do 2 rewrite outer_exterior.
    do 2 rewrite geo_to_ext_vector.
    rewrite ext_anticomm.
    apply ext_to_geo_neg.
Qed.

Theorem outer_reverse : ∀ a b, (a ⋀ b)† = b† ⋀ a†.
Proof.
    intros a b.
    do 2 rewrite outer_exterior.
    rewrite ext_to_geo_reverse.
    rewrite ext_reverse_mult.
    do 2 rewrite geo_to_ext_reverse.
    reflexivity.
Qed.

Theorem outer_involute : ∀ a b, (a ⋀ b)∗ = a∗ ⋀ b∗.
Proof.
    intros a b.
    do 2 rewrite outer_exterior.
    rewrite ext_to_geo_involute.
    rewrite ext_involute_mult.
    do 2 rewrite geo_to_ext_involute.
    reflexivity.
Qed.

Theorem outer_involute_swap : ∀ a X, φ a ⋀ X = X∗ ⋀ φ a.
Proof.
    intros a X.
    do 2 rewrite outer_exterior.
    rewrite geo_to_ext_vector.
    rewrite ext_involute_swap.
    rewrite geo_to_ext_involute.
    reflexivity.
Qed.

(* begin hide *)
End GeometricOuter.

(* end hide *)
Infix "⋀" := (geo_outer _) (at level 34, left associativity) : geo_scope.
