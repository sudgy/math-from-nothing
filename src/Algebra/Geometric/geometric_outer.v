Require Import init.

Require Import mult_product.
Require Import order_minmax.

Require Import linear_extend.

Require Export geometric_construct.
Require Import geometric_grade.
Require Import geometric_exterior_isomorphism.
Require Import geometric_decomposition.
Require Import exterior_involutions.
Require Import geometric_involutions_grade.
Require Import exterior_grade.

Section GeometricOuter.

Context {F : CRing} {V : Module F}.

Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMC := cring_mult_comm F.

Existing Instances UP UZ UN UPC UPZ UPN UM UO UMC.

Let VP := module_plus V.
Let VS := module_scalar V.

Existing Instances VP VS.

Context (B : set_type bilinear_form).

Let GP := geo_plus B.
Let GZ := geo_zero B.
Let GN := geo_neg B.
Let GPA := geo_plus_assoc B.
Let GPC := geo_plus_comm B.
Let GPZ := geo_plus_lid B.
Let GPN := geo_plus_linv B.
Let GM := geo_mult B.
Let GO := geo_one B.
Let GL := geo_ldist B.
Let GR := geo_rdist B.
Let GMA := geo_mult_assoc B.
Let GML := geo_mult_lid B.
Let GMR := geo_mult_rid B.
Let GS := geo_scalar B.
Let GSO := geo_scalar_id B.
Let GSL := geo_scalar_ldist B.
Let GSR := geo_scalar_rdist B.
Let GSC := geo_scalar_comp B.
Let GSML := geo_scalar_lmult B.
Let GSMR := geo_scalar_rmult B.
Let GG := geo_grade B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GL GR GMA GML GMR GS GSO GSL
    GSR GSC GSML GSMR GG.

Local Notation "'φ'" := (vector_to_geo B).
Local Notation "'σ'" := (scalar_to_geo B).
Local Notation "'E'" := (geo_to_ext B).
Local Notation "'G'" := (ext_to_geo B).

Let EP := ext_plus V.
Let EZ := ext_zero V.
Let EN := ext_neg V.
Let EPA := ext_plus_assoc V.
Let EPC := ext_plus_comm V.
Let EPZ := ext_plus_lid V.
Let EPN := ext_plus_linv V.
Let EM := ext_mult V.
Let EO := ext_one V.
Let EL := ext_ldist V.
Let ER := ext_rdist V.
Let EML := ext_mult_lid V.
Let EMR := ext_mult_rid V.
Let EMA := ext_mult_assoc V.
Let ES := ext_scalar V.
Let ESO := ext_scalar_id V.
Let ESL := ext_scalar_ldist V.
Let ESR := ext_scalar_rdist V.
Let ESML := ext_scalar_lmult V.
Let ESMR := ext_scalar_rmult V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO EL ER EML EMR EMA ES ESO ESL
    ESR ESML ESMR.

Local Open Scope geo_scope.
Local Open Scope nat_scope.

Definition geo_outer_base i j (a b : geo B) (ai : of_grade i a) (bj : of_grade j b)
    := grade_project (a * b) (i + j) : geo B.

Lemma geo_outer_ldist_base : bilinear_extend_ldist_base geo_outer_base.
    intros u v w i j ui vj wj.
    unfold geo_outer_base.
    rewrite ldist.
    apply grade_project_plus.
Qed.

Lemma geo_outer_rdist_base : bilinear_extend_rdist_base geo_outer_base.
    intros u v w i j ui vi wj.
    unfold geo_outer_base.
    rewrite rdist.
    apply grade_project_plus.
Qed.

Lemma geo_outer_lscalar_base : bilinear_extend_lscalar_base geo_outer_base.
    intros a u v i j ui vj.
    unfold geo_outer_base.
    rewrite scalar_lmult.
    apply grade_project_scalar.
Qed.

Lemma geo_outer_rscalar_base : bilinear_extend_rscalar_base geo_outer_base.
    intros a u v i j ui vj.
    unfold geo_outer_base.
    rewrite scalar_rmult.
    apply grade_project_scalar.
Qed.

Definition geo_outer := bilinear_extend geo_outer_base : geo B → geo B → geo B.

(** Note: Because Coq already uses ∧ for logical and, this symbol is actually
\bigwedge, not \wedge!
*)
Local Infix "⋀" := geo_outer (at level 34, left associativity).

Theorem outer_ldist : ∀ a b c, a ⋀ (b + c) = a ⋀ b + a ⋀ c.
    apply bilinear_extend_ldist.
    -   exact geo_outer_ldist_base.
    -   exact geo_outer_rscalar_base.
Qed.

Theorem outer_rdist : ∀ a b c, (a + b) ⋀ c = a ⋀ c + b ⋀ c.
    apply bilinear_extend_rdist.
    -   exact geo_outer_rdist_base.
    -   exact geo_outer_lscalar_base.
Qed.

Theorem outer_lscalar : ∀ a u v, (a · u) ⋀ v = a · (u ⋀ v).
    apply bilinear_extend_lscalar.
    -   apply geo_outer_rdist_base.
    -   apply geo_outer_lscalar_base.
Qed.

Theorem outer_rscalar : ∀ a u v, u ⋀ (a · v) = a · (u ⋀ v).
    apply bilinear_extend_rscalar.
    -   apply geo_outer_ldist_base.
    -   apply geo_outer_rscalar_base.
Qed.

Theorem outer_lanni : ∀ a, 0 ⋀ a = 0.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite outer_lscalar.
    apply scalar_lanni.
Qed.

Theorem outer_ranni : ∀ a, a ⋀ 0 = 0.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite outer_rscalar.
    apply scalar_lanni.
Qed.

Lemma outer_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
        u ⋀ v = geo_outer_base i j u v ui vj.
    intros i j u v ui vj.
    unfold geo_outer.
    apply bilinear_extend_homo.
    -   exact geo_outer_ldist_base.
    -   exact geo_outer_rdist_base.
    -   exact geo_outer_lscalar_base.
    -   exact geo_outer_rscalar_base.
Qed.

Let EG := exterior_grade V.
Let EGA := exterior_grade_mult V.

Existing Instances EG EGA.

Theorem outer_exterior : ∀ a b, a ⋀ b = G (E a * E b).
    intros a' b'.
    rewrite <- (ext_to_geo_to_ext B a') at 1.
    rewrite <- (ext_to_geo_to_ext B b') at 1.
    remember (E a') as a.
    remember (E b') as b.
    clear a' b' Heqa Heqb.
    induction b as [|b b' n bn b'n IHb] using grade_induction.
    {
        rewrite mult_ranni.
        rewrite ext_to_geo_zero.
        apply outer_ranni.
    }
    rewrite ldist.
    do 2 rewrite ext_to_geo_plus.
    rewrite outer_ldist.
    rewrite IHb; clear IHb.
    apply rplus; clear b' b'n.
    pose proof (ext_sum V a) as [l l_eq]; subst a.
    induction l as [|[α al] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_lanni.
        rewrite ext_to_geo_zero.
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
    assert (of_grade (H10 := GG) (list_size al)
        (G (list_prod (list_image al (vector_to_ext V))))) as al_grade.
    {
        exists (list_prod (list_image al (vector_to_ext V))).
        split; [>|reflexivity].
        apply ext_list_grade.
    }
    assert (of_grade (H10 := GG) n (G b)) as b_grade.
    {
        exists b.
        split; [>exact bn|reflexivity].
    }
    rewrite (outer_homo _ _ _ _ al_grade b_grade).
    unfold geo_outer_base.
    clear al_grade.
    induction al as [|v al].
    {
        cbn.
        rewrite ext_to_geo_one.
        do 2 rewrite mult_lid.
        rewrite plus_lid.
        apply grade_project_of_grade.
        exact b_grade.
    }
    cbn.
    remember (list_prod (list_image al (vector_to_ext V))) as a.
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
    assert (of_grade (H10 := GG) m (G a)) as a_grade'.
    {
        exists a.
        split; [>exact a_grade|reflexivity].
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

Theorem outer_assoc : ∀ a b c : geo B, a ⋀ (b ⋀ c) = (a ⋀ b) ⋀ c.
    intros a b c.
    do 4 rewrite outer_exterior.
    do 2 rewrite geo_to_ext_to_geo.
    rewrite mult_assoc.
    reflexivity.
Qed.

Theorem outer_lid : ∀ a : geo B, 1 ⋀ a = a.
    intros a.
    rewrite outer_exterior.
    rewrite geo_to_ext_one.
    rewrite mult_lid.
    apply ext_to_geo_to_ext.
Qed.

Theorem outer_rid : ∀ a : geo B, a ⋀ 1 = a.
    intros a.
    rewrite outer_exterior.
    rewrite geo_to_ext_one.
    rewrite mult_rid.
    apply ext_to_geo_to_ext.
Qed.

Theorem outer_alternating : ∀ v, φ v ⋀ φ v = 0.
    intros v.
    rewrite outer_exterior.
    rewrite geo_to_ext_vector.
    rewrite <- ext_alternating.
    apply ext_to_geo_zero.
Qed.

Theorem outer_anticomm : ∀ u v, φ u ⋀ φ v = -(φ v ⋀ φ u).
    intros u v.
    do 2 rewrite outer_exterior.
    do 2 rewrite geo_to_ext_vector.
    rewrite ext_anticomm.
    apply ext_to_geo_neg.
Qed.

Theorem outer_reverse : ∀ a b, (a ⋀ b)† = b† ⋀ a†.
    intros a b.
    do 2 rewrite outer_exterior.
    rewrite ext_to_geo_reverse.
    rewrite ext_reverse_mult.
    do 2 rewrite geo_to_ext_reverse.
    reflexivity.
Qed.

Theorem outer_involute : ∀ a b, (a ⋀ b)∗ = a∗ ⋀ b∗.
    intros a b.
    do 2 rewrite outer_exterior.
    rewrite ext_to_geo_involute.
    rewrite ext_involute_mult.
    do 2 rewrite geo_to_ext_involute.
    reflexivity.
Qed.

End GeometricOuter.

Infix "⋀" := (geo_outer _) (at level 34, left associativity) : geo_scope.
