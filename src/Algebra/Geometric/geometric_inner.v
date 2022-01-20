Require Import init.

Require Import mult_product.

Require Import linear_extend.

Require Export geometric_construct.
Require Import geometric_grade.
Require Import geometric_exterior_isomorphism.

Section GeometricInner.

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
Let GS := geo_scalar B.
Let GSO := geo_scalar_id B.
Let GSL := geo_scalar_ldist B.
Let GSR := geo_scalar_rdist B.
Let GSC := geo_scalar_comp B.
Let GSML := geo_scalar_lmult B.
Let GSMR := geo_scalar_rmult B.
Let GG := geo_grade B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GL GR GS GSO GSL GSR GSC GSML
    GSMR GG.

Local Notation "'φ'" := (vector_to_geo B).
Local Notation "'σ'" := (scalar_to_geo B).

Local Open Scope nat_scope.

Definition geo_inner_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := grade_project (a * b) (i ⊖ j).

Definition geo_lcontr_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := match j ¯ i with
       | opt_val n => grade_project (a * b) n
       | opt_nil _ => 0
       end.

Definition geo_rcontr_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := match i ¯ j with
       | opt_val n => grade_project (a * b) n
       | opt_nil _ => 0
       end.

Lemma geo_inner_ldist_base : bilinear_extend_ldist_base geo_inner_base.
    intros u v w i j ui vj wj.
    unfold geo_inner_base.
    rewrite ldist.
    apply grade_project_plus.
Qed.

Lemma geo_inner_rdist_base : bilinear_extend_rdist_base geo_inner_base.
    intros u v w i j ui vi wj.
    unfold geo_inner_base.
    rewrite rdist.
    apply grade_project_plus.
Qed.

Lemma geo_inner_lscalar_base : bilinear_extend_lscalar_base geo_inner_base.
    intros a u v i j ui vj.
    unfold geo_inner_base.
    rewrite scalar_lmult.
    apply grade_project_scalar.
Qed.

Lemma geo_inner_rscalar_base : bilinear_extend_rscalar_base geo_inner_base.
    intros a u v i j ui vj.
    unfold geo_inner_base.
    rewrite scalar_rmult.
    apply grade_project_scalar.
Qed.

Lemma geo_lcontr_ldist_base : bilinear_extend_ldist_base geo_lcontr_base.
    intros u v w i j ui vj wj.
    unfold geo_lcontr_base.
    rewrite ldist.
    destruct (j ¯ i).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma geo_lcontr_rdist_base : bilinear_extend_rdist_base geo_lcontr_base.
    intros u v w i j ui vi wj.
    unfold geo_lcontr_base.
    rewrite rdist.
    destruct (j ¯ i).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma geo_lcontr_lscalar_base : bilinear_extend_lscalar_base geo_lcontr_base.
    intros a u v i j ui vj.
    unfold geo_lcontr_base.
    rewrite scalar_lmult.
    destruct (j ¯ i).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Lemma geo_lcontr_rscalar_base : bilinear_extend_rscalar_base geo_lcontr_base.
    intros a u v i j ui vj.
    unfold geo_lcontr_base.
    rewrite scalar_rmult.
    destruct (j ¯ i).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Lemma geo_rcontr_ldist_base : bilinear_extend_ldist_base geo_rcontr_base.
    intros u v w i j ui vj wj.
    unfold geo_rcontr_base.
    rewrite ldist.
    destruct (i ¯ j).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma geo_rcontr_rdist_base : bilinear_extend_rdist_base geo_rcontr_base.
    intros u v w i j ui vi wj.
    unfold geo_rcontr_base.
    rewrite rdist.
    destruct (i ¯ j).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma geo_rcontr_lscalar_base : bilinear_extend_lscalar_base geo_rcontr_base.
    intros a u v i j ui vj.
    unfold geo_rcontr_base.
    rewrite scalar_lmult.
    destruct (i ¯ j).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Lemma geo_rcontr_rscalar_base : bilinear_extend_rscalar_base geo_rcontr_base.
    intros a u v i j ui vj.
    unfold geo_rcontr_base.
    rewrite scalar_rmult.
    destruct (i ¯ j).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Definition geo_inner := bilinear_extend geo_inner_base : geo B → geo B → geo B.
Definition geo_lcontr := bilinear_extend geo_lcontr_base : geo B → geo B → geo B.
Definition geo_rcontr := bilinear_extend geo_rcontr_base : geo B → geo B → geo B.

Local Infix "•" := geo_inner (at level 34, left associativity).
Local Infix "⌋" := geo_lcontr (at level 34, left associativity).
Local Infix "⌊" := geo_rcontr (at level 34, left associativity).

Theorem inner_ldist : ∀ a b c, a • (b + c) = a • b + a • c.
    apply bilinear_extend_ldist.
    -   exact geo_inner_ldist_base.
    -   exact geo_inner_rscalar_base.
Qed.

Theorem inner_rdist : ∀ a b c, (a + b) • c = a • c + b • c.
    apply bilinear_extend_rdist.
    -   exact geo_inner_rdist_base.
    -   exact geo_inner_lscalar_base.
Qed.

Theorem inner_lscalar : ∀ a u v, (a · u) • v = a · (u • v).
    apply bilinear_extend_lscalar.
    -   apply geo_inner_rdist_base.
    -   apply geo_inner_lscalar_base.
Qed.

Theorem inner_rscalar : ∀ a u v, u • (a · v) = a · (u • v).
    apply bilinear_extend_rscalar.
    -   apply geo_inner_ldist_base.
    -   apply geo_inner_rscalar_base.
Qed.

Theorem inner_lanni : ∀ a, 0 • a = 0.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite inner_lscalar.
    apply scalar_lanni.
Qed.

Theorem inner_ranni : ∀ a, a • 0 = 0.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite inner_rscalar.
    apply scalar_lanni.
Qed.

Theorem lcontr_ldist : ∀ a b c, a ⌋ (b + c) = a ⌋ b + a ⌋ c.
    apply bilinear_extend_ldist.
    -   exact geo_lcontr_ldist_base.
    -   exact geo_lcontr_rscalar_base.
Qed.

Theorem lcontr_rdist : ∀ a b c, (a + b) ⌋ c = a ⌋ c + b ⌋ c.
    apply bilinear_extend_rdist.
    -   exact geo_lcontr_rdist_base.
    -   exact geo_lcontr_lscalar_base.
Qed.

Theorem lcontr_lscalar : ∀ a u v, (a · u) ⌋ v = a · (u ⌋ v).
    apply bilinear_extend_lscalar.
    -   apply geo_lcontr_rdist_base.
    -   apply geo_lcontr_lscalar_base.
Qed.

Theorem lcontr_rscalar : ∀ a u v, u ⌋ (a · v) = a · (u ⌋ v).
    apply bilinear_extend_rscalar.
    -   apply geo_lcontr_ldist_base.
    -   apply geo_lcontr_rscalar_base.
Qed.

Theorem lcontr_lanni : ∀ a, 0 ⌋ a = 0.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite lcontr_lscalar.
    apply scalar_lanni.
Qed.

Theorem lcontr_ranni : ∀ a, a ⌋ 0 = 0.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite lcontr_rscalar.
    apply scalar_lanni.
Qed.

Theorem rcontr_ldist : ∀ a b c, a ⌊ (b + c) = a ⌊ b + a ⌊ c.
    apply bilinear_extend_ldist.
    -   exact geo_rcontr_ldist_base.
    -   exact geo_rcontr_rscalar_base.
Qed.

Theorem rcontr_rdist : ∀ a b c, (a + b) ⌊ c = a ⌊ c + b ⌊ c.
    apply bilinear_extend_rdist.
    -   exact geo_rcontr_rdist_base.
    -   exact geo_rcontr_lscalar_base.
Qed.

Theorem rcontr_lscalar : ∀ a u v, (a · u) ⌊ v = a · (u ⌊ v).
    apply bilinear_extend_lscalar.
    -   apply geo_rcontr_rdist_base.
    -   apply geo_rcontr_lscalar_base.
Qed.

Theorem rcontr_rscalar : ∀ a u v, u ⌊ (a · v) = a · (u ⌊ v).
    apply bilinear_extend_rscalar.
    -   apply geo_rcontr_ldist_base.
    -   apply geo_rcontr_rscalar_base.
Qed.

Theorem rcontr_lanni : ∀ a, 0 ⌊ a = 0.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite rcontr_lscalar.
    apply scalar_lanni.
Qed.

Theorem rcontr_ranni : ∀ a, a ⌊ 0 = 0.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite rcontr_rscalar.
    apply scalar_lanni.
Qed.

Lemma inner_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
        u • v = geo_inner_base i j u v ui vj.
    intros i j u v ui vj.
    unfold geo_inner.
    apply bilinear_extend_homo.
    -   exact geo_inner_ldist_base.
    -   exact geo_inner_rdist_base.
    -   exact geo_inner_lscalar_base.
    -   exact geo_inner_rscalar_base.
Qed.

Lemma lcontr_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
        u ⌋ v = geo_lcontr_base i j u v ui vj.
    intros i j u v ui vj.
    unfold geo_lcontr.
    apply bilinear_extend_homo.
    -   exact geo_lcontr_ldist_base.
    -   exact geo_lcontr_rdist_base.
    -   exact geo_lcontr_lscalar_base.
    -   exact geo_lcontr_rscalar_base.
Qed.

Lemma rcontr_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
        u ⌊ v = geo_rcontr_base i j u v ui vj.
    intros i j u v ui vj.
    unfold geo_rcontr.
    apply bilinear_extend_homo.
    -   exact geo_rcontr_ldist_base.
    -   exact geo_rcontr_rdist_base.
    -   exact geo_rcontr_lscalar_base.
    -   exact geo_rcontr_rscalar_base.
Qed.

End GeometricInner.

Infix "•" := (geo_inner _) (at level 34, left associativity) : geo_scope.
Infix "⌋" := (geo_lcontr _) (at level 34, left associativity) : geo_scope.
Infix "⌊" := (geo_rcontr _) (at level 34, left associativity) : geo_scope.
