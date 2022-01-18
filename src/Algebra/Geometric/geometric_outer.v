Require Import init.

Require Import mult_product.

Require Import linear_extend.

Require Export geometric_construct.
Require Import geometric_grade.
Require Import geometric_exterior_isomorphism.

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

Let GP := ga_plus B.
Let GZ := ga_zero B.
Let GN := ga_neg B.
Let GPA := ga_plus_assoc B.
Let GPC := ga_plus_comm B.
Let GPZ := ga_plus_lid B.
Let GPN := ga_plus_linv B.
Let GM := ga_mult B.
Let GO := ga_one B.
Let GL := ga_ldist B.
Let GR := ga_rdist B.
Let GS := ga_scalar B.
Let GSO := ga_scalar_id B.
Let GSL := ga_scalar_ldist B.
Let GSR := ga_scalar_rdist B.
Let GSC := ga_scalar_comp B.
Let GSML := ga_scalar_lmult B.
Let GSMR := ga_scalar_rmult B.
Let GG := ga_grade B.

Existing Instances GP GZ GN GPA GPC GPZ GPN GM GO GL GR GS GSO GSL GSR GSC GSML
    GSMR GG.

Local Notation "'φ'" := (vector_to_ga B).
Local Notation "'σ'" := (scalar_to_ga B).

Definition ga_outer_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := grade_project (a * b) (i + j).

Lemma ga_outer_ldist_base : bilinear_extend_ldist_base ga_outer_base.
    intros u v w i j ui vj wj.
    unfold ga_outer_base.
    rewrite ldist.
    apply grade_project_plus.
Qed.

Lemma ga_outer_rdist_base : bilinear_extend_rdist_base ga_outer_base.
    intros u v w i j ui vi wj.
    unfold ga_outer_base.
    rewrite rdist.
    apply grade_project_plus.
Qed.

Lemma ga_outer_lscalar_base : bilinear_extend_lscalar_base ga_outer_base.
    intros a u v i j ui vj.
    unfold ga_outer_base.
    rewrite scalar_lmult.
    apply grade_project_scalar.
Qed.

Lemma ga_outer_rscalar_base : bilinear_extend_rscalar_base ga_outer_base.
    intros a u v i j ui vj.
    unfold ga_outer_base.
    rewrite scalar_rmult.
    apply grade_project_scalar.
Qed.

Definition ga_outer := bilinear_extend ga_outer_base : ga B → ga B → ga B.

Local Infix "⋀" := ga_outer (at level 34, left associativity).

Theorem outer_ldist : ∀ a b c, a ⋀ (b + c) = a ⋀ b + a ⋀ c.
    apply bilinear_extend_ldist.
    -   exact ga_outer_ldist_base.
    -   exact ga_outer_rscalar_base.
Qed.

Theorem outer_rdist : ∀ a b c, (a + b) ⋀ c = a ⋀ c + b ⋀ c.
    apply bilinear_extend_rdist.
    -   exact ga_outer_rdist_base.
    -   exact ga_outer_lscalar_base.
Qed.

Theorem outer_lscalar : ∀ a u v, (a · u) ⋀ v = a · (u ⋀ v).
    apply bilinear_extend_lscalar.
    -   apply ga_outer_rdist_base.
    -   apply ga_outer_lscalar_base.
Qed.

Theorem outer_rscalar : ∀ a u v, u ⋀ (a · v) = a · (u ⋀ v).
    apply bilinear_extend_rscalar.
    -   apply ga_outer_ldist_base.
    -   apply ga_outer_rscalar_base.
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
        u ⋀ v = ga_outer_base i j u v ui vj.
    intros i j u v ui vj.
    unfold ga_outer.
    apply bilinear_extend_homo.
    -   exact ga_outer_ldist_base.
    -   exact ga_outer_rdist_base.
    -   exact ga_outer_lscalar_base.
    -   exact ga_outer_rscalar_base.
Qed.

End GeometricOuter.

Infix "⋀" := (ga_outer _) (at level 34, left associativity) : ga_scope.
