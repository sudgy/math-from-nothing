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

Local Open Scope nat_scope.

Definition ga_inner_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := grade_project (a * b) (i ⊖ j).

Definition ga_lcontr_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := match j ¯ i with
       | opt_val n => grade_project (a * b) n
       | opt_nil _ => 0
       end.

Definition ga_rcontr_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := match i ¯ j with
       | opt_val n => grade_project (a * b) n
       | opt_nil _ => 0
       end.

Lemma ga_inner_ldist_base : bilinear_extend_ldist_base ga_inner_base.
    intros u v w i j ui vj wj.
    unfold ga_inner_base.
    rewrite ldist.
    apply grade_project_plus.
Qed.

Lemma ga_inner_rdist_base : bilinear_extend_rdist_base ga_inner_base.
    intros u v w i j ui vi wj.
    unfold ga_inner_base.
    rewrite rdist.
    apply grade_project_plus.
Qed.

Lemma ga_inner_lscalar_base : bilinear_extend_lscalar_base ga_inner_base.
    intros a u v i j ui vj.
    unfold ga_inner_base.
    rewrite scalar_lmult.
    apply grade_project_scalar.
Qed.

Lemma ga_inner_rscalar_base : bilinear_extend_rscalar_base ga_inner_base.
    intros a u v i j ui vj.
    unfold ga_inner_base.
    rewrite scalar_rmult.
    apply grade_project_scalar.
Qed.

Lemma ga_lcontr_ldist_base : bilinear_extend_ldist_base ga_lcontr_base.
    intros u v w i j ui vj wj.
    unfold ga_lcontr_base.
    rewrite ldist.
    destruct (j ¯ i).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma ga_lcontr_rdist_base : bilinear_extend_rdist_base ga_lcontr_base.
    intros u v w i j ui vi wj.
    unfold ga_lcontr_base.
    rewrite rdist.
    destruct (j ¯ i).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma ga_lcontr_lscalar_base : bilinear_extend_lscalar_base ga_lcontr_base.
    intros a u v i j ui vj.
    unfold ga_lcontr_base.
    rewrite scalar_lmult.
    destruct (j ¯ i).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Lemma ga_lcontr_rscalar_base : bilinear_extend_rscalar_base ga_lcontr_base.
    intros a u v i j ui vj.
    unfold ga_lcontr_base.
    rewrite scalar_rmult.
    destruct (j ¯ i).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Lemma ga_rcontr_ldist_base : bilinear_extend_ldist_base ga_rcontr_base.
    intros u v w i j ui vj wj.
    unfold ga_rcontr_base.
    rewrite ldist.
    destruct (i ¯ j).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma ga_rcontr_rdist_base : bilinear_extend_rdist_base ga_rcontr_base.
    intros u v w i j ui vi wj.
    unfold ga_rcontr_base.
    rewrite rdist.
    destruct (i ¯ j).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma ga_rcontr_lscalar_base : bilinear_extend_lscalar_base ga_rcontr_base.
    intros a u v i j ui vj.
    unfold ga_rcontr_base.
    rewrite scalar_lmult.
    destruct (i ¯ j).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Lemma ga_rcontr_rscalar_base : bilinear_extend_rscalar_base ga_rcontr_base.
    intros a u v i j ui vj.
    unfold ga_rcontr_base.
    rewrite scalar_rmult.
    destruct (i ¯ j).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Definition ga_inner := bilinear_extend ga_inner_base : ga B → ga B → ga B.
Definition ga_lcontr := bilinear_extend ga_lcontr_base : ga B → ga B → ga B.
Definition ga_rcontr := bilinear_extend ga_rcontr_base : ga B → ga B → ga B.

Local Infix "•" := ga_inner (at level 34, left associativity).
Local Infix "⌋" := ga_lcontr (at level 34, left associativity).
Local Infix "⌊" := ga_rcontr (at level 34, left associativity).

Theorem inner_ldist : ∀ a b c, a • (b + c) = a • b + a • c.
    apply bilinear_extend_ldist.
    -   exact ga_inner_ldist_base.
    -   exact ga_inner_rscalar_base.
Qed.

Theorem inner_rdist : ∀ a b c, (a + b) • c = a • c + b • c.
    apply bilinear_extend_rdist.
    -   exact ga_inner_rdist_base.
    -   exact ga_inner_lscalar_base.
Qed.

Theorem inner_lscalar : ∀ a u v, (a · u) • v = a · (u • v).
    apply bilinear_extend_lscalar.
    -   apply ga_inner_rdist_base.
    -   apply ga_inner_lscalar_base.
Qed.

Theorem inner_rscalar : ∀ a u v, u • (a · v) = a · (u • v).
    apply bilinear_extend_rscalar.
    -   apply ga_inner_ldist_base.
    -   apply ga_inner_rscalar_base.
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
    -   exact ga_lcontr_ldist_base.
    -   exact ga_lcontr_rscalar_base.
Qed.

Theorem lcontr_rdist : ∀ a b c, (a + b) ⌋ c = a ⌋ c + b ⌋ c.
    apply bilinear_extend_rdist.
    -   exact ga_lcontr_rdist_base.
    -   exact ga_lcontr_lscalar_base.
Qed.

Theorem lcontr_lscalar : ∀ a u v, (a · u) ⌋ v = a · (u ⌋ v).
    apply bilinear_extend_lscalar.
    -   apply ga_lcontr_rdist_base.
    -   apply ga_lcontr_lscalar_base.
Qed.

Theorem lcontr_rscalar : ∀ a u v, u ⌋ (a · v) = a · (u ⌋ v).
    apply bilinear_extend_rscalar.
    -   apply ga_lcontr_ldist_base.
    -   apply ga_lcontr_rscalar_base.
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
    -   exact ga_rcontr_ldist_base.
    -   exact ga_rcontr_rscalar_base.
Qed.

Theorem rcontr_rdist : ∀ a b c, (a + b) ⌊ c = a ⌊ c + b ⌊ c.
    apply bilinear_extend_rdist.
    -   exact ga_rcontr_rdist_base.
    -   exact ga_rcontr_lscalar_base.
Qed.

Theorem rcontr_lscalar : ∀ a u v, (a · u) ⌊ v = a · (u ⌊ v).
    apply bilinear_extend_lscalar.
    -   apply ga_rcontr_rdist_base.
    -   apply ga_rcontr_lscalar_base.
Qed.

Theorem rcontr_rscalar : ∀ a u v, u ⌊ (a · v) = a · (u ⌊ v).
    apply bilinear_extend_rscalar.
    -   apply ga_rcontr_ldist_base.
    -   apply ga_rcontr_rscalar_base.
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
        u • v = ga_inner_base i j u v ui vj.
    intros i j u v ui vj.
    unfold ga_inner.
    apply bilinear_extend_homo.
    -   exact ga_inner_ldist_base.
    -   exact ga_inner_rdist_base.
    -   exact ga_inner_lscalar_base.
    -   exact ga_inner_rscalar_base.
Qed.

Lemma lcontr_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
        u ⌋ v = ga_lcontr_base i j u v ui vj.
    intros i j u v ui vj.
    unfold ga_lcontr.
    apply bilinear_extend_homo.
    -   exact ga_lcontr_ldist_base.
    -   exact ga_lcontr_rdist_base.
    -   exact ga_lcontr_lscalar_base.
    -   exact ga_lcontr_rscalar_base.
Qed.

Lemma rcontr_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
        u ⌊ v = ga_rcontr_base i j u v ui vj.
    intros i j u v ui vj.
    unfold ga_rcontr.
    apply bilinear_extend_homo.
    -   exact ga_rcontr_ldist_base.
    -   exact ga_rcontr_rdist_base.
    -   exact ga_rcontr_lscalar_base.
    -   exact ga_rcontr_rscalar_base.
Qed.

End GeometricInner.

Infix "•" := (ga_inner _) (at level 34, left associativity) : ga_scope.
Infix "⌋" := (ga_lcontr _) (at level 34, left associativity) : ga_scope.
Infix "⌊" := (ga_rcontr _) (at level 34, left associativity) : ga_scope.
