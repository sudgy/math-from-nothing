Require Import init.

Require Export linear_grade.
Require Import linear_subspace.
Require Export module_category.
Require Import algebra_category.
Require Import set.
Require Import unordered_list.

Section Grade.

Context {U} {V1 V2 : Module U} {I : Type} `{GradedSpace U V1 I}.

Variables (f : morphism V1 V2) (g : morphism V2 V1)
    (iso : is_isomorphism_pair f g).

Lemma grade_iso_fg : ∀ x, f (g x) = x.
Proof.
    intros x.
    pose proof (land iso) as eq.
    cbn in eq.
    unfold module_homo_compose, module_homo_id in eq.
    inversion eq as [eq2].
    apply (func_eq _ _ eq2).
Qed.
Lemma grade_iso_gf : ∀ x, g (f x) = x.
Proof.
    intros x.
    pose proof (rand iso) as eq.
    cbn in eq.
    unfold module_homo_compose, module_homo_id in eq.
    inversion eq as [eq2].
    apply (func_eq _ _ eq2).
Qed.

Program Instance grade_isomorphism : GradedSpace V2 I := {
    grade_modules := grade_modules;
    grade_to := grade_to ∘ g;
    grade_from := f ∘ grade_from;
}.
Next Obligation.
    rewrite grade_iso_gf.
    apply grade_to_from.
Qed.
Next Obligation.
    rewrite grade_from_to.
    apply grade_iso_fg.
Qed.

Theorem grade_iso_to : ∀ v, grade_to v = grade_to (g v).
Proof.
    intros v.
    reflexivity.
Qed.

Theorem grade_iso_from :
    ∀ v, (grade_from v : V2) = f (grade_from (GradedSpace := H) v : V1).
Proof.
    intros v.
    reflexivity.
Qed.

Theorem grade_iso_f_project :
    ∀ i v, (grade_project (f v) i) = f (grade_project v i).
Proof.
    intros i v.
    unfold grade_project.
    rewrite <- grade_iso_from.
    rewrite grade_iso_to.
    rewrite grade_iso_gf.
    reflexivity.
Qed.

Theorem grade_iso_g_project :
    ∀ i v, (grade_project (g v) i) = g (grade_project v i).
Proof.
    intros i v.
    unfold grade_project.
    rewrite <- grade_iso_to.
    rewrite grade_iso_from.
    rewrite grade_iso_gf.
    reflexivity.
Qed.

Theorem of_grade_iso_f : ∀ i v, of_grade i v ↔ of_grade i (f v).
Proof.
    intros i v.
    unfold of_grade.
    rewrite grade_iso_f_project.
    rewrite f_eq_iff; [>reflexivity|].
    intros a b eq.
    apply (f_equal g) in eq.
    do 2 rewrite grade_iso_gf in eq.
    exact eq.
Qed.

Theorem of_grade_iso_g : ∀ i v, of_grade i v ↔ of_grade i (g v).
Proof.
    intros i v.
    unfold of_grade.
    rewrite grade_iso_g_project.
    rewrite f_eq_iff; [>reflexivity|].
    intros a b eq.
    apply (f_equal f) in eq.
    do 2 rewrite grade_iso_fg in eq.
    exact eq.
Qed.

End Grade.

Section GradeAlgebraObj.

Context {U : CRingObj} {V1 V2 : Algebra U} {I : Type}.
Context `{VG : GradedSpace U (algebra_module V1) I}.
Variables (f : morphism V1 V2) (g : morphism V2 V1)
    (iso : is_isomorphism_pair f g).

Context `{IP : Plus I}.
Context `{GA : @GradedAlgebra U V1 I VG IP}.

Lemma graded_algebra_inv : is_isomorphism_pair (C0 := Module U)
    (algebra_to_module_homomorphism f)
    (algebra_to_module_homomorphism g).
Proof.
    destruct iso as [fg gf].
    split.
    -   apply module_homomorphism_eq.
        intros x; cbn.
        inversion fg as [eq].
        apply (func_eq _ _ eq).
    -   apply module_homomorphism_eq.
        intros x; cbn.
        inversion gf as [eq].
        apply (func_eq _ _ eq).
Qed.

Let VG2 := grade_isomorphism _ _ graded_algebra_inv.
Existing Instance VG2.

Instance graded_algebra_isomorphism : GradedAlgebra V2 I.
Proof.
    split.
    intros u v i j iu jv.
    apply of_grade_iso_g.
    cbn.
    rewrite algebra_homo_mult.
    apply of_grade_mult.
    -   apply of_grade_iso_g in iu.
        exact iu.
    -   apply of_grade_iso_g in jv.
        exact jv.
Qed.

End GradeAlgebraObj.
