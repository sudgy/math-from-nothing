Require Import init.

Require Export linear_sum_module.
Require Export linear_grade.

Section LinearGradeSum.

Context {U : CRingObj}.
Variable (I : Type).
Variable (V : I → ModuleObj U).

Instance sum_module_grade : GradedSpace (sum_module I V) I := {
    grade_modules := V;
    grade_to := 𝟙;
    grade_from := 𝟙;
    grade_to_from _ := Logic.eq_refl;
    grade_from_to _ := Logic.eq_refl;
}.

End LinearGradeSum.
