Require Import init.

Require Import set.
Require Import mult_characteristic.

Require Import linear_base.

(** WARNING: This is actually a symmetric bilinear form!  I don't care about
nonsymmetric bilinear forms right now so I'm just making all bilinear forms
symmetric for now.  I'll change it later if I want to change it.
*)
Definition bilinear_form {U V} `{Plus U, Mult U, Plus V, ScalarMult U V}
    (f : V → V → U) :=
    (∀ a v1 v2, f (a · v1) v2 = a * (f v1 v2)) ∧
    (∀ a v1 v2, f v1 (a · v2) = a * (f v1 v2)) ∧
    (∀ v1 v2 v3, f (v1 + v2) v3 = f v1 v3 + f v2 v3) ∧
    (∀ v1 v2 v3, f v1 (v2 + v3) = f v1 v2 + f v1 v3) ∧
    (∀ v1 v2, f v1 v2 = f v2 v1).

Definition degenerate_bilinear_form
    {U V} `{Plus U, Zero U, Mult U, Plus V, Zero V, ScalarMult U V}
    (f : set_type bilinear_form) := ∃ x, 0 ≠ x ∧ ∀ y, 0 = [f|] x y.

(* begin hide *)
Section BilinearForm.

Context {U V} `{
    UP : Plus U,
    UN : Neg U,
    UZ : Zero U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @Ldist U UP UM,
    @Rdist U UP UM,
    @MultAssoc U UM,
    @MultLid U UM UO,
    @MultLcancel U UZ UM,
    @CharacteristicNot U 2 UP UZ UO,
    Plus V,
    Zero V,
    ScalarMult U V
}.
(* end hide *)
Variable f : set_type bilinear_form.

Theorem bilinear_form_lscalar : ∀ a v1 v2, [f|] (a · v1) v2 = a * ([f|] v1 v2).
    apply [|f].
Qed.
Theorem bilinear_form_rscalar : ∀ a v1 v2, [f|] v1 (a · v2) = a * ([f|] v1 v2).
    apply [|f].
Qed.
Theorem bilinear_form_lplus : ∀ v1 v2 v3,
        [f|] (v1 + v2) v3 = [f|] v1 v3 + [f|] v2 v3.
    apply [|f].
Qed.
Theorem bilinear_form_rplus : ∀ v1 v2 v3,
        [f|] v1 (v2 + v3) = [f|] v1 v2 + [f|] v1 v3.
    apply [|f].
Qed.
Theorem bilinear_form_comm : ∀ v1 v2,
        [f|] v1 v2 = [f|] v2 v1.
    apply [|f].
Qed.

Theorem nondegenerate_nz_ex :
        (∃ x, 0 ≠ x) → ¬degenerate_bilinear_form f →
        ∃ x, 0 ≠ [f|] x x.
    intros [x x_nz] f_non.
    unfold degenerate_bilinear_form in f_non.
    rewrite not_ex in f_non.
    specialize (f_non x).
    rewrite not_and, not_not in f_non.
    destruct f_non as [C|f_non]; [>contradiction|].
    rewrite not_all in f_non.
    destruct f_non as [y nz].
    pose proof (Logic.eq_refl ([f|] (x + y) (x + y))) as eq.
    rewrite bilinear_form_lplus in eq at 1.
    do 2 rewrite bilinear_form_rplus in eq.
    rewrite (bilinear_form_comm y x) in eq.
    clear x_nz.
    classic_case (0 = [f|] x x) as [x_z|x_nz].
    2: {
        exists x.
        exact x_nz.
    }
    rewrite <- x_z in eq.
    rewrite plus_lid in eq.
    classic_case (0 = [f|] y y) as [y_z|y_nz].
    2: {
        exists y.
        exact y_nz.
    }
    rewrite <- y_z in eq.
    rewrite plus_rid in eq.
    classic_case (0 = [f|] (x + y) (x + y)) as [xy_z|xy_nz].
    2: {
        exists (x + y).
        exact xy_nz.
    }
    rewrite <- xy_z in eq.
    clear x_z y_z xy_z.
    rewrite <- (mult_lid ([f|] x y)) in eq.
    rewrite <- rdist in eq.
    rewrite <- (mult_ranni 2) in eq.
    apply mult_lcancel in eq; [>|apply two_nz].
    symmetry in eq; contradiction.
Qed.
(* begin hide *)

End BilinearForm.
(* end hide *)
