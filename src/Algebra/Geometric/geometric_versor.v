Require Import init.

Require Export geometric_construct.
Require Import geometric_involutions.
Require Import geometric_involutions_grade.
Require Import geometric_grade.
Require Import geometric_norm.
Require Import geometric_product_formulae.

(* begin hide *)
Section GeometricVersor.

(* end hide *)
Context {F : CRingObj} {V : ModuleObj F}.
(* begin hide *)

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

(* end hide *)
Context (B : set_type bilinear_form).

(* begin hide *)
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

Local Open Scope geo_scope.

(* end hide *)
Definition versor (A : geo B) := ∃ l : list (module_V V),
        A = list_prod (list_image l φ).

Theorem versor_reverse : ∀ A, versor A → versor (A†).
Proof.
    intros A [l l_eq]; subst A.
    exists (list_reverse l).
    induction l.
    -   cbn.
        apply geo_reverse_one.
    -   cbn.
        rewrite geo_reverse_mult.
        rewrite IHl.
        rewrite list_reverse_add.
        rewrite list_image_conc.
        rewrite list_image_single.
        rewrite list_prod_mult.
        cbn.
        rewrite geo_reverse_vector.
        rewrite mult_rid.
        reflexivity.
Qed.

Theorem versor_norm2 : ∀ A, versor A → A† * A = σ (geo_norm2 B A).
Proof.
    intros A [l A_eq]; subst A.
    unfold geo_norm2.
    rewrite scalar_part_eq.
    symmetry; apply grade_project_of_grade.
    induction l.
    -   cbn.
        rewrite mult_rid.
        rewrite geo_reverse_one.
        rewrite <- scalar_to_geo_one.
        apply scalar_to_geo_grade.
    -   cbn.
        rewrite geo_reverse_mult.
        rewrite geo_reverse_vector.
        rewrite <- mult_assoc.
        rewrite (mult_assoc (φ a)).
        rewrite geo_contract.
        rewrite scalar_lmult.
        rewrite scalar_rmult.
        apply of_grade_scalar.
        rewrite mult_lid.
        exact IHl.
Qed.

Theorem versor_norm2_2 : ∀ A, versor A → A * A† = σ (geo_norm2 B A).
Proof.
    intros A A_versor.
    rewrite <- (geo_reverse_reverse B A) at 1.
    rewrite versor_norm2 by (exact (versor_reverse _ A_versor)).
    unfold geo_norm2.
    rewrite <- geo_reverse_mult.
    rewrite scalar_part_reverse.
    rewrite scalar_part_comm.
    reflexivity.
Qed.

Lemma vector_sandwich_grade : ∀ a,
    ∀ (X : geo B) (n : nat), of_grade n X → of_grade n (φ a * X * φ a).
Proof.
    intros a X n Xn.
    rewrite <- mult_assoc.
    rewrite vector_lmult.
    rewrite vector_rmult.
    rewrite lcontr_ldist, outer_ldist.
    pose proof (vector_to_geo_grade B a) as a1.
    repeat apply of_grade_plus.
    -   rewrite <- (geo_reverse_reverse B (X ⌊ φ a)).
        rewrite rlcontr_reverse.
        rewrite geo_reverse_vector.
        nat_destruct n.
        +   apply geo_grade_zero_scalar in Xn as [α eq]; subst X.
            rewrite geo_reverse_of_scalar.
            rewrite lcontr_vector_scalar.
            rewrite geo_reverse_zero.
            rewrite lcontr_ranni.
            apply of_grade_zero.
        +   assert (of_grade n (φ a ⌋ X †)) as Xn'.
            {
                apply of_grade_reverse in Xn.
                rewrite (lcontr_homo _ _ _ _ _ a1 Xn).
                unfold geo_lcontr_base.
                unfold one at 1; cbn.
                change nat_zero with (zero (U := nat)).
                rewrite nat_minus_zero.
                apply grade_project_grade.
            }
            rewrite (geo_reverse_grade _ _ _ Xn').
            rewrite lcontr_rscalar.
            rewrite lcontr_twice.
            rewrite scalar_ranni.
            apply of_grade_zero.
    -   rewrite (outer_homo _ _ _ _ _ Xn a1).
        unfold geo_outer_base.
        rewrite (lcontr_homo _ _ _ _ _ a1 (grade_project_grade _ _)).
        unfold geo_lcontr_base.
        rewrite plus_comm.
        rewrite nat_minus_plus.
        apply grade_project_grade.
    -   nat_destruct n.
        +   apply geo_grade_zero_scalar in Xn as [α eq]; subst X.
            rewrite rcontr_scalar_vector.
            rewrite outer_ranni.
            apply of_grade_zero.
        +   rewrite (rcontr_homo _ _ _ _ _ Xn a1).
            unfold geo_rcontr_base.
            unfold one at 1; cbn.
            change nat_zero with (zero (U := nat)).
            rewrite nat_minus_zero.
            rewrite (outer_homo _ _ _ _ _ a1 (grade_project_grade _ _)).
            unfold geo_outer_base.
            apply grade_project_grade.
    -   rewrite outer_involute_swap.
        rewrite outer_involute.
        rewrite geo_involute_vector.
        rewrite <- scalar_neg_one.
        rewrite <- outer_assoc.
        rewrite outer_lscalar.
        rewrite outer_alternating.
        rewrite scalar_ranni.
        rewrite outer_ranni.
        apply of_grade_zero.
Qed.

Theorem versor_sandwich_grade : ∀ A, versor A →
    ∀ (X : geo B) (n : nat), of_grade n X → of_grade n (A† * X * A).
Proof.
    intros A [l A_eq] X n Xn; subst A.
    revert X Xn.
    induction l; intros.
    -   cbn.
        rewrite geo_reverse_one.
        rewrite mult_lid, mult_rid.
        exact Xn.
    -   cbn.
        rewrite geo_reverse_mult.
        rewrite geo_reverse_vector.
        rewrite mult_assoc.
        rewrite <- (mult_assoc _ X).
        rewrite <- (mult_assoc _ (φ a)).
        rewrite (mult_assoc _ X).
        apply IHl.
        apply vector_sandwich_grade.
        exact Xn.
Qed.

Theorem versor_outermorphism : ∀ A, versor A → ∀ (X Y : geo B),
    (A† * X * A) ⋀ (A† * Y * A) = geo_norm2 B A · (A† * (X ⋀ Y) * A).
Proof.
    intros A A_versor X Y.
    induction X as [|X X' m Xm X'm IHX] using grade_induction.
    {
        rewrite mult_ranni, mult_lanni.
        rewrite outer_lanni.
        rewrite outer_lanni.
        rewrite mult_ranni, mult_lanni.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite ldist, rdist.
    rewrite outer_rdist.
    rewrite IHX; clear IHX.
    rewrite outer_rdist.
    rewrite ldist, rdist.
    rewrite scalar_ldist.
    apply rplus; clear X' X'm.
    induction Y as [|Y Y' n Yn Y'n IHY] using grade_induction.
    {
        rewrite mult_ranni, mult_lanni.
        rewrite outer_ranni.
        rewrite outer_ranni.
        rewrite mult_ranni, mult_lanni.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite ldist, rdist.
    rewrite outer_ldist.
    rewrite IHY; clear IHY.
    rewrite outer_ldist.
    rewrite ldist, rdist.
    rewrite scalar_ldist.
    apply rplus; clear Y' Y'n.
    pose proof (versor_sandwich_grade A A_versor X m Xm) as AXm.
    pose proof (versor_sandwich_grade A A_versor Y n Yn) as AYn.
    rewrite (outer_homo _ _ _ _ _ AXm AYn).
    rewrite (outer_homo _ _ _ _ _ Xm Yn).
    unfold geo_outer_base.
    rewrite <- mult_assoc.
    do 2 rewrite (mult_assoc A).
    rewrite versor_norm2_2 by exact A_versor.
    rewrite scalar_to_geo_scalar.
    rewrite scalar_lmult.
    rewrite scalar_rmult.
    rewrite grade_project_scalar.
    apply lscalar.
    rewrite <- mult_assoc.
    rewrite (mult_assoc X).
    remember (X * Y) as x.
    clear X Y Xm Yn AXm AYn Heqx.
    induction x as [|x x' i xi x'i IHx] using grade_induction.
    {
        rewrite mult_lanni, mult_ranni.
        rewrite grade_project_zero.
        rewrite mult_ranni, mult_lanni.
        reflexivity.
    }
    rewrite rdist, ldist.
    rewrite grade_project_plus.
    rewrite IHx; clear IHx.
    rewrite grade_project_plus.
    rewrite ldist, rdist.
    apply rplus; clear x' x'i.
    rewrite mult_assoc.
    pose proof (versor_sandwich_grade A A_versor x i xi) as Axi.
    classic_case (i = m + n) as [eq|neq].
    -   subst i.
        rewrite (grade_project_of_grade _ _ xi).
        apply (grade_project_of_grade _ _ Axi).
    -   rewrite (grade_project_of_grade_neq _ _ _ xi neq).
        rewrite (grade_project_of_grade_neq _ _ _ Axi neq).
        rewrite mult_ranni, mult_lanni.
        reflexivity.
Qed.
(* begin hide *)

End GeometricVersor.
(* end hide *)
