Require Import init.

Require Import mult_product.
Require Import mult_pow.

Require Export geometric_construct.
Require Import geometric_exterior_isomorphism.
Require Import geometric_grade.
Require Import exterior_grade.
Require Export geometric_involutions.
Require Import exterior_involutions.

Section GeometricInvolutions.

Context {F : CRing} {V : Module F}.

Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UL := cring_ldist F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.

Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UL UMA UMC UMO.

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
Let ESC := ext_scalar_comp V.
Let ESML := ext_scalar_lmult V.
Let ESMR := ext_scalar_rmult V.
Let EG := exterior_grade V.
Let EGA := exterior_grade_mult V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO EL ER EML EMR EMA ES ESO ESL
    ESR ESC ESML ESMR EG EGA.

Local Open Scope geo_scope.
Local Open Scope nat_scope.

Theorem geo_mult_inner_involute : ∀ a (X : geo B),
        (geo_mult_inner B a X)∗ = -geo_mult_inner B a (X∗).
    intros a X.
    pose proof (geo_sum B X) as [l l_eq]; subst X.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite geo_involute_zero.
        rewrite geo_mult_inner_rzero.
        rewrite neg_zero, geo_involute_zero.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite geo_involute_plus.
    do 2 rewrite geo_mult_inner_rplus.
    rewrite geo_involute_plus.
    rewrite IHl; clear IHl.
    rewrite neg_plus.
    apply rplus; clear l.
    rewrite geo_involute_scalar.
    do 2 rewrite geo_mult_inner_rscalar.
    rewrite geo_involute_scalar.
    rewrite <- scalar_rneg.
    apply lscalar; clear α.
    induction x as [|v l].
    {
        cbn.
        rewrite geo_involute_one.
        rewrite <- scalar_to_geo_one.
        rewrite geo_mult_inner_scalar.
        rewrite neg_zero, geo_involute_zero.
        reflexivity.
    }
    cbn.
    rewrite geo_involute_mult.
    rewrite geo_involute_vector.
    rewrite mult_lneg.
    rewrite geo_mult_inner_rneg.
    rewrite neg_neg.
    do 2 rewrite geo_mult_inner_add.
    rewrite geo_involute_plus.
    rewrite geo_involute_neg.
    rewrite geo_involute_mult.
    rewrite IHl; clear IHl.
    rewrite geo_involute_vector.
    rewrite mult_lneg, mult_rneg.
    rewrite neg_neg.
    rewrite geo_involute_scalar.
    reflexivity.
Qed.

Theorem ext_to_geo_involute : ∀ X, (G X)∗ = G (ext_involute X).
    intros X.
    pose proof (ext_sum V X) as [l l_eq]; subst X.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ext_involute_zero.
        rewrite ext_to_geo_zero.
        apply geo_involute_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_involute_plus.
    do 2 rewrite ext_to_geo_plus.
    rewrite geo_involute_plus.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite ext_involute_scalar.
    do 2 rewrite ext_to_geo_scalar.
    rewrite geo_involute_scalar.
    apply lscalar; clear α.
    induction x as [|v l].
    {
        cbn.
        rewrite ext_involute_one.
        rewrite ext_to_geo_one.
        apply geo_involute_one.
    }
    cbn.
    rewrite ext_involute_mult.
    rewrite ext_involute_vector.
    rewrite mult_lneg.
    rewrite ext_to_geo_neg.
    do 2 rewrite ext_to_geo_add.
    rewrite geo_involute_plus.
    rewrite geo_involute_neg.
    rewrite geo_mult_inner_involute.
    rewrite neg_neg.
    rewrite geo_involute_mult.
    rewrite IHl; clear IHl.
    rewrite geo_involute_vector.
    rewrite neg_plus.
    rewrite neg_neg.
    rewrite mult_lneg.
    reflexivity.
Qed.

Theorem geo_to_ext_involute : ∀ X : geo B, ext_involute (E X) = E (X∗).
    intros X.
    rewrite <- (geo_to_ext_to_geo B (ext_involute (E X))).
    rewrite <- ext_to_geo_involute.
    rewrite ext_to_geo_to_ext.
    reflexivity.
Qed.

Theorem vector_bilinear_eq : ∀ a b, φ a * φ b + φ b * φ a = [B|] a b · 2.
    intros a b.
    apply plus_lcancel with (φ a * φ a).
    apply plus_rcancel with (φ b * φ b).
    rewrite scalar_ldist.
    rewrite bilinear_form_comm at 2.
    rewrite plus_assoc.
    rewrite <- ldist.
    rewrite <- plus_assoc.
    rewrite <- ldist.
    rewrite <- rdist.
    rewrite <- vector_to_geo_plus.
    do 3 rewrite geo_contract.
    rewrite bilinear_form_lplus.
    do 2 rewrite bilinear_form_rplus.
    do 2 rewrite plus_assoc.
    do 3 rewrite scalar_rdist.
    reflexivity.
Qed.

Local Arguments of_grade : simpl never.

Theorem ext_inner_grade : ∀ v (A : ext V) i, of_grade (nat_suc i) A
        → of_grade i (ext_inner B v A).
    intros v A i Ai.
    apply ext_grade_sum in Ai as [l A_eq]; subst A.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ext_inner_rzero.
        apply of_grade_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_inner_rplus.
    apply of_grade_plus; [>clear l IHl|exact IHl].
    rewrite ext_inner_rscalar.
    apply of_grade_scalar; clear α.
    destruct x as [l l_size]; cbn.
    revert l l_size.
    nat_induction i; intros.
    {
        destruct l as [|a l]; [>inversion l_size|].
        destruct l; [>|inversion l_size].
        clear l_size.
        cbn.
        rewrite mult_rid.
        rewrite ext_inner_vector.
        apply of_grade_scalar.
        rewrite <- scalar_to_ext_one.
        apply scalar_to_ext_grade.
    }
    destruct l as [|a l].
    {
        cbn.
        rewrite <- scalar_to_ext_one.
        rewrite ext_inner_scalar.
        apply of_grade_zero.
    }
    cbn.
    inversion l_size as [l_size'].
    rewrite ext_inner_add.
    apply of_grade_plus.
    -   apply of_grade_scalar.
        apply ext_list_grade.
    -   apply of_grade_neg.
        rewrite l_size'.
        change (nat_suc i) with (1 + i).
        apply (grade_mult (GradedAlgebra := EGA)).
        +   apply vector_to_ext_grade.
        +   apply IHi.
            exact l_size'.
Qed.

Theorem geo_mult_inner_swap : ∀ a (X : geo B),
        2 · geo_mult_inner B a X = φ a * X - X∗ * φ a.
    intros a X.
    pose proof (geo_sum B X) as [l l_eq]; subst X.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite geo_mult_inner_rzero.
        rewrite geo_involute_zero.
        rewrite scalar_ranni, mult_ranni, mult_lanni.
        rewrite neg_zero, plus_lid.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite geo_mult_inner_rplus.
    rewrite scalar_ldist.
    rewrite IHl; clear IHl.
    rewrite ldist.
    rewrite geo_involute_plus.
    rewrite (rdist _ _ (φ a)).
    rewrite neg_plus.
    do 2 rewrite plus_assoc.
    apply rplus.
    rewrite <- plus_assoc.
    rewrite (plus_comm _ (-_)).
    rewrite plus_assoc.
    apply rplus; clear l.
    rewrite geo_mult_inner_rscalar.
    rewrite scalar_rmult.
    rewrite scalar_comp.
    rewrite mult_comm.
    rewrite <- scalar_comp.
    rewrite geo_involute_scalar.
    rewrite scalar_lmult.
    rewrite <- scalar_rneg.
    rewrite <- scalar_ldist.
    apply lscalar; clear α.
    induction x as [|b l].
    {
        cbn.
        rewrite <- scalar_to_geo_one at 1.
        rewrite geo_mult_inner_scalar.
        rewrite scalar_ranni.
        rewrite geo_involute_one.
        rewrite mult_lid, mult_rid.
        rewrite plus_rinv.
        reflexivity.
    }
    cbn.
    remember (list_prod (list_image l (λ v, φ v))) as X.
    clear HeqX.
    rewrite geo_mult_inner_add.
    rewrite scalar_ldist.
    rewrite <- mult_lneg.
    rewrite <- scalar_rmult.
    rewrite IHl; clear IHl.
    rewrite ldist.
    rewrite mult_lneg, mult_lneg, mult_rneg.
    rewrite neg_neg.
    rewrite geo_involute_mult.
    rewrite geo_involute_vector.
    do 2 rewrite mult_lneg.
    rewrite neg_neg.
    do 2 rewrite mult_assoc.
    rewrite plus_assoc.
    apply rplus.
    rewrite scalar_comp.
    rewrite <- scalar_to_geo_scalar.
    rewrite (mult_comm 2).
    rewrite scalar_to_geo_mult.
    rewrite scalar_to_geo_scalar.
    rewrite scalar_to_geo_plus.
    rewrite scalar_to_geo_one.
    rewrite <- mult_lneg.
    rewrite <- rdist.
    rewrite mult_assoc.
    apply rmult; clear X.
    apply plus_rrmove.
    symmetry; apply vector_bilinear_eq.
Qed.

Theorem ext_to_geo_reverse : ∀ X : ext V, (G X)† = G (ext_reverse X).
    intros X.
    induction X as [|X X' n Xn X'n IHX] using grade_induction.
    {
        rewrite ext_reverse_zero.
        do 2 rewrite ext_to_geo_zero.
        apply geo_reverse_zero.
    }
    rewrite ext_reverse_plus.
    do 2 rewrite ext_to_geo_plus.
    rewrite geo_reverse_plus.
    rewrite IHX; clear IHX.
    apply rplus; clear X' X'n.
    revert X Xn.
    induction n as [n IHn] using strong_induction.
    intros X Xn.
    pose proof (ext_grade_sum _ _ _ Xn) as [l l_eq]; subst X.
    clear Xn.
    induction l as [|[α x] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ext_reverse_zero.
        rewrite ext_to_geo_zero.
        apply geo_reverse_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_reverse_plus.
    do 2 rewrite ext_to_geo_plus.
    rewrite geo_reverse_plus.
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    rewrite ext_reverse_scalar.
    do 2 rewrite ext_to_geo_scalar.
    rewrite geo_reverse_scalar.
    apply lscalar; clear α.
    destruct x as [l ln]; cbn.
    destruct l as [|a l].
    {
        cbn.
        rewrite ext_reverse_one.
        do 2 rewrite ext_to_geo_one.
        apply geo_reverse_one.
    }
    cbn.
    nat_destruct n; [>inversion ln|].
    remember (list_prod (list_image l (vector_to_ext V))) as X.
    assert (of_grade n X) as Xn.
    {
        inversion ln.
        rewrite HeqX.
        apply ext_list_grade.
    }
    clear HeqX l ln.
    assert (of_grade (nat_suc n) (vector_to_ext V a * X)) as aXn.
    {
        change (nat_suc n) with (1 + n).
        apply (of_grade_mult _ _ _ _ (vector_to_ext_grade V a) Xn).
    }
    rewrite (ext_reverse_grade _ _ aXn).
    rewrite ext_to_geo_scalar.
    do 2 rewrite ext_to_geo_add.
    rewrite geo_reverse_plus.
    rewrite geo_reverse_neg.
    rewrite geo_reverse_mult.
    rewrite geo_reverse_vector.
    rewrite (IHn n (nat_lt_suc n) _ Xn).
    rewrite (ext_reverse_grade _ _ Xn).
    rewrite ext_to_geo_scalar.
    rewrite <- (ext_to_geo_to_ext B (geo_mult_inner B a (G X))) at 1.
    rewrite geo_to_ext_inner.
    rewrite geo_to_ext_to_geo.
    nat_destruct n.
    {
        apply ext_grade_zero_scalar in Xn as [α X_eq]; subst X.
        rewrite ext_inner_scalar.
        rewrite ext_to_geo_zero.
        rewrite geo_reverse_zero.
        rewrite neg_zero, plus_lid.
        rewrite ext_to_geo_of_scalar.
        rewrite geo_mult_inner_scalar.
        rewrite neg_zero, plus_lid.
        rewrite binom_greater by apply nat_zero_lt_suc.
        rewrite binom_greater by (rewrite nat_sucs_lt; apply nat_zero_lt_suc).
        rewrite pow_0_nat.
        do 2 rewrite scalar_id.
        apply scalar_to_geo_comm.
    }
    pose proof (ext_inner_grade a X n Xn) as aXn'.
    pose proof (trans (nat_lt_suc n) (nat_lt_suc (nat_suc n))) as ltq.
    rewrite (IHn n ltq _ aXn').
    rewrite (ext_reverse_grade _ _ aXn').
    rewrite ext_to_geo_scalar.
    rewrite ext_to_geo_inner.
    rewrite (pow_neg_one_binom2 n).
    pose proof (geo_mult_inner_swap a (G X)) as eq.
    rewrite <- plus_lrmove in eq.
    rewrite <- eq; clear eq.
    rewrite scalar_rdist.
    rewrite scalar_id.
    rewrite plus_assoc.
    rewrite plus_llinv.
    rewrite scalar_ldist.
    rewrite scalar_lneg.
    apply lplus.
    rewrite ext_to_geo_involute.
    rewrite (ext_involute_grade _ _ Xn).
    rewrite ext_to_geo_scalar.
    do 2 rewrite scalar_lmult.
    rewrite scalar_comp.
    apply rscalar.
    change 2 with (nat_suc 1) at 1.
    rewrite binom_suc.
    rewrite binom_one.
    rewrite plus_comm.
    rewrite mult_lneg.
    rewrite pow_mult_nat.
    rewrite nat_plus_rsuc.
    rewrite pow_simpl.
    rewrite mult_comm.
    rewrite mult_neg_one.
    rewrite neg_neg.
    reflexivity.
Qed.

Theorem geo_to_ext_reverse : ∀ X : geo B, ext_reverse (E X) = E (X†).
    intros X.
    rewrite <- (geo_to_ext_to_geo B (ext_reverse (E X))).
    rewrite <- ext_to_geo_reverse.
    rewrite ext_to_geo_to_ext.
    reflexivity.
Qed.

Theorem geo_involute_grade : ∀ (X : geo B) (n : nat), of_grade (H10 := GG) n X →
        X∗ = (-(1))^n · X.
    intros X' n [X [Xn X_eq]]; subst X'.
    cbn.
    rewrite ext_to_geo_involute.
    rewrite (ext_involute_grade _ _ Xn).
    apply ext_to_geo_scalar.
Qed.

Theorem geo_reverse_grade : ∀ (X : geo B) (n : nat), of_grade (H10 := GG) n X →
        X† = (-(1))^(binom n 2) · X.
    intros X' n [X [Xn X_eq]]; subst X'.
    cbn.
    rewrite ext_to_geo_reverse.
    rewrite (ext_reverse_grade _ _ Xn).
    apply ext_to_geo_scalar.
Qed.

Theorem of_grade_involute : ∀ (X : geo B) n, of_grade n X → of_grade n (X∗).
    intros X n Xn.
    rewrite (geo_involute_grade _ _ Xn).
    apply of_grade_scalar.
    exact Xn.
Qed.

Theorem of_grade_reverse : ∀ (X : geo B) n, of_grade n X → of_grade n (X†).
    intros X n Xn.
    rewrite (geo_reverse_grade _ _ Xn).
    apply of_grade_scalar.
    exact Xn.
Qed.

Theorem geo_involute_project : ∀ (X : geo B) n,
        (grade_project X n)∗ = grade_project (X∗) n.
    intros X n.
    induction X as [|X X' i Xi X'i IHX] using grade_induction.
    {
        rewrite grade_project_zero.
        do 2 rewrite geo_involute_zero.
        rewrite grade_project_zero.
        reflexivity.
    }
    rewrite grade_project_plus.
    do 2 rewrite geo_involute_plus.
    rewrite grade_project_plus.
    rewrite IHX; clear IHX.
    apply rplus; clear X' X'i.
    pose proof (of_grade_involute _ _ Xi) as Xi'.
    classic_case (i = n) as [eq|neq].
    {
        subst.
        rewrite (grade_project_of_grade _ _ Xi).
        rewrite (grade_project_of_grade _ _ Xi').
        reflexivity.
    }
    rewrite (grade_project_of_grade_neq _ _ _ Xi neq).
    rewrite (grade_project_of_grade_neq _ _ _ Xi' neq).
    apply geo_involute_zero.
Qed.

Theorem geo_reverse_project : ∀ (X : geo B) n,
        (grade_project X n)† = grade_project (X†) n.
    intros X n.
    induction X as [|X X' i Xi X'i IHX] using grade_induction.
    {
        rewrite grade_project_zero.
        do 2 rewrite geo_reverse_zero.
        rewrite grade_project_zero.
        reflexivity.
    }
    rewrite grade_project_plus.
    do 2 rewrite geo_reverse_plus.
    rewrite grade_project_plus.
    rewrite IHX; clear IHX.
    apply rplus; clear X' X'i.
    pose proof (of_grade_reverse _ _ Xi) as Xi'.
    classic_case (i = n) as [eq|neq].
    {
        subst.
        rewrite (grade_project_of_grade _ _ Xi).
        rewrite (grade_project_of_grade _ _ Xi').
        reflexivity.
    }
    rewrite (grade_project_of_grade_neq _ _ _ Xi neq).
    rewrite (grade_project_of_grade_neq _ _ _ Xi' neq).
    apply geo_reverse_zero.
Qed.

Theorem geo_reverse_involute : ∀ X : geo B, X†∗ = X∗†.
    intros X.
    induction X as [|X X' n Xn X'n IHX] using grade_induction.
    {
        rewrite geo_involute_zero.
        do 2 rewrite geo_reverse_zero.
        apply geo_involute_zero.
    }
    rewrite geo_involute_plus.
    do 2 rewrite geo_reverse_plus.
    rewrite geo_involute_plus.
    rewrite IHX; clear IHX.
    apply rplus; clear X' X'n.
    rewrite (geo_reverse_grade _ _ Xn).
    rewrite (geo_involute_grade _ _ Xn).
    rewrite geo_reverse_scalar.
    rewrite geo_involute_scalar.
    rewrite (geo_reverse_grade _ _ Xn).
    rewrite (geo_involute_grade _ _ Xn).
    do 2 rewrite scalar_comp.
    rewrite mult_comm.
    reflexivity.
Qed.

End GeometricInvolutions.
