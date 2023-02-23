Require Import init.

Require Import order_minmax.
Require Import mult_div.
Require Import nat_domain.

Require Export geometric_construct.
Require Import geometric_grade.
Require Import geometric_exterior_isomorphism.
Require Import exterior_grade.
Require Import geometric_involutions.
Require Import geometric_involutions_grade.

(* begin hide *)
Section GeometricDecompose.

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
Let EMR := ext_mult_rid V.
Let EMA := ext_mult_assoc V.
Let ES := ext_scalar V.
Let ESO := ext_scalar_id V.
Let ESL := ext_scalar_ldist V.
Let ESR := ext_scalar_rdist V.
Let EG := exterior_grade V.
Let EGA := exterior_grade_mult V.

Existing Instances EP EZ EN EPA EPC EPZ EPN EM EO EL ER EMR EMA ES ESO ESL ESR.

Local Open Scope geo_scope.
Local Open Scope nat_scope.

(* end hide *)
Theorem geo_mult_inner_grade : ∀ v (A : geo B) i, of_grade (nat_suc i) A
    → of_grade i (geo_mult_inner B v A).
Proof.
    intros v A' i [A [Ai A_eq]]; subst A'; cbn.
    rewrite <- ext_to_geo_inner.
    exists (ext_inner B v A).
    split; [>|reflexivity].
    apply ext_inner_grade.
    exact Ai.
Qed.

Theorem mult_inner_grade_add : ∀ v (A : geo B) n,
    grade_project (geo_mult_inner B v A) n =
    geo_mult_inner B v (grade_project A (nat_suc n)).
Proof.
    intros v A n.
    induction A as [|A A' i Ai A'i IHA] using grade_induction.
    {
        rewrite geo_mult_inner_rzero.
        do 2 rewrite grade_project_zero.
        rewrite geo_mult_inner_rzero.
        reflexivity.
    }
    rewrite geo_mult_inner_rplus.
    do 2 rewrite grade_project_plus.
    rewrite geo_mult_inner_rplus.
    rewrite IHA; clear IHA.
    apply rplus; clear A' A'i.
    classic_case (i = nat_suc n) as [eq|neq].
    -   subst i.
        rewrite (grade_project_of_grade _ _ Ai).
        rewrite (grade_project_of_grade _ _ (geo_mult_inner_grade _ _ _ Ai)).
        reflexivity.
    -   rewrite (grade_project_of_grade_neq _ _ _ Ai neq).
        rewrite geo_mult_inner_rzero.
        nat_destruct i.
        {
            apply geo_grade_zero_scalar in Ai as [α eq]; subst A.
            rewrite geo_mult_inner_scalar.
            apply grade_project_zero.
        }
        apply (geo_mult_inner_grade v) in Ai.
        assert (i ≠ n) as neq' by (intro; subst; contradiction).
        rewrite (grade_project_of_grade_neq _ _ _ Ai neq').
        reflexivity.
Qed.

(* begin hide *)
Existing Instances EG EGA.

(* end hide *)
Theorem exterior_grade_add : ∀ v (A : ext V) n,
    grade_project (vector_to_ext V v * A) (nat_suc n) =
    vector_to_ext V v * grade_project A n.
Proof.
    intros v A n.
    induction A as [|A A' i Ai A'i IHA] using grade_induction.
    {
        rewrite mult_ranni.
        do 2 rewrite grade_project_zero.
        rewrite mult_ranni.
        reflexivity.
    }
    rewrite ldist.
    do 2 rewrite grade_project_plus.
    rewrite ldist.
    rewrite IHA; clear IHA.
    apply rplus; clear A' A'i.
    assert (of_grade (nat_suc i) (vector_to_ext V v * A)) as Ai'.
    {
        change (nat_suc i) with (1 + i).
        apply of_grade_mult.
        -   apply vector_to_ext_grade.
        -   exact Ai.
    }
    classic_case (i = n) as [eq|neq].
    -   subst.
        rewrite (grade_project_of_grade _ _ Ai).
        rewrite (grade_project_of_grade _ _ Ai').
        reflexivity.
    -   rewrite (grade_project_of_grade_neq _ _ _ Ai neq).
        rewrite (grade_project_of_grade_neq _ _ _ Ai').
        2: intros contr; inversion contr; contradiction.
        rewrite mult_ranni.
        reflexivity.
Qed.

(* begin hide *)
Remove Hints EG EGA : typeclass_instances.

(* end hide *)
Lemma geo_grade_decompose1 : ∀ (a b : geo B) (r s n : nat),
    of_grade r a → of_grade s b → r ≤ s →
    (n < r ⊖ s ∨ r + s < n ∨ (∃ z, n = r ⊖ s + 2 * z + 1)) →
    grade_project (a * b) n = 0.
Proof.
    intros a b r s n ar bs leq n_lt.
    revert n n_lt a ar.
    induction r using strong_induction; intros.
    assert (∀ m c, m < r → s = m + c → ∀ n,
        (n < c ∨ m + s < n ∨ (∃ z, n = c + 2 * z + 1)) →
        ∀ a : geo B, of_grade m a → grade_project (a * b) n = 0) as H'.
    {
        clear n n_lt a ar.
        intros m c ltq s_eq n.
        subst s.
        specialize (H m ltq (nat_le_self_rplus m c) n).
        rewrite nat_abs_minus_comm in H.
        rewrite nat_abs_minus_plus in H.
        exact H.
    }
    clear H.
    apply nat_le_ex in leq as [c eq]; subst s.
    rewrite nat_abs_minus_comm in n_lt.
    rewrite nat_abs_minus_plus in n_lt.
    rename a into a'.
    destruct ar as [a [ar a_eq]]; subst a'.
    cbn.
    change (module_V (algebra_module (exterior_algebra V))) with (ext V) in a.
    rename ar into ar'.
    assert (of_grade (H10 := EG) r a) as ar by exact ar'.
    clear ar'.
    apply ext_grade_sum in ar as [l l_eq]; subst a.
    induction l as [|[α a] l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite ext_to_geo_zero.
        rewrite mult_lanni.
        apply grade_project_zero.
    }
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ext_to_geo_plus.
    rewrite rdist.
    rewrite grade_project_plus.
    rewrite IHl; clear IHl l.
    rewrite plus_rid.
    rewrite ext_to_geo_scalar.
    rewrite scalar_lmult.
    rewrite grade_project_scalar.
    rewrite <- (scalar_ranni α).
    apply lscalar.
    clear α.
    destruct a as [l l_size]; cbn.
    destruct l as [|v l].
    {
        cbn.
        rewrite ext_to_geo_one.
        rewrite mult_lid.
        assert (r + c ≠ n) as neq.
        {
            intros contr; subst n.
            cbn in l_size.
            subst r.
            clear - n_lt.
            do 2 rewrite plus_lid in n_lt.
            destruct n_lt as [lt|[lt|lt]].
            -   destruct lt; contradiction.
            -   destruct lt; contradiction.
            -   destruct lt as [z eq].
                pose proof (nat_le_self_rplus c (2*z)) as leq.
                rewrite <- nat_lt_suc_le in leq.
                rewrite plus_comm in eq.
                rewrite eq in leq at 1.
                destruct leq; contradiction.
        }
        exact (grade_project_of_grade_neq _ _ _ bs neq).
    }
    nat_destruct r; [>inversion l_size|].
    inversion l_size as [l_size'].
    cbn.
    rewrite ext_to_geo_add.
    rewrite rdist.
    rewrite grade_project_plus.
    rewrite <- (plus_rid 0).
    assert (of_grade r (G (list_prod (list_image l (vector_to_ext V)))))
        as l_grade.
    {
        exists (list_prod (list_image l (vector_to_ext V))).
        split; [>|reflexivity].
        rewrite <- l_size'.
        apply ext_list_grade.
    }
    apply lrplus.
    -   destruct l as [|v2 l].
        {
            cbn.
            rewrite ext_to_geo_one.
            rewrite <- scalar_to_geo_one.
            rewrite geo_mult_inner_scalar.
            rewrite neg_zero, mult_lanni.
            apply grade_project_zero.
        }
        nat_destruct r; [>inversion l_size'|].
        rewrite mult_lneg.
        rewrite grade_project_neg.
        pose proof (geo_mult_inner_grade v _ _ l_grade) as a_grade.
        specialize (H' r (nat_suc (nat_suc c))).
        specialize (H' (trans (nat_lt_suc _) (nat_lt_suc _))).
        do 2 rewrite nat_plus_rsuc in H'.
        do 2 rewrite nat_plus_lsuc in H'.
        specialize (H' Logic.eq_refl n).
        prove_parts H'.
        {
            classic_case (n = c + 1) as [n_eq|n_neq].
            {
                left.
                rewrite n_eq.
                rewrite plus_comm.
                apply nat_lt_suc.
            }
            destruct n_lt as [lt|[lt|lt]]; [>left|right;left|right;right].
            -   apply (trans lt).
                apply (trans (nat_lt_suc c)).
                apply nat_lt_suc.
            -   apply (trans2 lt).
                do 4 rewrite nat_plus_lsuc.
                do 2 rewrite nat_plus_rsuc.
                apply (trans (nat_lt_suc _)).
                apply nat_lt_suc.
            -   destruct lt as [z eq].
                nat_destruct z.
                +   rewrite mult_ranni, plus_rid in eq.
                    contradiction.
                +   exists z.
                    clear - eq.
                    do 4 rewrite nat_plus_lsuc.
                    rewrite eq.
                    rewrite nat_mult_rsuc.
                    rewrite plus_assoc.
                    rewrite (plus_comm c 2).
                    do 2 rewrite <- plus_assoc.
                    rewrite (plus_assoc c).
                    reflexivity.
        }
        specialize (H' _ a_grade).
        rewrite H'.
        apply neg_zero.
    -   rewrite <- mult_assoc.
        rewrite <- (ext_to_geo_to_ext B (φ v * _)).
        rewrite geo_to_ext_add.
        rewrite ext_to_geo_plus.
        rewrite grade_project_plus.
        rewrite <- (plus_rid 0).
        specialize (H' r (nat_suc c) (nat_lt_suc r)).
        rewrite nat_plus_lsuc, nat_plus_rsuc in H'.
        specialize (H' Logic.eq_refl).
        apply lrplus.
        +   rewrite ext_to_geo_inner.
            rewrite ext_to_geo_to_ext.
            rewrite mult_inner_grade_add.
            specialize (H' (nat_suc n)).
            rewrite nat_plus_rsuc in H'.
            do 2 rewrite nat_sucs_lt in H'.
            prove_parts H'.
            {
                destruct n_lt as [lt|[lt|lt]];
                    [>left; exact lt|right; left|right; right].
                -   apply (trans2 lt).
                    do 2 rewrite nat_plus_lsuc.
                    rewrite nat_plus_rsuc.
                    apply (trans (nat_lt_suc _)).
                    apply nat_lt_suc.
                -   destruct lt as [z eq].
                    exists z.
                    clear - eq.
                    rewrite eq.
                    do 2 rewrite nat_plus_lsuc.
                    reflexivity.
            }
            specialize (H' _ l_grade).
            rewrite H'.
            apply geo_mult_inner_rzero.
        +   rewrite ext_to_geo_project.
            nat_destruct n.
            {
                remember (E _) as A.
                clear HeqA.
                induction A as [|A A' i Ai A'i IHA]
                    using (grade_induction (VG := EG)).
                -   rewrite mult_ranni.
                    rewrite grade_project_zero.
                    apply ext_to_geo_zero.
                -   rewrite ldist.
                    rewrite grade_project_plus.
                    rewrite ext_to_geo_plus.
                    rewrite IHA; clear A' A'i IHA.
                    assert (of_grade (H10 := EG) (nat_suc i)
                        (vector_to_ext V v * A)) as A_grade.
                    {
                        change (nat_suc i) with (1 + i).
                        apply (of_grade_mult (H14 := EGA)).
                        -   apply vector_to_ext_grade.
                        -   exact Ai.
                    }
                    assert (nat_suc i ≠ 0) as neq
                        by (intros contr; inversion contr).
                    rewrite (grade_project_of_grade_neq _ _ _ A_grade neq).
                    rewrite ext_to_geo_zero.
                    apply plus_lid.
            }
            rewrite exterior_grade_add.
            rewrite geo_to_ext_project.
            specialize (H' n).
            prove_parts H'.
            {
                classic_case (nat_suc n = c + 1) as [n_eq|n_neq].
                {
                    left.
                    rewrite plus_comm in n_eq.
                    inversion n_eq.
                    apply nat_lt_suc.
                }
                destruct n_lt as [lt|[lt|lt]]; [>left|right; left|right; right].
                -   apply (trans2 (nat_lt_suc c)).
                    apply (trans2 lt).
                    apply nat_lt_suc.
                -   rewrite nat_plus_lsuc in lt.
                    rewrite nat_sucs_lt in lt.
                    rewrite nat_plus_lsuc in lt.
                    exact lt.
                -   destruct lt as [z eq].
                    clear - z eq n_neq.
                    nat_destruct z.
                    +   rewrite mult_ranni, plus_rid in eq.
                        contradiction.
                    +   exists z.
                        rewrite plus_comm in eq.
                        inversion eq.
                        rewrite nat_mult_rsuc.
                        rewrite (plus_comm 2).
                        do 2 rewrite plus_assoc.
                        apply rplus.
                        rewrite plus_comm.
                        rewrite nat_plus_lsuc.
                        reflexivity.
            }
            specialize (H' _ l_grade).
            rewrite H'.
            rewrite geo_to_ext_zero.
            rewrite mult_ranni.
            apply ext_to_geo_zero.
Qed.

Lemma geo_grade_decompose2 : ∀ (a b : geo B) (r s n : nat),
    of_grade r a → of_grade s b →
    (n < r ⊖ s ∨ r + s < n ∨ (∃ z, n = r ⊖ s + 2 * z + 1)) →
    grade_project (a * b) n = 0.
Proof.
    intros a b r s n ar bs n_eq.
    destruct (connex r s) as [leq|leq].
    -   apply (geo_grade_decompose1 a b r s n ar bs leq n_eq).
    -   rewrite nat_abs_minus_comm in n_eq.
        rewrite (plus_comm r s) in n_eq.
        rewrite <- (geo_reverse_reverse B (grade_project (VG := GG) (a * b) n)).
        rewrite geo_reverse_project.
        rewrite geo_reverse_mult.
        apply of_grade_reverse in ar.
        apply of_grade_reverse in bs.
        rewrite (geo_grade_decompose1 _ _ s r n bs ar leq n_eq).
        apply geo_reverse_zero.
Qed.

Theorem geo_grade_decompose : ∀ (a b : geo B) (r s : nat),
    of_grade r a → of_grade s b →
    a * b = sum (U := geo B)
        (λ n, grade_project (a * b) (r ⊖ s + 2*n)) 0 (nat_suc (min r s)).
Proof.
    intros a b r s ar bs.
    apply all_grade_project_eq.
    intros n.
    rewrite grade_project_sum.
    classic_case (n < r ⊖ s ∨ r + s < n ∨ (∃ z, n = r ⊖ s + 2 * z + 1))
            as [n_eq|n_neq].
    -   rewrite (geo_grade_decompose2 a b r s n ar bs n_eq).
        symmetry; apply sum_zero_zero.
        intros m m_lt.
        assert (r ⊖ s + 2 * m ≠ n) as n_neq.
        {
            cbn in n.
            (*clear - n_eq m_lt.*)
            intros contr; subst n.
            destruct n_eq as [n_lt|[n_lt|[z eq]]].
            -   pose proof (nat_le_self_rplus (r ⊖ s) (2 * m)) as leq.
                destruct (le_lt_trans leq n_lt); contradiction.
            -   rewrite nat_lt_suc_le in m_lt.
                apply nat_le_lmult with 2 in m_lt.
                apply le_lplus with (r ⊖ s) in m_lt.
                pose proof (lt_le_trans n_lt m_lt) as ltq.
                (*clear - ltq.*)
                rewrite rdist in ltq.
                rewrite mult_lid in ltq.
                rewrite plus_assoc in ltq.
                rewrite nat_abs_minus_min in ltq.
                rewrite (plus_comm (max r s)) in ltq.
                rewrite min_max_plus in ltq.
                destruct ltq; contradiction.
            -   rewrite <- plus_assoc in eq.
                apply plus_lcancel in eq.
                do 2 rewrite (mult_comm 2) in eq.
                apply nat_even_neq_odd in eq.
                exact eq.
        }
        pose proof (grade_project_grade (a * b) (r ⊖ s + 2 * m)) as ab_grade.
        apply (grade_project_of_grade_neq _ _ _ ab_grade n_neq).
    -   do 2 rewrite not_or in n_neq.
        do 2 rewrite nlt_le in n_neq.
        destruct n_neq as [n_geq [n_leq z_ex]].
        apply nat_le_ex in n_geq as [c c_eq].
        assert (even c) as [m m_eq].
        {
            classic_contradiction contr.
            apply nat_odd_plus_one in contr as [m m_eq].
            subst c.
            rewrite not_ex in z_ex.
            specialize (z_ex m).
            rewrite plus_assoc in c_eq.
            symmetry in c_eq; contradiction.
        }
        rewrite mult_comm in m_eq.
        subst c.
        assert (Injective (λ m, r ⊖ s + 2 * m)) as f_inj.
        {
            split.
            intros i j eq.
            apply plus_lcancel in eq.
            apply mult_lcancel in eq.
            -   exact eq.
            -   intros contr; inversion contr.
        }
        symmetry; apply (sum_grade_project_single (VG := GG) _ _ _ _ _ f_inj m).
        +   exact c_eq.
        +   apply nat_pos.
        +   rewrite plus_lid.
            rewrite nat_lt_suc_le.
            subst n.
            apply nat_le_mult_lcancel with 2; [>intros contr; inversion contr|].
            rewrite (rdist _ _ (min r s)).
            rewrite mult_lid.
            apply le_plus_rcancel with (r ⊖ s).
            rewrite <- plus_assoc.
            do 2 rewrite (plus_comm _ (r ⊖ s)).
            rewrite nat_abs_minus_min.
            rewrite min_max_plus.
            exact n_leq.
Qed.

Theorem geo_mult_project_bigger : ∀ (a b : geo B) (r s : nat),
    of_grade r a → of_grade s b →
    ∀ n, r + s < n → grade_project (a * b) n = 0.
Proof.
    intros a b r s ar bs n n_gt.
    apply (geo_grade_decompose2 _ _ _ _ _ ar bs).
    right; left.
    exact n_gt.
Qed.

Theorem geo_mult_project_smaller : ∀ (a b : geo B) (r s : nat),
    of_grade r a → of_grade s b →
    ∀ n, n < r ⊖ s → grade_project (a * b) n = 0.
Proof.
    intros a b r s ar bs n n_lt.
    apply (geo_grade_decompose2 _ _ _ _ _ ar bs).
    left.
    exact n_lt.
Qed.
(* begin hide *)

End GeometricDecompose.
(* end hide *)
