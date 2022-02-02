Require Import init.

Require Export linear_base.
Require Import linear_basis.
Require Import linear_span.
Require Import set.
Require Import card.
Require Import unordered_list.
Require Import plus_sum.

Require Import module_category.
Require Import category_initterm.

Open Scope card_scope.

#[universes(template)]
Record free_linear U V `{Zero U} := make_free {
    free_f : V → U;
    free_fin : finite (|set_type (λ x, free_f x ≠ 0)|);
}.
Arguments make_free {U V H}.
Arguments free_f {U V H}.
Arguments free_fin {U V H}.

(* begin hide *)
Section LinearFree.

Context (F : CRing) (V : Type).
Let U := cring_U F.
Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD.

(* end hide *)
Theorem free_eq :
        ∀ (A B : free_linear U V), (∀ x, free_f A x = free_f B x) → A = B.
    intros [Af A_fin] [Bf B_fin] eq.
    apply functional_ext in eq.
    cbn in eq.
    subst.
    rewrite (proof_irrelevance A_fin B_fin).
    reflexivity.
Qed.

Let to_free_base (v : V) : (V → U) := λ x, If x = v then 1 else 0.
Lemma to_free_fin : ∀ v, finite (|set_type (λ x, to_free_base v x ≠ 0)|).
    intros v.
    classic_case (0 = 1) as [eq|not_trivial].
    {
        replace (λ x, to_free_base v x ≠ 0) with (λ x : V, 0 ≠ 0).
        2: {
            apply functional_ext; intros x.
            unfold to_free_base.
            unfold U in *.
            rewrite <- eq.
            case_if; reflexivity.
        }
        assert ((λ _ : V, 0 ≠ 0) = ∅) as empty_eq.
        {
            apply not_ex_empty.
            intros x.
            rewrite not_not.
            reflexivity.
        }
        rewrite empty_eq.
        apply empty_finite.
    }
    replace (λ x, to_free_base v x ≠ 0) with (singleton v).
    1: apply singleton_finite.
    unfold to_free_base.
    apply antisym.
    -   intros x vx.
        case_if.
        +   rewrite neq_sym.
            exact not_trivial.
        +   unfold singleton in vx.
            symmetry in vx.
            contradiction.
    -   intros x; cbn.
        case_if.
        +   intro neq.
            rewrite e.
            reflexivity.
        +   intros contr.
            contradiction.
Qed.
Definition to_free v := make_free (to_free_base v) (to_free_fin v).

Theorem to_free_eq : 0 ≠ 1 → ∀ u v, to_free u = to_free v → u = v.
    intros not_trivial u v eq.
    unfold to_free in eq.
    inversion eq as [eq2].
    unfold to_free_base in eq2.
    pose proof (func_eq _ _ eq2) as eq3.
    specialize (eq3 u).
    cbn in eq3.
    clear - not_trivial eq3.
    case_if.
    1: case_if.
    -   exact e0.
    -   symmetry in eq3.
        contradiction.
    -   contradiction.
Qed.

Let free_plus (A B : free_linear U V) := λ x, free_f A x + free_f B x.

Lemma free_plus_fin : ∀ A B, finite (|set_type (λ x, free_plus A B x ≠ 0)|).
    intros [f f_fin] [g g_fin].
    unfold free_plus; cbn.
    apply fin_nat_ex in f_fin as [m f_fin].
    apply fin_nat_ex in g_fin as [n g_fin].
    pose proof (nat_is_finite (m + n)) as mn_fin.
    apply (le_lt_trans2 mn_fin).
    rewrite <- nat_to_card_plus.
    rewrite f_fin, g_fin.
    clear m f_fin n g_fin mn_fin.
    unfold plus at 2, le; equiv_simpl.
    assert (∀ x, f x + g x ≠ 0 → f x ≠ 0 ∨ g x ≠ 0) as fg_neq.
    {
        intros x eq.
        classic_case (f x = 0) as [f_eq|neq]; try (left; exact neq).
        right.
        intro g_eq.
        rewrite f_eq, g_eq in eq.
        rewrite plus_lid in eq.
        contradiction.
    }
    exists (λ x, match (or_to_strong _ _ (fg_neq [x|] [|x])) with
        | strong_or_left  H => inl [[x|]|H]
        | strong_or_right H => inr [[x|]|H]
        end).
    intros a b eq.
    destruct (or_to_strong _) as [a_neq|a_neq];
    destruct (or_to_strong _) as [b_neq|b_neq].
    -   inversion eq as [eq2].
        apply set_type_eq.
        exact eq2.
    -   inversion eq.
    -   inversion eq.
    -   inversion eq as [eq2].
        apply set_type_eq.
        exact eq2.
Qed.

Instance free_plus_class : Plus (free_linear U V) := {
    plus A B := make_free (free_plus A B) (free_plus_fin A B)
}.

Lemma free_plus_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
    intros [af a_fin] [bf b_fin] [cf c_fin].
    unfold plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply plus_assoc.
Qed.
Instance free_plus_assoc_class : PlusAssoc _ := {
    plus_assoc := free_plus_assoc
}.

Lemma free_plus_comm : ∀ a b, a + b = b + a.
    intros [af a_fin] [bf b_fin].
    unfold plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply plus_comm.
Qed.
Instance free_plus_comm_class : PlusComm _ := {
    plus_comm := free_plus_comm
}.

Lemma free_zero_fin : finite (|set_type (λ x : V, (zero (U := U)) ≠ 0)|).
    replace (λ x, (zero (U := U)) ≠ 0) with (empty (U := V)).
    {
        rewrite <- empty_set_size.
        apply nat_is_finite.
    }
    symmetry; apply not_ex_empty.
    intros x.
    rewrite not_not.
    reflexivity.
Qed.
Instance free_zero : Zero (free_linear U V) := {
    zero := make_free (λ x, 0) free_zero_fin
}.

Lemma free_plus_lid : ∀ a, 0 + a = a.
    intros [af a_fin].
    unfold zero, plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply plus_lid.
Qed.
Instance free_plus_lid_class : PlusLid _ := {
    plus_lid := free_plus_lid
}.

Lemma free_neg_fin :
        ∀ A : free_linear U V, finite (|set_type (λ x, -(free_f A x) ≠ 0)|).
    intros [f f_fin]; cbn.
    apply (le_lt_trans2 f_fin).
    unfold le; equiv_simpl.
    assert (∀ x, -f x ≠ 0 → f x ≠ 0) as x_in.
    {
        intros x neq eq.
        rewrite eq in neq.
        rewrite neg_zero in neq.
        contradiction.
    }
    exists (λ x, [[x|] | x_in [x|] [|x]]).
    intros a b eq.
    inversion eq as [eq2].
    apply set_type_eq.
    exact eq2.
Qed.
Instance free_neg : Neg (free_linear U V) := {
    neg A := make_free (λ x, -free_f A x) (free_neg_fin A)
}.

Lemma free_plus_linv : ∀ a, -a + a = 0.
    intros [af a_fin].
    unfold neg, plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply plus_linv.
Qed.
Instance free_plus_linv_class : PlusLinv _ := {
    plus_linv := free_plus_linv
}.

Lemma free_scalar_fin : ∀ (a : U) (A : free_linear U V),
        finite (|set_type (λ x, a * free_f A x ≠ 0)|).
    intros a [f f_fin]; cbn.
    apply (le_lt_trans2 f_fin).
    unfold le; equiv_simpl.
    assert (∀ x, a * f x ≠ 0 → f x ≠ 0) as x_ex.
    {
        intros x neq eq.
        rewrite eq in neq.
        rewrite mult_ranni in neq.
        contradiction.
    }
    exists (λ x, [[x|] | x_ex [x|] [|x]]).
    intros x y eq.
    inversion eq as [eq2].
    apply set_type_eq.
    exact eq2.
Qed.
Instance free_scalar : ScalarMult U (free_linear U V) := {
    scalar_mult a B := make_free (λ x, a * free_f B x) (free_scalar_fin a B)
}.

Lemma free_scalar_comp : ∀ a b v, a · (b · v) = (a * b) · v.
    intros a b [f f_fin].
    unfold scalar_mult; cbn.
    apply free_eq; cbn.
    intros x.
    apply mult_assoc.
Qed.
Instance free_scalar_comp_class : ScalarComp _ _ := {
    scalar_comp := free_scalar_comp
}.

Lemma free_scalar_id : ∀ v, 1 · v = v.
    intros [f f_fin].
    unfold scalar_mult; cbn.
    apply free_eq; cbn.
    intros x.
    apply mult_lid.
Qed.
Instance free_scalar_id_class : ScalarId _ _ := {
    scalar_id := free_scalar_id
}.

Lemma free_scalar_ldist : ∀ a u v, a · (u + v) = a · u + a · v.
    intros a [uf uf_fin] [vf vf_fin].
    unfold scalar_mult, plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply ldist.
Qed.
Instance free_scalar_ldist_class : ScalarLdist _ _ := {
    scalar_ldist := free_scalar_ldist
}.

Lemma free_scalar_rdist : ∀ a b v, (a + b) · v = a · v + b · v.
    intros a b [f f_fin].
    unfold scalar_mult, plus at 2; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply rdist.
Qed.
Instance free_scalar_rdist_class : ScalarRdist _ _ := {
    scalar_rdist := free_scalar_rdist
}.

Definition free_basis v := ∃ b, v = to_free b.

Theorem free_basis_basis : basis free_basis.
    split.
    -   intros [l l_uni] l_in l_zero; cbn.
        apply ulist_prop_split.
        intros [α v] l' l_eq.
        subst l.
        rename l' into l.
        cbn.
        classic_contradiction α_nz.
        unfold linear_combination_set in l_uni.
        unfold linear_combination in l_zero; cbn in l_zero.
        unfold linear_list_in in l_in; cbn in l_in.
        rewrite ulist_image_add, ulist_unique_add in l_uni.
        rewrite ulist_image_add, ulist_sum_add in l_zero.
        rewrite ulist_prop_add in l_in.
        cbn in *.
        destruct l_in as [v_basis l_in].
        destruct v_basis as [v' v_eq].
        subst v.
        rename v' into v.
        destruct l_uni as [v_nin l_uni].
        clear l_uni.
        unfold zero, plus in l_zero; equiv_simpl in l_zero.
        inversion l_zero as [eq]; clear l_zero.
        pose proof (func_eq _ _ eq) as eq2; clear eq.
        cbn in eq2.
        specialize (eq2 v).
        unfold free_plus in eq2.
        unfold scalar_mult in eq2 at 1; cbn in eq2.
        unfold to_free_base in eq2.
        case_if; [>|contradiction].
        clear e.
        rewrite mult_rid in eq2.
        induction l using ulist_induction.
        +   rewrite ulist_image_end, ulist_sum_end in eq2.
            unfold zero at 2 in eq2; cbn in eq2.
            rewrite plus_rid in eq2.
            contradiction.
        +   destruct a as [β u].
            rewrite ulist_image_add, in_ulist_add in v_nin.
            rewrite not_or in v_nin.
            apply IHl; clear IHl.
            *   apply v_nin.
            *   rewrite ulist_prop_add in l_in.
                apply l_in.
            *   rewrite ulist_image_add, ulist_sum_add in eq2.
                unfold plus at 2 in eq2; cbn in eq2.
                unfold free_plus in eq2.
                unfold scalar_mult in eq2 at 1; cbn in eq2.
                rewrite plus_assoc in eq2.
                rewrite (plus_comm α) in eq2.
                rewrite <- plus_assoc in eq2.
                rewrite plus_0_ab_na_b in eq2.
                rewrite <- eq2; clear eq2.
                rewrite <- neg_zero.
                apply f_equal.
                assert (free_basis u) as u_basis.
                {
                    rewrite ulist_prop_add in l_in.
                    apply l_in.
                }
                destruct u_basis as [u' u_eq].
                subst u.
                rename u' into u.
                cbn.
                unfold to_free_base.
                case_if.
                --  destruct v_nin as [neq v_nin].
                    subst.
                    contradiction.
                --  rewrite mult_ranni.
                    reflexivity.
    -   apply all_is_all.
        intros f.
        classic_case (inhabited V) as [z|nV].
        2: {
            assert (0 = f) as f_z.
            {
                apply free_eq.
                intros v.
                exfalso; apply nV.
                split.
                exact v.
            }
            rewrite <- f_z.
            apply linear_span_zero.
        }
        destruct z as [z].
        rewrite (span_linear_combination U free_basis).
        unfold linear_combination_of; cbn.
        pose proof (fin_nat_ex _ (free_fin f)) as [n n_eq].
        unfold nat_to_card in n_eq; equiv_simpl in n_eq.
        destruct n_eq as [g [g_inj g_sur]].
        pose (g' m := match (strong_excluded_middle (m < n)) with
            | strong_or_left ltq => [g [m|ltq]|]
            | strong_or_right _ => z
            end).
        pose (l := func_to_ulist g' n).
        pose (l' := ulist_image l (λ v, (free_f f v, to_free v))).
        assert (linear_combination_set l') as l_comb.
        {
            unfold linear_combination_set.
            unfold l', l.
            rewrite ulist_image_comp.
            rewrite func_to_ulist_image.
            cbn.
            apply func_to_ulist_unique.
            intros m1 m2 m1_lt m2_lt eq.
            unfold g' in eq.
            destruct (strong_excluded_middle (m1 < n)) as [m1_lt'|m1_lt'].
            2: contradiction.
            destruct (strong_excluded_middle (m2 < n)) as [m2_lt'|m2_lt'].
            2: contradiction.
            inversion eq as [eq2].
            unfold to_free_base in eq2.
            pose proof (func_eq _ _ eq2) as eq3; cbn in eq3.
            clear eq eq2 m1_lt m2_lt.
            specialize (eq3 [g [m1 | m1_lt']|]).
            do 2 case_if; try contradiction.
            -   apply set_type_eq in e0.
                apply g_inj in e0.
                apply eq_set_type in e0; cbn in e0.
                exact e0.
            -   apply (rmult (free_f f [g [m1|m1_lt']|])) in eq3.
                rewrite mult_lid, mult_lanni in eq3.
                pose proof [|g [m1 | m1_lt']].
                contradiction.
        }
        exists [l'|l_comb].
        split.
        +   unfold linear_combination, l'; cbn.
            rewrite ulist_image_comp.
            cbn.
            apply free_eq.
            intros v.
            unfold l.
            rewrite func_to_ulist_image.
            assert (free_f (ulist_sum (func_to_ulist (λ m, free_f f (g' m) · to_free (g' m)) n)) v =
                ulist_sum (func_to_ulist (λ m, free_f f (g' m) * to_free_base (g' m) v) n)) as eq.
            {
                do 2 rewrite ulist_sum_sum_eq.
                remember n as n'.
                rewrite Heqn'.
                assert (n <= n') as n_leq by (rewrite Heqn'; apply refl).
                clear Heqn'.
                nat_induction n.
                -   unfold zero; cbn.
                    reflexivity.
                -   cbn.
                    unfold plus at 1; cbn.
                    unfold free_plus.
                    rewrite IHn by exact (trans (nat_le_suc n) n_leq).
                    apply lplus.
                    rewrite plus_lid.
                    unfold scalar_mult; cbn.
                    reflexivity.
            }
            rewrite eq; clear eq l l' l_comb.
            pose (h m := free_f f (g' m) * to_free_base (g' m) v).
            fold h.
            classic_case (free_f f v = 0) as [fv_z|fv_nz].
            *   rewrite fv_z.
                assert (h = (λ _, 0)) as h_eq.
                {
                    apply functional_ext.
                    intros m.
                    unfold h.
                    unfold to_free_base.
                    case_if.
                    -   rewrite mult_rid.
                        rewrite <- e.
                        exact fv_z.
                    -   apply mult_ranni.
                }
                rewrite h_eq.
                clear f z g g_inj g_sur g' v h fv_z h_eq.
                nat_induction n.
                --  rewrite func_to_ulist_zero.
                    rewrite ulist_sum_end.
                    reflexivity.
                --  cbn.
                    rewrite func_to_ulist_suc.
                    rewrite ulist_sum_add.
                    rewrite <- IHn.
                    rewrite plus_rid.
                    reflexivity.
            *   pose proof (g_sur [v|fv_nz]) as [vn vn_eq].
                pose (h' m := If m < n then h m else 0).
                assert (∀ m, m < n → h m = h' m) as h'_eq.
                {
                    intros m ltq.
                    unfold h', h.
                    case_if.
                    -   reflexivity.
                    -   contradiction.
                }
                rewrite (func_to_ulist_eq _ _ _ h'_eq); clear h'_eq.
                assert (h' = (λ m, If m = [vn|] then free_f f v else 0)) as h_eq.
                {
                    apply functional_ext.
                    intros m.
                    unfold h'; clear h'.
                    unfold h; clear h.
                    unfold to_free_base.
                    unfold g'.
                    do 2 case_if; subst.
                    1, 2: case_if; subst.
                    -   apply mult_rid.
                    -   apply eq_set_type in vn_eq; cbn in vn_eq.
                        apply set_type_eq in vn_eq.
                        apply g_inj in vn_eq.
                        apply eq_set_type in vn_eq.
                        symmetry in vn_eq; contradiction.
                    -   exfalso; apply n0.
                        apply eq_set_type in vn_eq; cbn in vn_eq.
                        rewrite <- vn_eq.
                        apply eq_set_type.
                        apply f_equal.
                        apply set_type_eq; reflexivity.
                    -   apply mult_ranni.
                    -   destruct vn; contradiction.
                    -   reflexivity.
                }
                rewrite h_eq.
                rewrite (ulist_sum_func_single (free_f f v) _ _ [|vn]).
                reflexivity.
        +   unfold linear_list_in; cbn.
            apply ulist_prop_split.
            intros [α v] l'' l'_eq.
            assert (in_ulist l' (α, v)) as v_in.
            {
                rewrite l'_eq.
                rewrite in_ulist_add.
                left; reflexivity.
            }
            apply image_in_ulist in v_in as [u [u_eq u_in]].
            exists u.
            inversion u_eq.
            reflexivity.
Qed.

Definition free_module := make_module
    F
    (free_linear U V)
    free_plus_class
    free_zero
    free_neg
    free_plus_assoc_class
    free_plus_comm_class
    free_plus_lid_class
    free_plus_linv_class
    free_scalar
    free_scalar_id_class
    free_scalar_ldist_class
    free_scalar_rdist_class
    free_scalar_comp_class
.

Record free_from := make_free_from {
    free_from_module : Module F;
    free_from_f : V → module_V free_from_module;
}.

Definition free_from_set (f g : free_from)
    (h : cat_morphism (MODULE F)
                      (free_from_module f)
                      (free_from_module g))
    := ∀ x, module_homo_f h (free_from_f f x) = free_from_f g x.

Definition free_from_compose {F G H : free_from}
    (f : set_type (free_from_set G H)) (g : set_type (free_from_set F G))
    := [f|] ∘ [g|].

Lemma free_from_set_compose_in
        {F' G H : free_from} : ∀ (f : set_type (free_from_set G H)) g,
        free_from_set F' H (free_from_compose f g).
    intros [f f_eq] [g g_eq].
    unfold free_from_set in *.
    unfold free_from_compose; cbn.
    intros x.
    rewrite g_eq.
    apply f_eq.
Qed.

Lemma free_from_set_id_in : ∀ f : free_from, free_from_set f f 𝟙.
    intros f.
    unfold free_from_set.
    intros x.
    cbn.
    reflexivity.
Qed.

Program Instance FREE_FROM : Category := {
    cat_U := free_from;
    cat_morphism f g := set_type (free_from_set f g);
    cat_compose {F G H} f g := [_|free_from_set_compose_in f g];
    cat_id f := [_|free_from_set_id_in f];
}.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_assoc (MODULE F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_lid (MODULE F)).
Qed.
Next Obligation.
    apply set_type_eq; cbn.
    apply (@cat_rid (MODULE F)).
Qed.

Definition to_free_from := make_free_from free_module to_free.

Theorem free_module_universal : initial to_free_from.
    intros [gM g].
    pose (gP := module_plus gM).
    pose (gZ := module_zero gM).
    pose (gN := module_neg gM).
    pose (gPC := module_plus_comm gM).
    pose (gPA := module_plus_assoc gM).
    pose (gPZ := module_plus_lid gM).
    pose (gPN := module_plus_linv gM).
    pose (gSM := module_scalar gM).
    pose (gSMO := module_scalar_id gM).
    pose (gSML := module_scalar_ldist gM).
    pose (gSMR := module_scalar_rdist gM).
    pose (gSMC := module_scalar_comp gM).
    cbn.
    apply card_unique_one.
    -   apply ex_set_type.
        pose (f1 v := ex_val (basis_coefficients_S_ex _ free_basis_basis v)).
        pose (f v := ulist_sum (ulist_image (f1 v) (λ x, fst x · g (ex_val [|snd x])))).
        assert (∀ l1 l2 : ulist (U * set_type free_basis),
            ulist_sum (ulist_image l1 (λ x, fst x · [snd x|])) =
            ulist_sum (ulist_image l2 (λ x, fst x · [snd x|])) →
            linear_combination_set (ulist_image l1 (λ x, (fst x, [snd x|]))) →
            ulist_sum (ulist_image l1 (λ x, fst x · g (ex_val [|snd x]))) =
            ulist_sum (ulist_image l2 (λ x, fst x · g (ex_val [|snd x]))))
            as wlog.
        {
            intros l1 l2 l_eq l1_uni.
            revert l1 l_eq l1_uni.
            induction l2 using ulist_induction; intros.
            -   rewrite ulist_image_end, ulist_sum_end in l_eq.
                assert (linear_list_in free_basis [_|l1_uni]) as l1_in.
                {
                    unfold linear_list_in; cbn.
                    apply ulist_prop_split.
                    intros [α u] l' l'_eq.
                    assert (in_ulist (ulist_image l1 (λ x, (fst x, [snd x|])))
                        (α, u)) as u_in.
                    {
                        rewrite l'_eq.
                        rewrite in_ulist_add.
                        left; reflexivity.
                    }
                    apply image_in_ulist in u_in as [[β v] [v_eq v_in]].
                    inversion v_eq.
                    exact [|v].
                }
                assert (0 = linear_combination [_|l1_uni]) as l1_zero.
                {
                    unfold linear_combination; cbn.
                    rewrite ulist_image_comp.
                    symmetry; exact l_eq.
                }
                pose proof (land free_basis_basis [_|l1_uni] l1_in l1_zero)
                    as all_zero.
                cbn in all_zero.
                clear l1_uni l_eq l1_in l1_zero.
                induction l1 using ulist_induction.
                +   reflexivity.
                +   change (cring_U F) with U in all_zero.
                    rewrite ulist_image_add, ulist_prop_add in all_zero.
                    specialize (IHl1 (rand all_zero)).
                    rewrite ulist_image_add, ulist_sum_add.
                    rewrite IHl1; clear IHl1.
                    rewrite ulist_image_end, ulist_sum_end.
                    rewrite plus_rid.
                    cbn in all_zero.
                    rewrite <- (land all_zero).
                    apply scalar_lanni.
            -   rewrite ulist_image_add, ulist_sum_add in l_eq.
                apply plus_rlmove in l_eq.
                rewrite <- scalar_lneg in l_eq.
                classic_case (∃ α, in_ulist l1 (α, snd a)) as [a_in|a_nin].
                +   destruct a_in as [α a_in].
                    apply in_ulist_split in a_in as [l1' l1_eq].
                    subst l1.
                    rewrite ulist_image_add, ulist_sum_add in l_eq; cbn in l_eq.
                    rewrite (plus_assoc _ (α · _)) in l_eq.
                    rewrite (plus_comm _ (α · _)) in l_eq.
                    rewrite <- scalar_rdist in l_eq.
                    rewrite <- ulist_sum_add in l_eq.
                    pose proof (ulist_image_add (α - fst a, snd a) l1'
                        (λ x, fst x · [snd x|])) as eq.
                    cbn in eq.
                    rewrite <- eq in l_eq; clear eq.
                    assert (linear_combination_set (ulist_image
                        ((α - fst a, snd a) ::: l1')
                        (λ x, (fst x, [snd x|])))) as l1_uni'.
                    {
                        unfold linear_combination_set in *.
                        rewrite ulist_image_comp in *.
                        rewrite ulist_image_add, ulist_unique_add in l1_uni.
                        cbn in l1_uni.
                        rewrite ulist_image_add, ulist_unique_add; cbn.
                        apply l1_uni.
                    }
                    specialize (IHl2 _ l_eq l1_uni').
                    clear l_eq l1_uni l1_uni'.
                    do 2 rewrite ulist_image_add, ulist_sum_add; cbn.
                    rewrite <- IHl2.
                    rewrite ulist_image_add, ulist_sum_add; cbn.
                    rewrite plus_assoc.
                    apply rplus.
                    rewrite scalar_rdist.
                    rewrite scalar_lneg.
                    rewrite plus_comm.
                    rewrite plus_rlinv.
                    reflexivity.
                +   pose (l1' := (-fst a, snd a) ::: l1).
                    assert (-fst a · [snd a|] +
                        ulist_sum (ulist_image l1 (λ x, fst x · [snd x|]))
                        = ulist_sum (ulist_image l1' (λ x, fst x · [snd x|])))
                        as eq.
                    {
                        unfold l1'.
                        rewrite ulist_image_add, ulist_sum_add; cbn.
                        reflexivity.
                    }
                    rewrite eq in l_eq; clear eq.
                    assert (linear_combination_set (ulist_image
                        ((-fst a, snd a) ::: l1)
                        (λ x, (fst x, [snd x|])))) as l1_uni'.
                    {
                        unfold linear_combination_set.
                        rewrite ulist_image_comp.
                        rewrite ulist_image_add, ulist_unique_add; cbn.
                        split.
                        -   intros contr.
                            apply a_nin.
                            apply image_in_ulist in contr as [a' [eq a_in]].
                            exists (fst a').
                            apply set_type_eq in eq.
                            rewrite <- eq.
                            destruct a' as [α a']; cbn in *.
                            exact a_in.
                        -   unfold linear_combination_set in l1_uni.
                            rewrite ulist_image_comp in l1_uni.
                            exact l1_uni.
                    }
                    specialize (IHl2 _ l_eq l1_uni').
                    unfold l1' in IHl2.
                    clear l_eq l1_uni l1_uni' l1'.
                    rewrite ulist_image_add, ulist_sum_add; cbn.
                    rewrite <- IHl2.
                    rewrite ulist_image_add, ulist_sum_add; cbn.
                    rewrite scalar_lneg.
                    rewrite plus_lrinv.
                    reflexivity.
        }
        assert (∀ u v, f (u + v) = f u + f v) as f_plus.
        {
            intros u v.
            unfold f, f1.
            rewrite_ex_val luv luv_eq.
            rewrite_ex_val lu lu_eq.
            rewrite_ex_val lv lv_eq.
            pose proof (basis_coefficients_combination _ free_basis_basis (u + v)) as uv_eq.
            pose proof (basis_coefficients_combination _ free_basis_basis u) as u_eq.
            pose proof (basis_coefficients_combination _ free_basis_basis v) as v_eq.
            pose proof [|basis_coefficients _ free_basis_basis (u + v)] as luv_uni.
            rewrite luv_eq in luv_uni.
            apply (f_equal (λ l, ulist_image l (λ x, fst x · snd x))) in luv_eq.
            apply (f_equal ulist_sum) in luv_eq.
            apply (f_equal (λ l, ulist_image l (λ x, fst x · snd x))) in lu_eq.
            apply (f_equal ulist_sum) in lu_eq.
            apply (f_equal (λ l, ulist_image l (λ x, fst x · snd x))) in lv_eq.
            apply (f_equal ulist_sum) in lv_eq.
            unfold linear_combination in *.
            rewrite <- uv_eq in luv_eq; clear uv_eq.
            rewrite <- u_eq in lu_eq; clear u_eq.
            rewrite <- v_eq in lv_eq; clear v_eq.
            rewrite ulist_image_comp in luv_eq, lu_eq, lv_eq.
            cbn in *.
            subst u v.
            rewrite <- ulist_sum_plus.
            rewrite <- ulist_image_conc.
            rewrite <- ulist_sum_plus in luv_eq.
            rewrite <- ulist_image_conc in luv_eq.
            remember (lu +++ lv) as luv'.
            clear Heqluv' lu lv.
            symmetry in luv_eq.
            apply (wlog _ _ luv_eq luv_uni).
        }
        assert (∀ a v, f (a · v) = a · f v) as f_scalar.
        {
            intros a v.
            unfold f, f1.
            rewrite_ex_val lav lav_eq.
            rewrite_ex_val lv lv_eq.
            pose proof (basis_coefficients_combination _ free_basis_basis (a · v)) as av_eq.
            pose proof (basis_coefficients_combination _ free_basis_basis v) as v_eq.
            pose proof [|basis_coefficients _ free_basis_basis (a · v)] as av_uni.
            rewrite lav_eq in av_uni.
            apply (f_equal (λ l, ulist_image l (λ x, fst x · snd x))) in lav_eq.
            apply (f_equal ulist_sum) in lav_eq.
            apply (f_equal (λ l, ulist_image l (λ x, fst x · snd x))) in lv_eq.
            apply (f_equal ulist_sum) in lv_eq.
            unfold linear_combination in *.
            rewrite <- av_eq in lav_eq; clear av_eq.
            rewrite <- v_eq in lv_eq; clear v_eq.
            rewrite ulist_image_comp in lav_eq, lv_eq.
            cbn in *.
            subst v.
            remember (ulist_image lv (λ x, (a * fst x, snd x))) as lav'.
            assert (a · ulist_sum (ulist_image lv (λ x, fst x · [snd x|])) =
                    ulist_sum (ulist_image lav' (λ x, fst x · [snd x|]))) as eq.
            {
                rewrite Heqlav'.
                clear lav_eq av_uni lav' Heqlav'.
                rewrite ulist_image_comp; cbn.
                induction lv using ulist_induction.
                -   do 2 rewrite ulist_image_end, ulist_sum_end.
                    apply scalar_ranni.
                -   do 2 rewrite ulist_image_add, ulist_sum_add.
                    rewrite <- IHlv; clear IHlv.
                    rewrite scalar_ldist.
                    rewrite scalar_comp.
                    reflexivity.
            }
            rewrite eq in lav_eq; clear eq.
            assert (a · ulist_sum (ulist_image lv (λ x, fst x · g (ex_val [|snd x]))) =
                    ulist_sum (ulist_image lav' (λ x, fst x · g (ex_val [|snd x])))) as eq.
            {
                rewrite Heqlav'.
                clear lav_eq av_uni lav' Heqlav'.
                rewrite ulist_image_comp; cbn.
                induction lv using ulist_induction.
                -   do 2 rewrite ulist_image_end, ulist_sum_end.
                    apply scalar_ranni.
                -   do 2 rewrite ulist_image_add, ulist_sum_add.
                    rewrite <- IHlv; clear IHlv.
                    rewrite scalar_ldist.
                    rewrite scalar_comp.
                    reflexivity.
            }
            rewrite eq; clear eq.
            symmetry in lav_eq.
            apply (wlog _ _ lav_eq av_uni).
        }
        pose (fH := make_module_homomorphism F free_module gM f f_plus f_scalar).
        exists fH.
        unfold free_from_set; cbn.
        intros v.
        clear fH.
        unfold f, f1.
        rewrite_ex_val l l_eq.
        clear f f1 f_plus f_scalar.
        classic_case (0 = 1) as [triv|not_triv].
        +   rewrite <- scalar_id.
            rewrite <- (scalar_id (ulist_sum _)).
            rewrite <- triv.
            do 2 rewrite scalar_lanni.
            reflexivity.
        +   assert (free_basis (to_free v)) as v_basis by (exists v; reflexivity).
            rewrite (basis_single not_triv _ _ _ v_basis) in l_eq.
            assert (l = (1, [_|v_basis]) ::: ulist_end) as l_eq2.
            {
                destruct l using ulist_destruct.
                1: {
                    rewrite ulist_image_end in l_eq.
                    apply ulist_end_neq in l_eq.
                    contradiction l_eq.
                }
                destruct l using ulist_destruct.
                2: {
                    apply not_not_impl2 in l_eq.
                    exfalso; apply l_eq.
                    apply ulist_size_neq.
                    do 2 rewrite ulist_image_add.
                    do 3 rewrite ulist_size_add.
                    rewrite ulist_size_end.
                    intros contr.
                    inversion contr.
                }
                rewrite ulist_image_add in l_eq.
                rewrite ulist_image_end in l_eq.
                apply ulist_single_eq in l_eq.
                inversion l_eq as [[eq1 eq2]].
                apply f_equal2; [>|reflexivity].
                destruct a as [a u]; cbn in *.
                subst a.
                apply f_equal.
                apply set_type_eq; cbn.
                symmetry; exact eq2.
            }
            rewrite l_eq2.
            rewrite ulist_image_add, ulist_sum_add; cbn.
            rewrite ulist_image_end, ulist_sum_end.
            rewrite scalar_id.
            rewrite plus_rid.
            rewrite_ex_val v' v'_eq.
            apply to_free_eq in v'_eq.
            2: exact not_triv.
            rewrite v'_eq.
            reflexivity.
    -   intros [f1 f1_in] [f2 f2_in].
        pose (f1_plus := @module_homo_plus _ _ _ f1).
        pose (f1_scalar := @module_homo_scalar _ _ _ f1).
        pose (f2_plus := @module_homo_plus _ _ _ f2).
        pose (f2_scalar := @module_homo_scalar _ _ _ f2).
        apply set_type_eq; cbn.
        apply module_homomorphism_eq.
        cbn.
        intros v.
        unfold free_from_set in f1_in; cbn in f1_in.
        unfold free_from_set in f2_in; cbn in f2_in.
        pose proof (basis_coefficients_combination _ free_basis_basis v) as v_eq.
        pose proof (basis_coefficients_in _ free_basis_basis v) as v_in.
        rewrite v_eq; clear v_eq.
        remember (basis_coefficients free_basis free_basis_basis v) as l.
        clear Heql.
        destruct l as [l l_comb].
        unfold linear_list_in in v_in.
        cbn in *.
        unfold linear_combination; cbn.
        clear l_comb.
        induction l using ulist_induction.
        +   rewrite ulist_image_end, ulist_sum_end.
            rewrite <- (scalar_lanni 0).
            rewrite f1_scalar.
            rewrite f2_scalar.
            do 2 rewrite scalar_lanni.
            reflexivity.
        +   prove_parts IHl.
            {
                clear v.
                apply ulist_prop_split.
                intros [α v] l' l_eq; cbn.
                subst l.
                rewrite ulist_swap in v_in.
                rewrite ulist_prop_add in v_in.
                apply v_in.
            }
            rewrite ulist_image_add, ulist_sum_add.
            rewrite f1_plus, f2_plus.
            rewrite IHl.
            apply rplus.
            rewrite f1_scalar, f2_scalar.
            assert (free_basis (snd a)) as [x x_eq].
            {
                rewrite ulist_prop_add in v_in.
                apply v_in.
            }
            rewrite x_eq.
            rewrite f1_in, f2_in.
            reflexivity.
Qed.
(* begin hide *)

End LinearFree.

Close Scope card_scope.
(* end hide *)
