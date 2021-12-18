Require Import init.

Require Export list_base.
Require Export list_prop.

Require Import relation.

Set Implicit Arguments.

Inductive list_permutation {U} : list U → list U → Prop :=
| list_perm_nil: list_permutation list_end list_end
| list_perm_skip x l l' : list_permutation l l' → list_permutation (x::l) (x::l')
| list_perm_swap x y l : list_permutation (y::x::l) (x::y::l)
| list_perm_trans l l' l'' :
    list_permutation l l' → list_permutation l' l'' → list_permutation l l''.

Theorem list_perm_refl {U} : ∀ l : list U, list_permutation l l.
    intros l.
    induction l.
    -   exact list_perm_nil.
    -   apply list_perm_skip.
        exact IHl.
Qed.

Theorem list_perm_sym {U} : ∀ al bl : list U,
        list_permutation al bl → list_permutation bl al.
    intros al bl perm.
    induction perm.
    -   exact list_perm_nil.
    -   apply list_perm_skip.
        exact IHperm.
    -   apply list_perm_swap.
    -   exact (list_perm_trans IHperm2 IHperm1).
Qed.

Theorem list_perm_trans2 {U} (l l' l'' : list U) :
        list_permutation l' l'' → list_permutation l l' →
        list_permutation l l''.
    intros eq1 eq2.
    apply (list_perm_trans eq2 eq1).
Qed.

Theorem list_perm_nil_eq {U} : ∀ l : list U,
        list_permutation list_end l → list_end = l.
    intros l l_end.
    remember (list_end) as m in l_end.
    induction l_end.
    -   reflexivity.
    -   inversion Heqm.
    -   inversion Heqm.
    -   apply IHl_end1 in Heqm.
        symmetry in Heqm.
        apply IHl_end2 in Heqm.
        exact Heqm.
Qed.

Theorem list_perm_lpart {U} : ∀ (al bl cl : list U),
        list_permutation al bl → list_permutation (al ++ cl) (bl ++ cl).
    intros al bl cl albl.
    induction albl.
    -   cbn.
        apply list_perm_refl.
    -   cbn.
        apply list_perm_skip.
        exact IHalbl.
    -   cbn.
        apply list_perm_swap.
    -   apply (list_perm_trans IHalbl1 IHalbl2).
Qed.

Theorem list_perm_add {U} : ∀ (l : list U) a,
        list_permutation (a :: l) (l ++ a :: list_end).
    intros l a.
    induction l.
    -   cbn.
        apply list_perm_refl.
    -   remember (a :: l) as l1.
        remember (l ++ a :: list_end) as l2.
        induction IHl.
        +   inversion Heql1.
        +   inversion Heql1.
            subst x l0.
            rewrite (list_add_conc a0 l) at 2.
            rewrite <- list_conc_assoc.
            rewrite <- Heql2.
            apply (list_perm_skip a0) in IHl.
            apply (list_perm_skip a) in IHl.
            apply (list_perm_trans IHl).
            apply list_perm_swap.
        +   inversion Heql1.
            subst y l.
            clear Heql1.
            rewrite (list_add_conc a0 _) at 2.
            rewrite <- list_conc_assoc.
            rewrite <- Heql2.
            cbn.
            pose (list_perm_swap a0 a (x :: l0)) as eq.
            apply (list_perm_trans eq).
            apply list_perm_skip.
            apply list_perm_swap.
        +   rewrite (list_add_conc a0 l) at 2.
            rewrite <- list_conc_assoc.
            rewrite <- Heql2.
            apply (list_perm_trans (list_perm_swap a0 a l)).
            apply list_perm_skip.
            rewrite <- Heql1.
            apply (list_perm_trans IHl1 IHl2).
Qed.

Theorem list_perm_conc {U} : ∀ al bl : list U,
        list_permutation (al ++ bl) (bl ++ al).
    intros al bl.
    induction al.
    -   cbn.
        rewrite list_conc_end.
        apply list_perm_refl.
    -   remember (al ++ bl) as l1.
        remember (bl ++ al) as l2.
        induction IHal.
        +   assert (al = list_end) as al_end.
            {
                destruct al; try reflexivity.
                inversion Heql1.
            }
            subst al.
            cbn in *.
            rewrite list_conc_end in Heql2.
            subst bl.
            cbn.
            apply list_perm_refl.
        +   clear IHIHal.
            destruct al.
            *   cbn in *.
                destruct bl.
                1: inversion Heql1.
                inversion Heql1 as [[eq Heql1']].
                subst u l.
                apply list_perm_add.
            *   remember (u :: al) as al'.
                pose proof (list_perm_add bl a) as eq.
                pose proof (list_perm_lpart al' eq) as eq2.
                rewrite <- list_conc_assoc in eq2.
                cbn in eq2.
                apply (list_perm_trans2 eq2).
                rewrite (list_add_conc a).
                rewrite (list_add_conc a (bl ++ al')).
                rewrite <- list_conc_assoc.
                rewrite <- Heql1, <- Heql2.
                cbn.
                do 2 apply list_perm_skip.
                exact IHal.
        +   pose proof (list_perm_add bl a) as eq.
            pose proof (list_perm_lpart al eq) as eq2.
            rewrite <- list_conc_assoc in eq2.
            cbn in eq2.
            apply (list_perm_trans2 eq2).
            cbn.
            rewrite <- Heql1, <- Heql2.
            apply list_perm_skip.
            apply list_perm_swap.
        +   pose proof (list_perm_add bl a) as eq.
            pose proof (list_perm_lpart al eq) as eq2.
            rewrite <- list_conc_assoc in eq2.
            cbn in eq2.
            apply (list_perm_trans2 eq2).
            cbn.
            rewrite <- Heql1, <- Heql2.
            apply list_perm_skip.
            apply (list_perm_trans IHal1 IHal2).
Qed.

Theorem list_perm_rpart {U} : ∀ (al bl cl : list U),
        list_permutation bl cl → list_permutation (al ++ bl) (al ++ cl).
    intros al bl cl blcl.
    apply (list_perm_trans (list_perm_conc al bl)).
    apply (list_perm_trans2 (list_perm_conc cl al)).
    apply list_perm_lpart.
    exact blcl.
Qed.

Theorem list_in_unique_perm {U} : ∀ al bl : list U,
        list_unique al → list_unique bl → (∀ x, in_list al x ↔ in_list bl x) →
        list_permutation al bl.
    intros al bl al_uni bl_uni l_in.
    revert bl bl_uni l_in.
    induction al; intros.
    -   destruct bl.
        1: exact list_perm_nil.
        specialize (l_in u) as [l_in1 l_in2].
        exfalso; apply l_in2.
        left; reflexivity.
    -   assert (in_list bl a) as bl_a.
        {
            apply l_in.
            left.
            reflexivity.
        }
        pose proof (in_list_split _ _ bl_a) as [bl1 [bl2 bl_eq]].
        pose (bl' := bl1 ++ bl2).
        assert (∀ x, in_list al x ↔ in_list bl' x) as l_in'.
        {
            intros x.
            unfold bl'.
            split.
            -   intros x_in.
                assert (in_list bl x) as bl_x.
                {
                    apply l_in.
                    right.
                    exact x_in.
                }
                rewrite bl_eq in bl_x.
                apply in_list_conc in bl_x as [bl_x|[bl_x|bl_x]].
                +   apply in_list_lconc.
                    exact bl_x.
                +   subst x.
                    destruct al_uni.
                    contradiction.
                +   apply in_list_rconc.
                    exact bl_x.
            -   intros x_in.
                assert (in_list bl x) as bl_x.
                {
                    rewrite bl_eq.
                    apply in_list_conc in x_in.
                    destruct x_in as [x_in|x_in].
                    -   apply in_list_lconc.
                        exact x_in.
                    -   apply in_list_rconc.
                        right.
                        exact x_in.
                }
                apply l_in in bl_x.
                destruct bl_x as [ax|al_x].
                +   subst x.
                    rewrite bl_eq in bl_uni.
                    exfalso; clear - bl_uni x_in.
                    apply in_list_conc in x_in.
                    destruct x_in as [x_in|x_in].
                    *   apply (list_in_not_unique bl1 (a :: bl2) a);
                            try assumption.
                        left.
                        reflexivity.
                    *   apply (list_in_not_unique (bl1 ++ a :: list_end) bl2 a);
                            try assumption.
                        --  apply in_list_rconc.
                            left.
                            reflexivity.
                        --  rewrite <- list_conc_assoc.
                            cbn.
                            exact bl_uni.
                +   exact al_x.
        }
        assert (list_unique bl') as bl'_uni.
        {
            subst bl; unfold bl'.
            clear - bl_uni.
            induction bl1.
            -   cbn in *.
                apply bl_uni.
            -   cbn in *.
                split.
                +   intros contr.
                    apply bl_uni.
                    apply in_list_conc in contr as [contr|contr].
                    *   apply in_list_lconc.
                        exact contr.
                    *   apply in_list_rconc.
                        right.
                        exact contr.
                +   apply IHbl1.
                    apply bl_uni.
        }
        specialize (IHal (rand al_uni) bl' bl'_uni l_in').
        rewrite bl_eq.
        pose proof (list_perm_conc (a :: bl2) bl1) as eq.
        apply (list_perm_trans2 eq).
        cbn.
        apply list_perm_skip.
        apply (list_perm_trans IHal).
        apply list_perm_conc.
Qed.

Lemma list_perm_in_wlog {U} : ∀ al bl : list U,
        list_permutation al bl → (∀ x, in_list al x → in_list bl x).
    intros al bl albl x al_x.
    induction albl.
    -   contradiction al_x.
    -   destruct al_x as [eq|al_x].
        +   left.
            exact eq.
        +   right.
            exact (IHalbl al_x).
    -   destruct al_x as [eq|[eq|al_x]].
        +   right; left.
            exact eq.
        +   left.
            exact eq.
        +   right; right.
            exact al_x.
    -   apply IHalbl2.
        apply IHalbl1.
        exact al_x.
Qed.

Theorem list_perm_in {U} : ∀ al bl : list U,
        list_permutation al bl → (∀ x, in_list al x ↔ in_list bl x).
    intros al bl albl x.
    split; apply list_perm_in_wlog.
    -   exact albl.
    -   apply list_perm_sym.
        exact albl.
Qed.

Theorem list_perm_unique {U} : ∀ al bl : list U,
        list_permutation al bl → list_unique al → list_unique bl.
    intros al bl albl al_uni.
    induction albl.
    -   exact al_uni.
    -   cbn in *.
        split.
        +   intros contr.
            apply al_uni.
            apply (list_perm_in albl).
            exact contr.
        +   apply IHalbl.
            apply al_uni.
    -   cbn in *.
        rewrite not_or.
        rewrite not_or in al_uni.
        destruct al_uni as [[neq y_in] [x_in l_uni]].
        repeat split; try assumption.
        rewrite neq_sym.
        exact neq.
    -   apply IHalbl2.
        apply IHalbl1.
        exact al_uni.
Qed.

Theorem list_image_perm {U V} : ∀ al bl (f : U → V),
        list_permutation al bl →
        list_permutation (list_image al f) (list_image bl f).
    intros al bl f albl.
    induction albl.
    -   cbn.
        exact list_perm_nil.
    -   cbn.
        apply list_perm_skip.
        exact IHalbl.
    -   cbn.
        apply list_perm_swap.
    -   apply (list_perm_trans IHalbl1 IHalbl2).
Qed.

Theorem list_perm_split {U} : ∀ l1 l2 (x : U),
        list_permutation (l1 ++ x :: l2) (x :: l1 ++ l2).
    intros l1 l2 x.
    rewrite (list_add_conc).
    rewrite list_conc_assoc.
    change (x :: l1 ++ l2) with ((x :: l1) ++ l2).
    apply list_perm_lpart.
    apply list_perm_sym.
    apply list_perm_add.
Qed.

Theorem list_split_perm {U} : ∀ l (a : U), in_list l a → ∃ l',
        list_permutation l (a :: l').
    intros l a a_in.
    pose proof (in_list_split l a a_in) as [l1 [l2 l_eq]].
    rewrite l_eq.
    exists (l1 ++ l2).
    apply list_perm_split.
Qed.

Theorem list_perm_single {U} : ∀ (x : U) l, list_permutation (x :: list_end) l →
        l = x :: list_end.
    intros x l l_perm.
    remember (x :: list_end) as m in l_perm.
    induction l_perm.
    -   inversion Heqm.
    -   inversion Heqm.
        subst x0 l.
        apply list_perm_nil_eq in l_perm.
        rewrite <- l_perm.
        reflexivity.
    -   inversion Heqm.
    -   subst l.
        apply IHl_perm2.
        apply IHl_perm1.
        reflexivity.
Qed.

Theorem list_perm_eq {U} : ∀ l1 l2 : list U, l1 = l2 → list_permutation l1 l2.
    intros l1 l2 eq.
    rewrite eq.
    apply list_perm_refl.
Qed.

Theorem list_prop_perm {U} : ∀ (S : U → Prop) (l1 l2 : list U),
        list_permutation l1 l2 → list_prop S l1 → list_prop S l2.
    intros S l1 l2 eq Sl1.
    induction eq.
    -   exact Sl1.
    -   cbn.
        split.
        +   apply Sl1.
        +   apply IHeq.
            apply Sl1.
    -   repeat split; apply Sl1.
    -   exact (IHeq2 (IHeq1 Sl1)).
Qed.

Theorem list_perm_swap2 {U} : ∀ (a b : U) l1 l2, list_permutation l1 l2 →
        list_permutation (a :: b :: l1) (b :: a :: l2).
    intros a b l1 l2 eq.
    pose proof (list_perm_swap b a l1) as eq1.
    apply (list_perm_trans eq1).
    apply list_perm_skip.
    apply list_perm_skip.
    exact eq.
Qed.
