Require Import init.

Require Export ord_base.
Require Import ord_order.
Require Import ord_plus.
Require Import ord_mult.
Require Import set.
Require Import function.
Require Import nat.
Require Import card.
Require Import ord_induction.

(* begin hide *)
Open Scope card_scope.
Open Scope ord_scope.
(* end hide *)
Definition ord_fin_support {A B} (f : ord_U B → ord_U A) :=
    finite (|set_type (λ x, f x ≠ ord_zero (f x))|).

Record ord_pow_type A B := make_ord_pow {
    ord_pow_f : ord_U B → ord_U A;
    ord_pow_fin : finite (|set_type (
        λ x, ord_pow_f x ≠ ord_zero (ord_pow_f x)
    )|);
}.
Arguments make_ord_pow {A B}.
Arguments ord_pow_f {A B}.
Arguments ord_pow_fin {A B}.

Theorem ord_pow_eq : ∀ {A B : ord_type} {C D : ord_pow_type A B},
        (∀ x, ord_pow_f C x = ord_pow_f D x) → C = D.
    intros A B [Cf C_fin] [Df D_fin] eq.
    cbn in *.
    apply functional_ext in eq.
    subst.
    rewrite (proof_irrelevance C_fin D_fin).
    reflexivity.
Qed.

Theorem ord_pow_max_ex : ∀ {A B : ord_type} (C : ord_pow_type A B),
        (∃ x, ord_pow_f C x ≠ ord_zero (ord_pow_f C x)) →
        ∃ x, ord_pow_f C x ≠ ord_zero (ord_pow_f C x) ∧
             ∀ y, strict (ord_le B) x y →
                 ord_pow_f C y = ord_zero (ord_pow_f C y).
    intros A B C [x x_eq].
    get_ord_wo B.
    classic_contradiction contr.
    rewrite not_ex in contr.
    setoid_rewrite not_and in contr.
    setoid_rewrite not_not in contr.
    setoid_rewrite not_all in contr.
    pose proof (ord_pow_fin C) as C_fin.
    unfold finite in C_fin.
    rewrite <- nle_lt in C_fin.
    apply C_fin; clear C_fin.
    apply all_greater_inf_set.
    -   exists x.
        exact x_eq.
    -   intros [a a_neq].
        specialize (contr a) as [contr|[b contr]]; try contradiction.
        rewrite not_impl in contr.
        destruct contr as [b_lt b_neq].
        exists [b|b_neq].
        cbn.
        exact b_lt.
Qed.

Theorem ord_pow_max_dif_ex : ∀ {A B : ord_type} {C D : ord_pow_type A B},
        C ≠ D →
        ∃ x, ord_pow_f C x ≠ ord_pow_f D x ∧
             ∀ y, strict (ord_le B) x y → ord_pow_f C y = ord_pow_f D y.
    intros A B C D neq.
    get_ord_wo B.
    pose (S x := ord_pow_f C x ≠ ord_pow_f D x).
    assert (∃ x, S x) as S_ex.
    {
        classic_contradiction contr.
        rewrite not_ex in contr.
        unfold S in contr.
        setoid_rewrite not_not in contr.
        apply neq.
        apply ord_pow_eq.
        exact contr.
    }
    assert (finite (|set_type S|)) as S_fin.
    {
        pose (N (O : ord_pow_type A B) x :=
            ord_pow_f O x ≠ ord_zero (ord_pow_f O x)).
        assert (|set_type S| <= |set_type (N C)| + |set_type (N D)|) as leq.
        {
            unfold le, plus; equiv_simpl.
            assert (∀ x : set_type S, {N C [x|]} + {N D [x|]}) as x_in.
            {
                intros x.
                classic_case (N C [x|]) as [Cx|nCx].
                -   left; exact Cx.
                -   right.
                    unfold N in *.
                    rewrite not_not in nCx.
                    destruct x as [x Sx]; cbn in *.
                    unfold S in Sx.
                    rewrite nCx in Sx.
                    rewrite neq_sym.
                    rewrite (ord_zero_eq _ (ord_pow_f C x)).
                    exact Sx.
            }
            exists (λ x, match x_in x with
                         | strong_or_left H => inl ([[x|]|H])
                         | strong_or_right H => inr ([[x|]|H])
                         end).
            intros a b eq.
            destruct (x_in a); destruct (x_in b).
            all: inversion eq as [eq2].
            all: apply set_type_eq in eq2.
            all: exact eq2.
        }
        apply (le_lt_trans leq).
        pose proof (fin_nat_ex _ (ord_pow_fin C)) as [m m_eq].
        pose proof (fin_nat_ex _ (ord_pow_fin D)) as [n n_eq].
        unfold N; rewrite <- m_eq, <- n_eq.
        rewrite nat_to_card_plus.
        apply nat_is_finite.
    }
    pose proof (finite_well_ordered_set_max _ S_fin S_ex) as [x [Sx x_max]].
    exists x.
    split.
    -   exact Sx.
    -   intros y y_gt.
        classic_contradiction Sy.
        specialize (x_max y Sy).
        pose proof (op_le_lt_trans x_max y_gt) as [leq neq2].
        contradiction.
Qed.

Definition ord_pow_le (A B : ord_type) (C D : ord_pow_type A B) :=
    (∀ x, ord_pow_f C x = ord_pow_f D x) ∨
    (∃ x, strict (ord_le A) (ord_pow_f C x) (ord_pow_f D x) ∧
     ∀ y, strict (ord_le B) x y → ord_pow_f C y = ord_pow_f D y).

(* begin hide *)
Lemma ord_pow_wo_wo : ∀ A B,
        ∀ S : (ord_pow_type A B → Prop), (∃ C, S C) →
        ∃ M, is_least (ord_pow_le A B) S M.
    intros A B.
    remember (to_equiv_type ord_equiv B) as β.
    revert B Heqβ.
    induction β using transfinite_induction.
    rename H into ind.
    intros B β_eq.
    get_ord_wo A.
    get_ord_wo B.
    intros S S_ex.
    classic_case (∃ C, S C ∧ ∀ x, ord_pow_f C x = ord_zero (ord_pow_f C x))
        as [C_ex|C_nex].
    {
        destruct C_ex as [C [SC C_zero]].
        exists C.
        split.
        -   exact SC.
        -   intros D SD.
            classic_case (C = D) as [eq|neq].
            +   left.
                intros x.
                subst.
                reflexivity.
            +   right.
                assert (∃ x, ord_pow_f D x ≠ ord_zero (ord_pow_f D x)) as D_ex.
                {
                    classic_contradiction contr.
                    rewrite not_ex in contr.
                    setoid_rewrite not_not in contr.
                    apply neq.
                    apply ord_pow_eq.
                    intros x.
                    rewrite C_zero, contr.
                    apply ord_zero_eq.
                }
                pose proof (ord_pow_max_ex D D_ex) as [x [x_neq x_gt]].
                exists x.
                rewrite C_zero.
                repeat split.
                *   apply ord_zero_le.
                *   rewrite neq_sym.
                    rewrite (ord_zero_eq _ (ord_pow_f D x)).
                    exact x_neq.
                *   intros y y_gt.
                    specialize (x_gt y y_gt).
                    rewrite x_gt.
                    rewrite C_zero.
                    apply ord_zero_eq.
    }
    assert (∀ C : set_type S,
        ∃ x, ord_pow_f [C|] x ≠ ord_zero (ord_pow_f [C|] x)) as max_ex.
    {
        intros [C SC]; cbn.
        rewrite not_ex in C_nex.
        setoid_rewrite not_and in C_nex.
        specialize (C_nex C) as [C_nex|C_nex]; try contradiction.
        rewrite not_all in C_nex.
        exact C_nex.
    }
    clear C_nex.
    pose (T x := ∃ C : set_type S, x = ex_val (ord_pow_max_ex _ (max_ex C))).
    assert (∃ x, T x) as T_ex.
    {
        destruct S_ex as [C SC].
        exists (ex_val (ord_pow_max_ex C (max_ex [C|SC]))).
        exists [C|SC].
        reflexivity.
    }
    pose proof (well_ordered T T_ex) as [m [Tm m_least]].
    pose (L (C : ord_pow_type A B) :=
        ∀ y, strict (ord_le B) m y → ord_pow_f C y = ord_zero (ord_pow_f C y)).
    pose (T' x := ∃ C, S C ∧ L C ∧ ord_pow_f C m = x).
    assert (∃ x, T' x) as T'_ex.
    {
        destruct Tm as [[C SC] Tm]; cbn in Tm.
        exists (ord_pow_f C m).
        exists C.
        repeat split.
        -   exact SC.
        -   rewrite_ex_val x xH.
            destruct xH as [x_neq x_gt].
            subst x.
            exact x_gt.
    }
    pose proof (well_ordered T' T'_ex) as [a [T'a a_least]].
    pose (B' := initial_segment B m).
    assert (∀ S : ord_pow_type A B' → Prop, (∃ C, S C) →
        ∃ M, is_least (ord_pow_le A B') S M) as B'_wf.
    {
        apply (ind (to_equiv_type ord_equiv B')); try reflexivity.
        rewrite β_eq.
        rewrite ord_lt_initial.
        exists m.
        unfold B'.
        apply ord_eq_reflexive.
    }
    pose (F_base (C : ord_pow_type A B) := λ (x : ord_U B'), ord_pow_f C [x|]).
    assert (∀ C, finite (|set_type (
        λ x, (F_base C x) ≠ ord_zero (F_base C x)
    )|)) as F_fin.
    {
        intros C.
        assert (|set_type (λ x, F_base C x ≠ ord_zero (F_base C x))| <=
                |set_type (λ x, ord_pow_f C x ≠ ord_zero (ord_pow_f C x))|)
            as ltq.
        {
            unfold le; equiv_simpl.
            assert (∀ x, F_base C x ≠ ord_zero (F_base C x) →
                ord_pow_f C [x|] ≠ ord_zero (ord_pow_f C [x|])) as f_in.
            {
                intros x x_neq.
                unfold F_base in x_neq.
                exact x_neq.
            }
            exists (λ x, [[[x|]|]|f_in [x|] [|x]]).
            intros x y eq.
            inversion eq as [eq2].
            do 2 apply set_type_eq in eq2.
            exact eq2.
        }
        apply (le_lt_trans ltq).
        apply ord_pow_fin.
    }
    pose (F C := make_ord_pow (F_base C) (F_fin C)).
    pose (R C := S C ∧ L C ∧ ord_pow_f C m = a).
    pose (R' C' := ∃ C, R C ∧ F C = C').
    assert (∃ C', R' C') as R'_ex.
    {
        destruct T'a as [C RC].
        exists (F C).
        exists C.
        split; try reflexivity.
        exact RC.
    }
    pose proof (B'_wf R' R'_ex) as [M' [[M [[SM [LM M_eq]] M'_eq]] M'_min]].
    clear B'_wf.
    exists M.
    split; try exact SM.
    intros C SC.
    classic_case (C = M) as [eq|neq].
    {
        subst.
        left.
        reflexivity.
    }
    right.
    pose proof (ord_pow_max_dif_ex neq) as [x [x_neq x_gt]].
    exists x.
    repeat split.
    -   classic_case (strict (ord_le B) m x) as [ltq|leq].
        +   rewrite LM by exact ltq.
            apply ord_zero_le.
        +   rewrite op_nlt_le in leq.
            assert (L C) as LC.
            {
                intros b b_gt.
                rewrite x_gt by exact (op_le_lt_trans leq b_gt).
                rewrite LM by exact b_gt.
                apply ord_zero_eq.
            }
            assert (T' (ord_pow_f C m)) as T'm.
            {
                exists C.
                repeat split; auto.
            }
            classic_case (R' (F C)) as [R'FC|nR'FC].
            *   specialize (M'_min (F C) R'FC).
                rewrite <- M'_eq in M'_min.
                classic_case (x = m) as [eq2|neq2].
                {
                    subst x.
                    rewrite M_eq.
                    apply a_least.
                    exists C.
                    repeat split; auto.
                }
                destruct M'_min as [eq|M'_min].
                --  specialize (eq [x|make_and leq neq2]).
                    cbn in eq.
                    unfold F_base in eq; cbn in eq.
                    symmetry in eq; contradiction.
                --  destruct M'_min as [[y y_ltm] [y_lt y_gt]].
                    cbn in y_lt.
                    unfold F_base in y_lt; cbn in y_lt.
                    cbn in y_gt.
                    unfold F_base in y_gt; cbn in y_gt.
                    destruct (trichotomy x y) as [[ltq2|eq2]|ltq2].
                    ++  rewrite x_gt in y_lt by exact ltq2.
                        destruct y_lt; contradiction.
                    ++  subst y.
                        apply y_lt.
                    ++  specialize (y_gt [x|make_and leq neq2]); cbn in y_gt.
                        rewrite y_gt in x_neq; try contradiction.
                        split; cbn.
                        **  apply ltq2.
                        **  intro contr.
                            inversion contr.
                            subst.
                            destruct ltq2; contradiction.
            *   classic_contradiction contr.
                apply nR'FC.
                exists C.
                split; try reflexivity.
                repeat split; try assumption.
                classic_case (x = m) as [eq|neq2].
                --  subst.
                    specialize (a_least _ T'm).
                    contradiction.
                --  rewrite <- M_eq.
                    rewrite x_gt by exact (make_and leq neq2).
                    reflexivity.
    -   rewrite neq_sym.
        exact x_neq.
    -   intros y y_gt.
        rewrite x_gt by exact y_gt.
        reflexivity.
Qed.

Lemma ord_pow_wo_antisym : ∀ A B, Antisymmetric (ord_pow_le A B).
    intros A B.
    get_ord_wo A.
    get_ord_wo B.
    split.
    intros C D CD DC.
    destruct CD as [eq|CD].
    2: destruct DC as [eq|DC].
    -   apply ord_pow_eq.
        exact eq.
    -   apply ord_pow_eq.
        intro; symmetry.
        apply eq.
    -   exfalso.
        destruct CD as [a [a_lt a_gt]].
        destruct DC as [b [b_lt b_gt]].
        destruct (trichotomy a b) as [[ltq|neq]|ltq].
        +   specialize (a_gt b ltq).
            rewrite a_gt in b_lt.
            destruct b_lt; contradiction.
        +   subst.
            pose proof (trans a_lt b_lt) as [leq neq].
            contradiction.
        +   specialize (b_gt a ltq).
            rewrite b_gt in a_lt.
            destruct a_lt; contradiction.
Qed.
(* end hide *)
Lemma ord_pow_wo : ∀ A B, well_orders (ord_pow_le A B).
    intros A B.
    get_ord_wo A.
    get_ord_wo B.
    repeat split.
    -   intros C D.
        classic_case (C = D) as [eq|neq].
        +   subst.
            left; left.
            reflexivity.
        +   apply or_to_strong.
            pose proof (ord_pow_max_dif_ex neq) as [x [x_neq y_eq]].
            destruct (connex (ord_pow_f C x) (ord_pow_f D x)) as [leq|leq].
            *   left; right.
                exists x.
                repeat split; assumption.
            *   right; right.
                exists x.
                rewrite neq_sym in x_neq.
                repeat split; try assumption.
                intros y y_lt.
                symmetry; apply y_eq.
                exact y_lt.
    -   apply ord_pow_wo_antisym.
    -   intros C D E CD DE.
        destruct CD as [eq|CD].
        2: destruct DE as [eq|DE].
        +   apply ord_pow_eq in eq.
            subst.
            exact DE.
        +   apply ord_pow_eq in eq.
            subst.
            right; exact CD.
        +   right.
            destruct CD as [a [a_lt a_gt]].
            destruct DE as [b [b_lt b_gt]].
            destruct (trichotomy a b) as [[ltq|neq]|ltq].
            *   exists b.
                split.
                --  rewrite a_gt by exact ltq.
                    exact b_lt.
                --  intros y y_gt.
                    rewrite a_gt by exact (trans ltq y_gt).
                    apply b_gt.
                    exact y_gt.
            *   subst.
                exists b.
                split.
                --  exact (trans a_lt b_lt).
                --  intros y y_gt.
                    rewrite a_gt by exact y_gt.
                    apply b_gt.
                    exact y_gt.
            *   exists a.
                split.
                --  rewrite <- b_gt by exact ltq.
                    exact a_lt.
                --  intros y y_gt.
                    rewrite a_gt by exact y_gt.
                    apply b_gt.
                    exact (trans ltq y_gt).
    -   intros S S_ex.
        pose proof (ord_pow_wo_wo A B S S_ex) as [M [SM M_min]].
        exists M.
        split; try exact SM.
        intros C SC C_neq C_leq.
        specialize (M_min C SC).
        pose proof (ord_pow_wo_antisym A B).
        pose proof (antisym C_leq M_min).
        contradiction.
Qed.

Notation "A ⊙ B" := (make_ord_type _ (ord_pow_le A B) (ord_pow_wo A B)).

(* begin hide *)
Lemma ord_pow_wd_fin : ∀ {A B C D} (F : ord_pow_type A C)
        (f : ord_U A → ord_U B) (g : ord_U D → ord_U C),
        bijective f → bijective g →
        (∀ a b, ord_le A a b ↔ ord_le B (f a) (f b)) →
        (∀ a b, ord_le D a b ↔ ord_le C (g a) (g b)) →
        ord_fin_support (λ x : ord_U D, f (ord_pow_f F (g x))).
    intros A B C D E f g f_bij g_bij f_iso g_iso.
    get_ord_wo A.
    get_ord_wo B.
    pose (F E := (λ x, f (ord_pow_f E (g x)))).
    pose (g' := bij_inv g g_bij).
    unfold ord_fin_support in *.
    assert (|set_type (λ x, ord_pow_f E x ≠ ord_zero (ord_pow_f E x))| =
            |set_type (λ x, F E x ≠ ord_zero (F E x))|) as eq.
    {
        equiv_simpl.
        assert (∀ x, ord_pow_f E x ≠ ord_zero (ord_pow_f E x) →
                F E (g' x) ≠ ord_zero (F E (g' x))) as nz.
        {
            unfold F.
            intros x x_neq x_eq.
            rewrite (inverse_eq2 _ _ (bij_inv_inv _ g_bij)) in x_eq.
            apply x_neq; clear x_neq.
            apply antisym; try apply ord_zero_le.
            rewrite f_iso.
            rewrite x_eq.
            apply ord_zero_le.
        }
        exists (λ x, [g' [x|] | nz [x|] [|x]]).
        split.
        -   intros a b eq.
            inversion eq as [eq2].
            apply (bij_inv_bij _ g_bij) in eq2.
            apply set_type_eq in eq2.
            exact eq2.
        -   intros [y y_nz].
            pose proof (rand (bij_inv_bij _ g_bij) y) as [x x_eq].
            assert (ord_pow_f E x ≠ ord_zero (ord_pow_f E x)) as x_in.
            {
                intro eq.
                apply y_nz; clear y_nz.
                subst y.
                apply antisym; try apply ord_zero_le.
                unfold F.
                rewrite (inverse_eq2 _ _ (bij_inv_inv _ g_bij)).
                rewrite <- (ord_zero_iso _ f f_bij f_iso).
                rewrite <- f_iso.
                rewrite eq.
                apply ord_zero_le.
            }
            exists [x|x_in].
            apply set_type_eq; cbn.
            exact x_eq.
    }
    unfold F in eq.
    rewrite <- eq.
    exact (ord_pow_fin E).
Qed.

Lemma ord_pow_wd : ∀ A B C D, A ~ B → C ~ D → A ⊙ C ~ B ⊙ D.
    intros A B C D [f [f_bij f_iso]] [g [g_bij g_iso]].
    get_ord_wo A.
    get_ord_wo B.
    pose (g' := bij_inv g g_bij).
    pose (F E := (λ x, f (ord_pow_f E (g' x)))).
    assert (∀ E, ord_fin_support (F E)) as F_fin.
    {
        intros E.
        apply ord_pow_wd_fin; try assumption.
        -   apply bij_inv_bij.
        -   intros a b.
            rewrite g_iso.
            do 2 rewrite (inverse_eq2 _ _ (bij_inv_inv _ g_bij)).
            reflexivity.
    }
    exists (λ E, make_ord_pow (F E) (F_fin E)).
    split.
    1: split.
    -   intros [Xf X_fin] [Yf Y_fin] eq; cbn in *.
        apply ord_pow_eq; cbn.
        inversion eq as [eq2].
        unfold F in eq2; cbn in eq2.
        intros x.
        pose proof (func_eq _ _ eq2 (g x)) as eq3.
        cbn in eq3.
        apply f_bij in eq3.
        rewrite (inverse_eq1 _ _ (bij_inv_inv _ g_bij)) in eq3.
        exact eq3.
    -   intros Y.
        pose (f' := bij_inv f f_bij).
        pose (F' (x : ord_U C) := f' (ord_pow_f Y (g x))).
        assert (ord_fin_support F') as F'_fin.
        {
            apply ord_pow_wd_fin; try assumption.
            -   apply bij_inv_bij.
            -   intros a b.
                rewrite f_iso.
                do 2 rewrite (inverse_eq2 _ _ (bij_inv_inv _ f_bij)).
                reflexivity.
        }
        exists (make_ord_pow F' F'_fin).
        apply ord_pow_eq.
        intros x.
        unfold F'; cbn.
        unfold F; cbn.
        rewrite (inverse_eq2 _ _ (bij_inv_inv _ f_bij)).
        rewrite (inverse_eq2 _ _ (bij_inv_inv _ g_bij)).
        reflexivity.
    -   intros X Y.
        cbn.
        unfold F; cbn.
        split.
        +   intros [eq|[x [x_lt x_gt]]].
            *   left.
                intros x; cbn.
                rewrite eq.
                reflexivity.
            *   right; cbn.
                exists (g x).
                split.
                --  rewrite (inverse_eq1 _ _ (bij_inv_inv _ g_bij)).
                    rewrite <- (ord_iso_strict f_bij f_iso).
                    exact x_lt.
                --  intros y y_lt.
                    rewrite <- (inverse_eq2 _ g' (bij_inv_inv _ g_bij) y) in y_lt.
                    rewrite <- (ord_iso_strict g_bij g_iso) in y_lt.
                    apply f_equal.
                    exact (x_gt _ y_lt).
        +   intros [eq|[x [x_lt x_gt]]].
            *   left.
                cbn in eq.
                intros x.
                specialize (eq (g x)).
                apply f_bij in eq.
                rewrite (inverse_eq1 _ _ (bij_inv_inv _ g_bij)) in eq.
                exact eq.
            *   right; cbn in *.
                exists (g' x).
                split.
                --  rewrite (ord_iso_strict f_bij f_iso).
                    exact x_lt.
                --  intros y y_lt.
                    rewrite (ord_iso_strict g_bij g_iso) in y_lt.
                    rewrite (inverse_eq2 _ _ (bij_inv_inv _ g_bij)) in y_lt.
                    specialize (x_gt _ y_lt).
                    apply f_bij in x_gt.
                    rewrite (inverse_eq1 _ _ (bij_inv_inv _ g_bij)) in x_gt.
                    exact x_gt.
Qed.
(* end hide *)
Definition ord_pow := binary_self_op ord_pow_wd.
Infix "^" := ord_pow : ord_scope.
(* begin hide *)
Close Scope ord_scope.
Close Scope card_scope.
(* end hide *)
