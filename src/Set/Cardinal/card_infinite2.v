Require Import init.

Require Export card_base.
Require Import card_order.
Require Import card_plus.
Require Import card_mult.
Require Import card_nat.
Require Import set.
Require Import zorn.
Require Import function.
Require Import nat.
Require Import order_minmax.
Require Import card_infinite1.

(* begin hide *)
Open Scope card_scope.

Module CardMultIdemp.
Section CardMultIdemp.

Variable A : Type.
Hypothesis A_inf : |nat| ≤ |A|.

Record fs := make_fs {
    fs_f : bin_set_function_type A A;
    fs_range : ∀ a b, bin_domain fs_f (fs_f⟨a, b⟩);
    fs_inj : ∀ a b c d, fs_f⟨a, b⟩ = fs_f⟨c, d⟩ → a = c ∧ b = d;
    fs_sur : ∀ c, bin_domain fs_f c → ∃ a b, fs_f⟨a, b⟩ = c;
}.

Definition fs_le f g := bin_func_le (fs_f f) (fs_f g).
Local Instance fs_le_class : Order fs := {
    le := fs_le
}.
Lemma fs_le_refl : ∀ f, f ≤ f.
Proof.
    intros f.
    unfold le; cbn.
    unfold fs_le.
    apply refl.
Qed.
Local Instance fs_le_refl_class : Reflexive le := {
    refl := fs_le_refl
}.
Lemma fs_le_antisym : ∀ f g, f ≤ g → g ≤ f → f = g.
Proof.
    intros f g.
    unfold le; cbn.
    unfold fs_le.
    intros fg gf.
    pose proof (antisym fg gf) as eq.
    destruct f as [f_f f_range f_inj f_sur].
    destruct g as [g_f g_range g_inj g_sur].
    cbn in *.
    subst.
    rewrite (proof_irrelevance f_range g_range).
    rewrite (proof_irrelevance f_inj g_inj).
    rewrite (proof_irrelevance f_sur g_sur).
    reflexivity.
Qed.
Local Instance fs_le_antisym_class : Antisymmetric le := {
    antisym := fs_le_antisym
}.
Lemma fs_le_trans : ∀ f g h, f ≤ g → g ≤ h → f ≤ h.
Proof.
    intros f g h.
    unfold le; cbn.
    unfold fs_le.
    apply trans.
Qed.
Local Instance fs_le_trans_class : Transitive le := {
    trans := fs_le_trans
}.

Section UpperBound.

Local Open Scope set_scope.

Variable C : fs → Prop.
Hypothesis C_chain : is_chain le C.

Definition C_union_set x := ∃ f, C f ∧ bin_domain (fs_f f) x.

Lemma combining_f_ex : ∀ x y : set_type (C_union_set),
    ∃ f, C f ∧ bin_domain (fs_f f) [x|] ∧ bin_domain (fs_f f) [y|].
Proof.
    intros [x [f1 [Cf1 f1x]]] [y [f2 [Cf2 f2y]]]; cbn.
    specialize (C_chain f1 f2 Cf1 Cf2) as [leq|leq].
    -   exists f2.
        repeat split; try assumption.
        apply leq.
        exact f1x.
    -   exists f1.
        repeat split; try assumption.
        apply leq.
        exact f2y.
Qed.

Definition C_union_f (x y : set_type (C_union_set)) :=
    fs_f (ex_val (combining_f_ex x y))⟨
        [_|land (rand (ex_proof (combining_f_ex x y)))],
        [_|rand (rand (ex_proof (combining_f_ex x y)))]
    ⟩.

Lemma all_equal : ∀ F G, C F → C G → ∀ a b
    (Fa : bin_domain (fs_f F) a) (Fb : bin_domain (fs_f F) b)
    (Ga : bin_domain (fs_f G) a) (Gb : bin_domain (fs_f G) b),
    (fs_f F)⟨[a|Fa], [b|Fb]⟩ = (fs_f G)⟨[a|Ga], [b|Gb]⟩.
Proof.
    intros F G CF CG a b Fa Fb Ga Gb.
    destruct (C_chain F G CF CG) as [[sub FG]|[sub GF]].
    -   specialize (FG [a|Fa] [b|Fb]); cbn in FG.
        rewrite (proof_irrelevance _ Ga) in FG.
        rewrite (proof_irrelevance _ Gb) in FG.
        exact FG.
    -   specialize (GF [a|Ga] [b|Gb]); cbn in GF.
        rewrite (proof_irrelevance _ Fa) in GF.
        rewrite (proof_irrelevance _ Fb) in GF.
        symmetry; exact GF.
Qed.

Lemma C_union_f_range : ∀ a b, C_union_set (C_union_f a b).
Proof.
    intros [x [f1 [Cf1 f1x]]] [y [f2 [Cf2 f2y]]]; cbn.
    unfold C_union_set, C_union_f; cbn.
    destruct (C_chain f1 f2 Cf1 Cf2) as [[sub leq]|[sub leq]];
        cbn in *; clear leq.
    -   exists f2.
        split; try assumption.
        unfold C_union_f; cbn.
        unfold ex_val, ex_proof.
        destruct (ex_to_type _) as [g [Cg [gx gy]]]; cbn.
        rewrite (proof_irrelevance _ gx).
        rewrite (proof_irrelevance _ gy).
        rewrite (all_equal g f2 Cg Cf2 x y gx gy (sub x f1x) f2y).
        apply (fs_range f2).
    -   exists f1.
        split; try assumption.
        unfold C_union_f; cbn.
        unfold ex_val, ex_proof.
        destruct (ex_to_type _) as [g [Cg [gx gy]]]; cbn.
        rewrite (proof_irrelevance _ gx).
        rewrite (proof_irrelevance _ gy).
        rewrite (all_equal g f1 Cg Cf1 x y gx gy (f1x) (sub y f2y)).
        apply (fs_range f1).
Qed.

Lemma C_union_f_inj : ∀ a b c d, C_union_f a b = C_union_f c d → a = c ∧ b = d.
Proof.
    intros [a Ca] [b Cb] [c Cc] [d Cd] eq.
    unfold C_union_f, ex_val, ex_proof in eq.
    destruct (ex_to_type _) as [f1 [Cf1 [f1a f1b]]].
    destruct (ex_to_type _) as [f2 [Cf2 [f2c f2d]]].
    cbn in *.
    rewrite (proof_irrelevance _ f1a) in eq.
    rewrite (proof_irrelevance _ f1b) in eq.
    rewrite (proof_irrelevance _ f2c) in eq.
    rewrite (proof_irrelevance _ f2d) in eq.
    destruct (C_chain f1 f2 Cf1 Cf2) as [[sub leq]|[sub leq]].
    -   rewrite leq in eq; cbn in eq.
        apply (fs_inj f2) in eq.
        destruct eq as [eq1 eq2].
        inversion eq1.
        inversion eq2.
        subst.
        split; apply set_type_eq; reflexivity.
    -   rewrite leq in eq; cbn in eq.
        apply (fs_inj f1) in eq.
        destruct eq as [eq1 eq2].
        inversion eq1.
        inversion eq2.
        subst.
        split; apply set_type_eq; reflexivity.
Qed.

Lemma C_union_f_sur : ∀ c, C_union_set c → ∃ a b, C_union_f a b = c.
Proof.
    intros c [f [Cf fc]].
    pose proof (fs_sur f c fc) as [[a fa] [[b fb] eq]].
    assert (C_union_set a) as Ca by (exists f; split; assumption).
    assert (C_union_set b) as Cb by (exists f; split; assumption).
    exists [a|Ca], [b|Cb].
    unfold C_union_f, ex_val, ex_proof.
    destruct (ex_to_type _) as [g [Cg [ga gb]]]; cbn in *.
    rewrite <- eq.
    apply all_equal; assumption.
Qed.

Lemma zorn_piece : has_upper_bound le C.
Proof.
    exists (make_fs
        (make_bin_set_function C_union_set C_union_f)
        C_union_f_range
        C_union_f_inj
        C_union_f_sur
    ).
    intros f Cf.
    unfold le; cbn.
    unfold fs_le; cbn.
    unfold bin_func_le; cbn.
    assert (bin_domain (fs_f f) ⊆ C_union_set) as sub.
    {
        intros x fx.
        exists f.
        split; assumption.
    }
    exists sub.
    intros [x fx] [y fy]; cbn.
    unfold C_union_f; cbn.
    unfold ex_val, ex_proof.
    destruct (ex_to_type _) as [g [Cg [gx gy]]]; cbn in *.
    rewrite (proof_irrelevance _ gx).
    rewrite (proof_irrelevance _ gy).
    specialize (C_chain f g Cf Cg) as [[sub2 fg]|[sub2 gf]].
    -   specialize (fg [x|fx] [y|fy]); cbn in fg.
        rewrite (proof_irrelevance _ gx) in fg.
        rewrite (proof_irrelevance _ gy) in fg.
        exact fg.
    -   specialize (gf [x|gx] [y|gy]); cbn in gf.
        rewrite (proof_irrelevance _ fx) in gf.
        rewrite (proof_irrelevance _ fy) in gf.
        symmetry; exact gf.
Qed.

End UpperBound.

Definition f := ex_val (zorn le zorn_piece).
Lemma f_max : ∀ g, ¬(f < g).
Proof.
    intros g.
    unfold f.
    rewrite_ex_val C0 H0. (* For some reason using H breaks it? *)
    apply H0.
Qed.

Definition X := bin_domain (fs_f f).

Lemma X_mult_idemp : |set_type X| * |set_type X| = |set_type X|.
Proof.
    unfold mult; equiv_simpl.
    exists (λ x, [fs_f f⟨fst x, snd x⟩ | fs_range f (fst x) (snd x)]).
    split.
    -   intros [a b] [c d] eq; cbn in *.
        inversion eq as [eq2].
        pose proof (fs_inj f a b c d eq2) as [eq3 eq4].
        subst.
        reflexivity.
    -   intros [y fy].
        pose proof (fs_sur f y fy) as [x1 [x2 x_eq]].
        exists (x1, x2).
        apply set_type_eq; cbn.
        exact x_eq.
Qed.

Lemma X_not_0 : |set_type X| ≠ 0.
Proof.
    intro contr.
    pose proof (card_le_sub _ _ A_inf) as [A' A'_eq].
    pose proof nat_mult_nat as eq.
    rewrite <- A'_eq in eq.
    unfold mult in eq; equiv_simpl in eq.
    destruct eq as [g g_bij].
    assert (∀ a b, A' [g (a, b)|]) as g_range.
    {
        intros a b.
        apply [|g (a, b)].
    }
    assert (∀ a b c d, [g (a, b)|] = [g (c, d)|] → a = c ∧ b = d) as g_inj.
    {
        intros a b c d eq.
        apply set_type_eq in eq.
        apply g_bij in eq.
        inversion eq.
        split; reflexivity.
    }
    assert (∀ c, A' c → ∃ a b, [g (a, b)|] = c) as g_sur.
    {
        intros c A'c.
        pose proof (rand g_bij [c|A'c]) as [[a b] eq].
        exists a, b.
        rewrite eq.
        reflexivity.
    }
    apply (f_max (make_fs
        (make_bin_set_function A' (λ a b, [g (a, b)|]))
        g_range
        g_inj
        g_sur
    )).
    split.
    -   unfold le; cbn.
        unfold fs_le; cbn.
        assert (X = ∅)%set as X_empty.
        {
            apply not_ex_empty.
            intros x Xx.
            unfold zero in contr; cbn in contr.
            unfold nat_to_card in contr; equiv_simpl in contr.
            destruct contr as [f f_bij].
            contradiction (nat_lt_0_false (f [x|Xx])).
        }
        assert (X ⊆ A')%set as sub.
        {
            rewrite X_empty.
            apply empty_sub.
        }
        exists sub.
        intros a.
        unfold X in X_empty.
        exfalso.
        rewrite X_empty in a.
        destruct a; contradiction.
    -   intro contr2.
        assert (X = A') as X_eq.
        {
            unfold X.
            rewrite contr2.
            cbn.
            reflexivity.
        }
        rewrite X_eq in contr.
        rewrite contr in A'_eq.
        clear - A'_eq.
        pose proof (nat_is_finite 0) as [leq neq].
        contradiction.
Qed.

Lemma X_not_1 : |set_type X| ≠ 1.
Proof.
    intro contr.
    pose proof (card_le_sub _ _ A_inf) as [A' A'_eq].
    assert (|set_type (A' ∪ X)%set| = |set_type A'|) as A'X_eq.
    {
        apply antisym.
        -   apply (trans (card_plus_union _ _)).
            rewrite contr.
            rewrite inf_plus_fin.
            +   apply refl.
            +   rewrite A'_eq.
                apply refl.
            +   apply nat_is_finite.
        -   apply card_union_left.
    }
    rewrite <- A'X_eq in A'_eq.
    pose proof nat_mult_nat as eq.
    rewrite <- A'_eq in eq.
    unfold mult, plus in eq; equiv_simpl in eq.
    destruct eq as [g g_bij].
    assert (∃ x, X x) as [x Xx].
    {
        symmetry in contr.
        unfold one in contr; cbn in contr.
        unfold nat_to_card in contr; equiv_simpl in contr.
        destruct contr as [f f_bij].
        pose proof (nat_lt_suc 0) as one_pos.
        exists [f [0|one_pos]|].
        apply [|f [0|one_pos]].
    }
    assert (∀ y, X y → x = y) as x_unique.
    {
        intros y Xy.
        symmetry in contr.
        unfold one in contr; cbn in contr.
        unfold nat_to_card in contr; equiv_simpl in contr.
        destruct contr as [f f_bij].
        pose proof (rand f_bij [x|Xx]) as [[m m_lt] m_eq].
        pose proof (rand f_bij [y|Xy]) as [[n n_lt] n_eq].
        pose proof m_lt as m_lt2.
        pose proof n_lt as n_lt2.
        apply nat_lt_one_eq in m_lt2.
        apply nat_lt_one_eq in n_lt2.
        subst.
        rewrite (proof_irrelevance m_lt n_lt) in m_eq.
        rewrite m_eq in n_eq.
        inversion n_eq.
        reflexivity.
    }
    remember (g ([x|make_ror Xx], [x|make_ror Xx])) as gx.
    pose (g' (a b : (set_type (A' ∪ X)%set)) :=
        If a = [x|make_ror Xx] ∧ b = [x|make_ror Xx]
        then x
        else If g (a, b) = [x|make_ror Xx]
        then [gx|]
        else [g (a, b)|]).
    assert (∀ a b, (A' ∪ X)%set (g' a b)) as g_range.
    {
        intros a b.
        unfold g'.
        repeat case_if.
        -   right; exact Xx.
        -   apply [|gx].
        -   apply [|g (a, b)].
    }
    assert (∀ a b c d, g' a b = g' c d → a = c ∧ b = d) as g_inj.
    {
        intros [a a_in] [b b_in] [c c_in] [d d_in] eq.
        unfold g' in eq.
        case_if.
        -   case_if.
            +   destruct a0 as [eq1 eq2], a1 as [eq3 eq4].
                inversion eq1; inversion eq2; inversion eq3; inversion eq4.
                subst.
                split; apply set_type_eq; reflexivity.
            +   case_if.
                *   subst x.
                    destruct gx as [gx gx_in]; cbn in *.
                    rewrite (proof_irrelevance _ gx_in) in e.
                    rewrite Heqgx in e.
                    apply g_bij in e.
                    inversion e as [[eq1 eq2]].
                    subst.
                    exfalso; apply n; clear.
                    split; apply set_type_eq; reflexivity.
                *   subst x; clear g' g_range.
                    exfalso; apply n0; clear.
                    apply set_type_eq; cbn.
                    reflexivity.
        -   case_if.
            +   case_if.
                *   subst x.
                    destruct gx as [gx gx_in]; cbn in *.
                    rewrite (proof_irrelevance _ gx_in) in e.
                    rewrite Heqgx in e.
                    apply g_bij in e.
                    inversion e as [[eq1 eq2]].
                    subst.
                    exfalso; apply n; clear.
                    split; apply set_type_eq; reflexivity.
                *   case_if.
                    --  rewrite <- e0 in e.
                        apply g_bij in e.
                        inversion e as [[eq1 eq2]].
                        subst.
                        split; apply set_type_eq; reflexivity.
                    --  rewrite Heqgx in eq.
                        apply set_type_eq in eq.
                        apply g_bij in eq.
                        inversion eq as [[eq1 eq2]].
                        subst.
                        exfalso; apply n0.
                        split; apply set_type_eq; reflexivity.
            +   case_if.
                *   subst x.
                    exfalso; apply n0.
                    apply set_type_eq; cbn.
                    reflexivity.
                *   case_if.
                    --  rewrite Heqgx in eq.
                        apply set_type_eq in eq.
                        apply g_bij in eq.
                        inversion eq as [[eq1 eq2]].
                        subst.
                        exfalso; apply n.
                        split; apply set_type_eq; reflexivity.
                    --  apply set_type_eq in eq.
                        apply g_bij in eq.
                        inversion eq as [[eq1 eq2]].
                        subst.
                        split; apply set_type_eq; reflexivity.
    }
    assert (∀ c, (A' ∪ X)%set c → ∃ a b, g' a b = c) as g_sur.
    {
        intros c A'xc.
        classic_case (c = x) as [eq|neq].
        2: classic_case (c = [gx|]) as [eq|neq2].
        -   subst.
            exists [x|make_ror Xx], [x|make_ror Xx].
            unfold g'; cbn.
            case_if; try reflexivity.
            case_if.
            +   rewrite e.
                reflexivity.
            +   exfalso; apply n.
                split; reflexivity.
        -   subst c.
            pose proof (rand g_bij [x|make_ror Xx]) as [[a b] eq].
            exists a, b.
            unfold g'; case_if.
            +   destruct a0; subst.
                rewrite eq in neq.
                contradiction.
            +   case_if; try reflexivity.
                contradiction.
        -   pose proof (rand g_bij [c|A'xc]) as [[a b] eq].
            exists a, b.
            unfold g'.
            case_if.
            +   destruct a0; subst a b.
                rewrite <- Heqgx in eq.
                symmetry in eq.
                rewrite <- eq in neq2.
                contradiction.
            +   case_if.
                *   rewrite eq in e.
                    inversion e.
                    contradiction.
                *   rewrite eq.
                    reflexivity.
    }
    apply (f_max (make_fs
        (make_bin_set_function (A' ∪ X)%set g')
        g_range
        g_inj
        g_sur
    )).
    split.
    -   unfold le; cbn.
        unfold fs_le; cbn.
        exists (union_rsub _ _).
        intros [a Xa] [b Xb]; cbn.
        unfold g'.
        case_if.
        +   destruct a0 as [eq1 eq2].
            inversion eq1.
            inversion eq2.
            subst.
            symmetry; apply x_unique.
            apply (fs_range f).
        +   exfalso.
            rewrite not_and in n.
            destruct n as [neq|neq].
            *   apply neq.
                apply set_type_eq; cbn.
                symmetry; apply x_unique.
                exact Xa.
            *   apply neq.
                apply set_type_eq; cbn.
                symmetry; apply x_unique.
                exact Xb.
    -   intro contr2.
        assert (X = A' ∪ X)%set as XA'_eq.
        {
            unfold X.
            rewrite contr2.
            cbn.
            rewrite union_assoc.
            rewrite union_idemp.
            reflexivity.
        }
        clear contr2.
        assert (∃ y, A' y ∧ x ≠ y) as [y [A'y y_neq]].
        {
            rewrite A'X_eq in A'_eq.
            clear - A'_eq.
            symmetry in A'_eq.
            equiv_simpl in A'_eq.
            destruct A'_eq as [f f_bij].
            classic_case (x = [f 0|]) as [eq|neq].
            -   exists [f 1|].
                split.
                +   apply [|f 1].
                +   intro eq1; subst.
                    apply set_type_eq in eq1.
                    apply f_bij in eq1.
                    inversion eq1.
            -   exists [f 0|].
                split; try exact neq.
                apply [|f 0].
        }
        apply y_neq; clear y_neq.
        apply x_unique.
        rewrite XA'_eq.
        left.
        exact A'y.
Qed.

Section XInf.

Hypothesis contr : finite (|set_type X|).

Lemma X_fin_false : False.
Proof.
    apply fin_nat_ex in contr as [n eq1].
    assert (0 ≠ n) as n_neq_0.
    {
        intro contr; subst.
        symmetry in eq1.
        contradiction (X_not_0 eq1).
    }
    assert (1 ≠ n) as n_neq_1.
    {
        intro contr; subst.
        symmetry in eq1.
        contradiction (X_not_1 eq1).
    }
    pose proof X_mult_idemp as eq2.
    rewrite <- eq1 in eq2; clear eq1.
    rewrite nat_to_card_mult in eq2.
    apply nat_to_card_eq in eq2.
    nat_destruct n; try contradiction.
    nat_destruct n; try contradiction.
    clear n_neq_0 n_neq_1.
    rewrite nat_mult_lsuc in eq2.
    rewrite <- (plus_rid (nat_suc (nat_suc n))) in eq2 at 3.
    apply plus_lcancel in eq2.
    rewrite nat_mult_rsuc in eq2.
    rewrite nat_plus_lsuc in eq2.
    inversion eq2.
Qed.

End XInf.

Lemma X_inf : infinite (|set_type X|).
Proof.
    classic_contradiction contr.
    apply X_fin_false.
    unfold infinite in contr.
    rewrite nle_lt in contr.
    exact contr.
Qed.

Lemma X_ex : ∃ a, X a.
Proof.
    pose proof X_inf as inf.
    unfold infinite, le in inf; equiv_simpl in inf.
    destruct inf as [f f_inj].
    exists [f 0|].
    apply [|f 0].
Qed.

Lemma X_le : |set_type X| ≤ |A|.
Proof.
    unfold le; equiv_simpl.
    exists (λ x, [x|]).
    intros a b eq.
    apply set_type_eq in eq.
    exact eq.
Qed.

Section Contr.

Hypothesis contr : |set_type X| ≠ |A|.

Definition X' x := ¬X x.

Lemma XX'_eq : |set_type X| + |set_type X'| = |A|.
Proof.
    unfold plus; equiv_simpl.
    exists (λ x, match x with | inl x' => [x'|] | inr x' => [x'|] end).
    split.
    -   intros [[a Xa]|[a X'a]] [[b Xb]|[b X'b]] eq; cbn in eq; subst.
        +   apply f_equal.
            apply set_type_eq; reflexivity.
        +   contradiction.
        +   contradiction.
        +   apply f_equal.
            apply set_type_eq; reflexivity.
    -   intros c.
        classic_case (X c) as [Xc|X'c].
        +   exists (inl [c|Xc]); reflexivity.
        +   exists (inr [c|X'c]); reflexivity.
Qed.

Lemma X'_ge : |set_type X| ≤ |set_type X'|.
Proof.
    classic_contradiction ltq.
    rewrite nle_lt in ltq.
    apply contr.
    apply antisym; try exact X_le.
    rewrite <- XX'_eq.
    destruct ltq as [leq neq].
    apply le_lplus with (|set_type X|) in leq.
    apply (trans leq).
    rewrite <- (mult_lid (|set_type X|)) at 1 2.
    rewrite <- rdist.
    rewrite <- X_mult_idemp at 2.
    apply card_le_rmult.
    unfold one; cbn.
    rewrite nat_to_card_plus.
    apply (trans (land (nat_is_finite 2)) X_inf).
Qed.
Lemma f0_ex : ∃ f : set_type X → set_type X', injective f.
Proof.
    pose proof X'_ge.
    unfold le in H; equiv_simpl in H.
    exact H.
Qed.

Definition f0 := ex_val f0_ex.
Definition Y y := ∃ x, [f0 x|] = y.

Lemma Y_eq : |set_type X| = |set_type Y|.
Proof.
    equiv_simpl.
    assert (∀ x, Y [f0 x|]) as f_in by (intro x; exists x; reflexivity).
    exists (λ x, [_|f_in x]).
    split.
    -   intros a b eq.
        inversion eq as [eq2].
        apply set_type_eq in eq2.
        apply (ex_proof f0_ex) in eq2.
        exact eq2.
    -   intros [y [x eq]].
        exists x.
        apply set_type_eq; cbn.
        exact eq.
Qed.

Lemma Y_eq2 :
    |set_type X| * |set_type Y| +
    |set_type Y| * |set_type X| +
    |set_type Y| * |set_type Y| = |set_type Y|.
Proof.
    rewrite <- Y_eq.
    rewrite X_mult_idemp.
    rewrite <- (mult_lid (|set_type X|)) at 1 2 3.
    do 2 rewrite <- rdist.
    assert (nat_to_card 3 = 2 + 1) as eq.
    {
        unfold one at 4 5 6; cbn.
        do 2 rewrite nat_to_card_plus.
        reflexivity.
    }
    rewrite <- eq; clear eq.
    apply antisym.
    -   rewrite <- X_mult_idemp at 2.
        apply card_le_rmult.
        pose proof (nat_is_finite 3) as three_fin.
        exact (trans (land three_fin) X_inf).
    -   rewrite <- (mult_lid (|set_type X|)) at 1.
        apply card_le_rmult.
        unfold one at 1; cbn.
        unfold nat_to_card, le; equiv_simpl.
        exists (λ (x : set_type (λ x, x < 1)),
            [[x|]|trans (trans [|x] (nat_lt_suc _)) (nat_lt_suc _)]).
        intros a b eq.
        apply set_type_eq.
        inversion eq.
        exact H0.
Qed.

Lemma f1_ex : ∃ f :
    set_type X * set_type Y +
    set_type Y * set_type X +
    set_type Y * set_type Y →
    set_type Y, bijective f.
Proof.
    pose proof Y_eq2 as H.
    unfold plus, mult in H; equiv_simpl in H.
    exact H.
Qed.

Definition f1 := ex_val f1_ex.
Lemma f1_bij : bijective f1.
Proof.
    apply (ex_proof f1_ex).
Qed.

Local Open Scope set_scope.

Definition f_domain := X ∪ Y.

Definition f' (a b : set_type f_domain) :=
    match (or_to_strong _ _ [|a]), (or_to_strong _ _ [|b]) with
    | strong_or_left Xa, strong_or_left Xb => fs_f f⟨[[a|] | Xa], [[b|] | Xb]⟩
    | strong_or_left Xa, strong_or_right Yb => [f1 (inl (inl ([[a|] | Xa], [[b|] | Yb])))|]
    | strong_or_right Ya, strong_or_left Xb => [f1 (inl (inr ([[a|] | Ya], [[b|] | Xb])))|]
    | strong_or_right Ya, strong_or_right Yb => [f1 (inr ([[a|] | Ya], [[b|] | Yb]))|]
    end.

Lemma XY_not : ∀ a, X a → ¬ Y a.
Proof.
    intros a Xa Ya.
    destruct Ya as [c c_eq].
    pose proof [|f0 c] as H.
    rewrite c_eq in H.
    contradiction.
Qed.

Lemma f'_range : ∀ a b, f_domain (f' a b).
Proof.
    intros [a [Xa|Ya]] [b [Xb|Yb]].
    -   left.
        unfold f'; cbn.
        destruct (or_to_strong _ _ _) as [Xa'|Ya].
        1: destruct (or_to_strong _ _ _) as [Xb'|Yb].
        +   apply (fs_range f).
        +   contradiction (XY_not _ Xb Yb).
        +   contradiction (XY_not _ Xa Ya).
    -   right.
        unfold f'; cbn.
        destruct (or_to_strong _ _ _) as [Xa'|Ya].
        1: destruct (or_to_strong _ _ _) as [Xb|Yb'].
        +   contradiction (XY_not _ Xb Yb).
        +   apply [|f1 (inl (inl ([a|Xa'], [b|Yb'])))].
        +   contradiction (XY_not _ Xa Ya).
    -   right.
        unfold f'; cbn.
        destruct (or_to_strong _ _ _) as [Xa|Ya'].
        2: destruct (or_to_strong _ _ _) as [Xb'|Yb].
        +   contradiction (XY_not _ Xa Ya).
        +   apply [|f1 (inl (inr ([a|Ya'], [b|Xb'])))].
        +   contradiction (XY_not _ Xb Yb).
    -   right.
        unfold f'; cbn.
        destruct (or_to_strong _ _ _) as [Xa|Ya'].
        2: destruct (or_to_strong _ _ _) as [Xb|Yb'].
        +   contradiction (XY_not _ Xa Ya).
        +   contradiction (XY_not _ Xb Yb).
        +   apply [|f1 (inr ([a|Ya'], [b|Yb']))].
Qed.
Lemma f'_inj : ∀ a b c d, f' a b = f' c d → a = c ∧ b = d.
Proof.
    intros [a a_in] [b b_in] [c c_in] [d d_in] eq.
    unfold f' in eq; cbn in eq.
    destruct (or_to_strong _ _ _) as [Xa|Ya].
    all: destruct (or_to_strong _ _ b_in) as [Xb|Yb].
    all: destruct (or_to_strong _ _ c_in) as [Xc|Yc].
    all: destruct (or_to_strong _ _ d_in) as [Xd|Yd].
    -   apply (fs_inj f) in eq.
        destruct eq as [eq1 eq2].
        inversion eq1; inversion eq2.
        split; apply set_type_eq; assumption.
    -   pose proof (fs_range f [a|Xa] [b|Xb]) as Xf.
        rewrite eq in Xf.
        apply XY_not in Xf.
        pose proof [|f1 (inl (inl ([c|Xc], [d|Yd])))].
        contradiction.
    -   pose proof (fs_range f [a|Xa] [b|Xb]) as Xf.
        rewrite eq in Xf.
        apply XY_not in Xf.
        pose proof [|f1 (inl (inr ([c|Yc], [d|Xd])))].
        contradiction.
    -   pose proof (fs_range f [a|Xa] [b|Xb]) as Xf.
        rewrite eq in Xf.
        apply XY_not in Xf.
        pose proof [|f1 (inr ([c|Yc], [d|Yd]))].
        contradiction.
    -   pose proof (fs_range f [c|Xc] [d|Xd]) as Xf.
        rewrite <- eq in Xf.
        apply XY_not in Xf.
        pose proof [|f1 (inl (inl ([a|Xa], [b|Yb])))].
        contradiction.
    -   apply set_type_eq in eq; apply (land f1_bij) in eq.
        inversion eq.
        subst.
        split; apply set_type_eq; reflexivity.
    -   apply set_type_eq in eq; apply (land f1_bij) in eq.
        inversion eq.
    -   apply set_type_eq in eq; apply (land f1_bij) in eq.
        inversion eq.
    -   pose proof (fs_range f [c|Xc] [d|Xd]) as Xf.
        rewrite <- eq in Xf.
        apply XY_not in Xf.
        pose proof [|f1 (inl (inr ([a|Ya], [b|Xb])))].
        contradiction.
    -   apply set_type_eq in eq; apply (land f1_bij) in eq.
        inversion eq.
    -   apply set_type_eq in eq; apply (land f1_bij) in eq.
        inversion eq.
        subst.
        split; apply set_type_eq; reflexivity.
    -   apply set_type_eq in eq; apply (land f1_bij) in eq.
        inversion eq.
    -   pose proof (fs_range f [c|Xc] [d|Xd]) as Xf.
        rewrite <- eq in Xf.
        apply XY_not in Xf.
        pose proof [|f1 (inr ([a|Ya], [b|Yb]))].
        contradiction.
    -   apply set_type_eq in eq; apply (land f1_bij) in eq.
        inversion eq.
    -   apply set_type_eq in eq; apply (land f1_bij) in eq.
        inversion eq.
    -   apply set_type_eq in eq; apply (land f1_bij) in eq.
        inversion eq.
        subst.
        split; apply set_type_eq; reflexivity.
Qed.
Lemma f'_sur : ∀ c, f_domain c → ∃ a b, f' a b = c.
Proof.
    intros c [Xc|Yc].
    -   pose proof (fs_sur f c Xc) as [[a Xa] [[b Xb] eq]].
        exists [a|make_lor Xa], [b|make_lor Xb].
        unfold f'; cbn.
        destruct (or_to_strong _ _ _) as [Xa'|Ya].
        1: destruct (or_to_strong _ _ _) as [Xb'|Yb].
        +   rewrite (proof_irrelevance Xa' Xa).
            rewrite (proof_irrelevance Xb' Xb).
            exact eq.
        +   clear eq.
            apply XY_not in Xb.
            contradiction.
        +   clear eq.
            apply XY_not in Xa.
            contradiction.
    -   pose proof (rand f1_bij [c|Yc])
            as [[[[[a Xa] [b Yb]] | [[a Ya] [b Xb]]] | [[a Ya] [b Yb]]] eq].
        +   exists [a|make_lor Xa], [b|make_ror Yb].
            unfold f'; cbn.
            destruct (or_to_strong _ _ _) as [Xa'|Ya].
            1: destruct (or_to_strong _ _ _) as [Xb|Yb'].
            *   exfalso; apply XY_not in Xb.
                contradiction.
            *   rewrite (proof_irrelevance Xa' Xa).
                rewrite (proof_irrelevance Yb' Yb).
                rewrite eq.
                reflexivity.
            *   clear eq; apply XY_not in Xa.
                contradiction.
        +   exists [a|make_ror Ya], [b|make_lor Xb].
            unfold f'; cbn.
            destruct (or_to_strong _ _ _) as [Xa|Ya'].
            2: destruct (or_to_strong _ _ _) as [Xb'|Yb].
            *   contradiction (XY_not _ Xa Ya).
            *   rewrite (proof_irrelevance Ya' Ya).
                rewrite (proof_irrelevance Xb' Xb).
                rewrite eq.
                reflexivity.
            *   contradiction (XY_not _ Xb Yb).
        +   exists [a|make_ror Ya], [b|make_ror Yb].
            unfold f'; cbn.
            destruct (or_to_strong _ _ _) as [Xa|Ya'].
            2: destruct (or_to_strong _ _ _) as [Xb|Yb'].
            *   contradiction (XY_not _ Xa Ya).
            *   contradiction (XY_not _ Xb Yb).
            *   rewrite (proof_irrelevance Ya' Ya).
                rewrite (proof_irrelevance Yb' Yb).
                rewrite eq.
                reflexivity.
Qed.

Lemma con : False.
Proof.
    pose (g := make_fs
        (make_bin_set_function f_domain f')
        f'_range
        f'_inj
        f'_sur
    ).
    apply (f_max g).
    split.
    -   unfold le; cbn.
        unfold fs_le.
        assert (bin_domain (fs_f f) ⊆ bin_domain (fs_f g)) as sub.
        {
            intros x fx.
            unfold g; cbn.
            left.
            exact fx.
        }
        exists sub.
        intros [a Xa] [b Xb]; cbn.
        unfold f'; cbn.
        destruct (or_to_strong _ _ _) as [Xa'|Ya].
        1: destruct (or_to_strong _ _ _) as [Xb'|Yb].
        +   rewrite (proof_irrelevance Xa Xa').
            rewrite (proof_irrelevance Xb Xb').
            reflexivity.
        +   destruct Yb as [c c_eq].
            pose proof [|f0 c] as X'b.
            rewrite c_eq in X'b.
            contradiction.
        +   destruct Ya as [c c_eq].
            pose proof [|f0 c] as X'a.
            rewrite c_eq in X'a.
            contradiction.
    -   intro eq.
        assert (bin_domain (fs_f f) = bin_domain (fs_f g)) as eq2.
        {
            subst g.
            rewrite eq.
            reflexivity.
        }
        destruct X_ex as [a Xa].
        assert (bin_domain (fs_f g) [f0 [a|Xa]|]) as fa_in.
        {
            right.
            exists [a|Xa].
            reflexivity.
        }
        rewrite <- eq2 in fa_in.
        pose proof [|f0 [a|Xa]] as H.
        contradiction.
Qed.

End Contr.

Lemma X_card : |set_type X| = |A|.
Proof.
    classic_contradiction contr.
    apply con.
    exact contr.
Qed.

Theorem card_mult_idemp : |A| * |A| = |A|.
Proof.
    rewrite <- X_card.
    apply X_mult_idemp.
Qed.

End CardMultIdemp.
End CardMultIdemp.
(* end hide *)
Theorem card_mult_idemp : ∀ κ, infinite κ → κ * κ = κ.
Proof.
    intros A A_inf.
    equiv_get_value A.
    apply CardMultIdemp.card_mult_idemp.
    exact A_inf.
Qed.

Theorem card_plus_lmax : ∀ κ μ, infinite κ → μ ≤ κ → κ + μ = κ.
Proof.
    intros κ μ κ_inf leq.
    apply antisym.
    -   apply le_lplus with κ in leq.
        apply (trans leq).
        rewrite <- (card_mult_idemp κ κ_inf) at 3.
        rewrite <- (mult_lid κ) at 1 2.
        rewrite <- rdist.
        unfold one; cbn.
        rewrite nat_to_card_plus.
        apply card_le_rmult.
        exact (trans (land (nat_is_finite _)) κ_inf).
    -   pose proof (refl (op := le) κ) as leq2.
        pose proof (card_le_zero μ) as leq3.
        pose proof (le_lrplus leq2 leq3) as leq4.
        rewrite plus_rid in leq4.
        exact leq4.
Qed.

Theorem card_plus_idemp : ∀ κ, infinite κ → κ + κ = κ.
Proof.
    intros κ κ_inf.
    apply (card_plus_lmax _ _ κ_inf).
    apply refl.
Qed.

Theorem card_mult_lmax : ∀ κ μ, infinite κ → 0 ≠ μ → μ ≤ κ → κ * μ = κ.
Proof.
    intros κ μ κ_inf μ_nz leq.
    apply antisym.
    -   rewrite <- (card_mult_idemp _ κ_inf) at 2.
        apply card_le_lmult.
        exact leq.
    -   rewrite <- (mult_rid κ) at 1.
        apply card_le_lmult.
        equiv_get_value μ.
        rename μ into A.
        assert A as x.
        {
            classic_contradiction contr.
            apply μ_nz; clear μ_nz.
            unfold zero; cbn; unfold nat_to_card; equiv_simpl.
            exists (λ x, (False_rect _ (nat_lt_0_false x))).
            split.
            -   intros a b eq.
                contradiction (nat_lt_0_false a).
            -   intros b.
                contradiction (contr b).
        }
        unfold one; cbn.
        unfold le, nat_to_card; equiv_simpl.
        exists (λ a, x).
        intros [a a_lt] [b b_lt] eq.
        apply set_type_eq; cbn.
        apply nat_lt_one_eq in a_lt.
        apply nat_lt_one_eq in b_lt.
        subst.
        reflexivity.
Qed.

Theorem card_plus_max : ∀ κ μ, infinite κ → infinite μ → κ + μ = max κ μ.
Proof.
    intros κ μ κ_inf μ_inf.
    unfold max; case_if.
    -   rewrite plus_comm.
        apply card_plus_lmax; assumption.
    -   rewrite nle_lt in n.
        destruct n.
        apply card_plus_lmax; assumption.
Qed.

Theorem card_mult_max : ∀ κ μ, infinite κ → infinite μ → κ * μ = max κ μ.
Proof.
    intros κ μ κ_inf μ_inf.
    unfold max; case_if.
    -   rewrite mult_comm.
        apply card_mult_lmax; try assumption.
        intro contr; subst.
        unfold infinite in κ_inf.
        pose proof (le_lt_trans κ_inf (nat_is_finite _)) as [C0 C1].
        contradiction.
    -   rewrite nle_lt in n.
        destruct n as [leq neq].
        apply card_mult_lmax; try assumption.
        intro contr; subst.
        unfold infinite in μ_inf.
        pose proof (le_lt_trans μ_inf (nat_is_finite _)) as [C0 C1].
        contradiction.
Qed.

Theorem card_inf_plus_mult : ∀ κ μ, infinite κ → infinite μ → κ + μ = κ * μ.
Proof.
    intros κ μ κ_inf μ_inf.
    rewrite card_plus_max by assumption.
    rewrite card_mult_max by assumption.
    reflexivity.
Qed.
(* begin hide *)
Close Scope card_scope.
(* end hide *)
