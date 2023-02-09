Require Import init.

Require Export topology_base.
Require Export topology_axioms.
Require Export topology_subspace.
Require Export topology_limit.

(* begin hide *)
Open Scope card_scope.
Open Scope set_scope.
(* end hide *)
Definition open_covering_of {U} `{Topology U} SS X :=
    X ⊆ ⋃ SS ∧ ∀ S, SS S → open S.
Definition open_covering {U} `{Topology U} SS := open_covering_of SS all.
Definition compact U `{Topology U} := ∀ SS, open_covering SS →
    ∃ SS', SS' ⊆ SS ∧ finite (|set_type SS'|) ∧ (∀ x, (⋃ SS') x).

Definition limit_point_compact U `{Topology U} :=
    ∀ S, infinite (|set_type S|) → ∃ x, limit_point S x.

Definition sequentially_compact U `{Topology U} :=
    ∀ a, ∃ b, subsequence a b ∧ seq_converges b.

(* begin hide *)
Section Compact.

Context {U} `{Topology U}.
Existing Instance subspace_topology.
(* end hide *)
Theorem compact_subspace : ∀ X, compact (set_type X) ↔
    ∀ SS, open_covering_of SS X →
        ∃ SS', SS' ⊆ SS ∧ finite (|set_type SS'|) ∧ X ⊆ ⋃ SS'.
Proof.
    intros X.
    split.
    -   intros X_compact SS [X_sub SS_open].
        pose (XSS S := ∃ S', to_set_type X S' = S ∧ SS S').
        assert (open_covering XSS) as XSS_cover.
        {
            split.
            -   intros [x Xx] C0; clear C0.
                specialize (X_sub x Xx) as [S [SS_S Sx]].
                exists (to_set_type X S).
                split.
                +   exists S.
                    split; trivial.
                +   exact Sx.
            -   intros XS [S [S_eq SS_S]].
                subst XS.
                exists S.
                split; try reflexivity.
                apply SS_open.
                exact SS_S.
        }
        specialize (X_compact XSS XSS_cover)
            as [XSS' [XSS'_sub [XSS'_fin XSS'_cover]]].
        assert (∀ XS, XSS' XS → ∃ S, to_set_type X S = XS ∧ SS S) as from_X.
        {
            intros XS XSS'XS.
            apply XSS'_sub in XSS'XS.
            exact XSS'XS.
        }
        pose (SS' S := ∃ XS, S = ex_val (from_X [XS|] [|XS])).
        exists SS'.
        split.
        2: split.
        +   intros S [[XS XS_in] S_eq].
            subst S.
            rewrite_ex_val S S_eq.
            destruct S_eq as [XS_eq SS_S].
            exact SS_S.
        +   apply (le_lt_trans2 XSS'_fin).
            unfold le; equiv_simpl.
            exists (λ S : set_type SS', ex_val [|S]).
            split.
            intros [S1 SS'_S1] [S2 SS'_S2] eq.
            apply set_type_eq; cbn in *.
            rewrite_ex_val XS1 XS1_eq.
            rewrite_ex_val_with SS'_S2 XS2 XS2_eq.
            subst.
            reflexivity.
        +   intros x Xx.
            specialize (XSS'_cover [x|Xx]) as [XA [XSS'A Ax]].
            exists (ex_val (from_X XA XSS'A)).
            split.
            *   exists [XA|XSS'A].
                reflexivity.
            *   rewrite_ex_val A A_eq.
                destruct A_eq as [A_eq SS_A].
                subst XA.
                exact Ax.
    -   intros X_compact XSS [XSS_sub XSS_open].
        assert (∀ XS, XSS XS → ∃ S, to_set_type X S = XS ∧ open S) as SS_ex.
        {
            intros XS XSS_XS.
            apply XSS_open in XSS_XS.
            destruct XSS_XS as [S [S_open XS_eq]].
            subst XS.
            exists S.
            split; trivial.
        }
        pose (SS S := ∃ XS, S = ex_val (SS_ex [XS|] [|XS])).
        assert (open_covering_of SS X) as SS_cover.
        {
            split.
            -   intros x Xx.
                specialize (XSS_sub [x|Xx] true) as [XS [XSS_XS XSx]].
                exists (ex_val (SS_ex XS XSS_XS)).
                split.
                +   exists [XS|XSS_XS].
                    reflexivity.
                +   rewrite_ex_val S S_eq.
                    destruct S_eq as [S_eq S_open].
                    subst XS.
                    exact XSx.
            -   intros S [XS S_eq].
                subst S.
                rewrite_ex_val S S_eq.
                apply S_eq.
        }
        specialize (X_compact SS SS_cover) as [SS' [SS'_sub [SS'_fin sub_SS']]].
        pose (XSS' S := ∃ S', to_set_type X S' = S ∧ SS' S').
        exists XSS'.
        split.
        2: split.
        +   intros XS [S [S_eq SS'_S]].
            subst XS.
            apply SS'_sub in SS'_S.
            destruct SS'_S as [XS S_eq].
            subst S.
            rewrite_ex_val S S_eq.
            destruct S_eq as [S_eq S_open].
            rewrite S_eq.
            exact [|XS].
        +   apply (le_lt_trans2 SS'_fin).
            unfold le; equiv_simpl.
            exists (λ XS : set_type XSS',
                [ex_val [|XS] | rand (ex_proof [|XS])]).
            split.
            intros XS1 XS2 eq.
            inversion eq as [eq2]; clear eq.
            rewrite_ex_val S1 [S1_eq SS'_S1].
            rewrite_ex_val S2 [S2_eq SS'_S2].
            subst.
            rewrite S1_eq in S2_eq.
            apply set_type_eq.
            exact S2_eq.
        +   intros [x Xx].
            specialize (sub_SS' x Xx) as [A [SS'A Ax]].
            pose proof SS'A as SS'A2.
            apply SS'_sub in SS'A.
            destruct SS'A as [[XA XA_in] A_eq]; cbn in *.
            subst A.
            rewrite_ex_val A [XA_eq A_open].
            exists XA.
            subst XA.
            split.
            *   exists A.
                split; trivial.
            *   exact Ax.
Qed.

Theorem compact_closed_compact :
    ∀ X, compact U → closed X → compact (set_type X).
Proof.
    intros X U_compact X_closed.
    apply compact_subspace.
    intros XSS [XSS_sub XSS_open].
    pose (USS := XSS ∪ ❴𝐂 X❵).
    assert (open_covering USS) as USS_cover.
    {
        split.
        -   intros x C0; clear C0.
            classic_case (X x) as [Xx|nXx].
            +   specialize (XSS_sub x Xx) as [S [XSS_S Sx]].
                exists S.
                split; try exact Sx.
                left.
                exact XSS_S.
            +   exists (𝐂 X).
                split; try exact nXx.
                right.
                reflexivity.
        -   intros S [XSS_S|nX_S].
            +   apply XSS_open.
                exact XSS_S.
            +   rewrite <- nX_S.
                exact X_closed.
    }
    specialize (U_compact USS USS_cover) as [SS' [SS'_sub [SS'_fin sub_SS']]].
    exists (SS' - ❴𝐂 X❵).
    split.
    2: split.
    -   intros S [SS'_S nX_S].
        apply SS'_sub in SS'_S.
        destruct SS'_S as [XSS_S|contr].
        +   exact XSS_S.
        +   contradiction.
    -   apply (le_lt_trans2 SS'_fin).
        apply card_minus_le.
    -   intros x Xx.
        specialize (sub_SS' x) as [A [SS'_A Ax]].
        exists A.
        repeat split.
        +   exact SS'_A.
        +   intro contr.
            rewrite <- contr in Ax.
            contradiction.
        +   exact Ax.
Qed.

Theorem compact_limit_point_compact : compact U → limit_point_compact U.
Proof.
    intros U_comp A A_inf.
    classic_contradiction no_lim.
    rewrite not_ex in no_lim.
    assert (closed A) as A_closed.
    {
        apply closed_limit_points.
        intros x x_lim.
        contradiction (no_lim x x_lim).
    }
    unfold limit_point in no_lim.
    assert (∀ a, ∃ S, open S ∧ S a ∧ ¬intersects (A - ❴a❵) S)
        as no_lim'.
    {
        intros a.
        specialize (no_lim a).
        rewrite not_all in no_lim.
        destruct no_lim as [S no_lim].
        exists S.
        do 2 rewrite not_impl in no_lim.
        exact no_lim.
    }
    clear no_lim.
    pose (SS S := ∃ a, S = ex_val (no_lim' a)).
    assert (open_covering SS) as SS_cover.
    {
        split.
        -   intros x C0; clear C0.
            exists (ex_val (no_lim' x)).
            split.
            +   exists x.
                reflexivity.
            +   rewrite_ex_val S S_H.
                apply S_H.
        -   intros S [x S_eq].
            subst S.
            rewrite_ex_val S S_H.
            setoid_rewrite not_impl in S_H.
            exact (land S_H).
    }
    specialize (U_comp SS SS_cover) as [SS' [SS'_sub [SS'_fin sub_SS']]].
    assert (finite (|set_type A|)) as A_fin.
    {
        apply (le_lt_trans2 SS'_fin).
        unfold le; equiv_simpl.
        exists (λ x, [ex_val (sub_SS' [x|]) | land (ex_proof (sub_SS' [x|]))]).
        split.
        intros [x Ax] [y Ay] eq.
        apply set_type_eq; cbn.
        rename eq into eq2; inversion eq2 as [eq]; clear eq2.
        rewrite_ex_val S1 [SS'_S1 S1x].
        rewrite_ex_val S2 [SS'_S2 S2y].
        subst.
        clear SS'_S2.
        apply SS'_sub in SS'_S1.
        destruct SS'_S1 as [z S2_eq].
        rewrite_ex_val S S_H.
        subst S2.
        destruct S_H as [S_open [Sz S_inter]].
        unfold intersects in S_inter.
        rewrite not_not in S_inter.
        assert (∀ a, A a → S a → z = a) as z_eq.
        {
            intros a Aa Sa.
            classic_contradiction contr.
            assert (((A - ❴z❵) ∩ S) a) as a_in.
            {
                repeat split; assumption.
            }
            rewrite S_inter in a_in.
            exact a_in.
        }
        rewrite <- (z_eq x Ax S1x).
        rewrite <- (z_eq y Ay S2y).
        reflexivity.
    }
    destruct (le_lt_trans A_inf A_fin); contradiction.
Qed.

Theorem sequentially_limit_point_compact :
    sequentially_compact U → limit_point_compact U.
Proof.
    intros U_comp S S_inf.
    apply infinite_seq_ex in S_inf as [Sf Sf_inj].
    remember (λ n, [Sf n|]) as f.
    assert (∀ n, S (f n)) as f_in.
    {
        intros n.
        rewrite Heqf.
        exact [|Sf n].
    }
    assert (∀ i j, i ≠ j → f i ≠ f j) as f_inj.
    {
        intros i j neq eq.
        specialize (Sf_inj i j neq).
        rewrite Heqf in eq.
        apply set_type_eq in eq.
        contradiction.
    }
    clear Sf Sf_inj Heqf.
    specialize (U_comp f) as [g [g_sub [x g_lim]]].
    destruct g_sub as [ns [ns_lt fg_eq]].
    exists x.
    intros A A_open Ax.
    specialize (g_lim A A_open Ax) as [N all_gt].
    apply empty_neq.
    classic_case (g N = x) as [x_eq|x_neq].
    -   exists (g (nat_suc N)).
        repeat split.
        +   rewrite <- fg_eq.
            apply f_in.
        +   rewrite singleton_eq; intro contr.
            subst x.
            do 2 rewrite <- fg_eq in contr.
            destruct (ns_lt N) as [C0 neq]; clear C0.
            exact (f_inj _ _ neq contr).
        +   apply all_gt.
            apply nat_le_suc.
    -   exists (g N).
        repeat split.
        +   rewrite <- fg_eq.
            apply f_in.
        +   rewrite singleton_eq.
            rewrite neq_sym.
            exact x_neq.
        +   apply all_gt.
            apply refl.
Qed.

(* begin hide *)
End Compact.
(* end hide *)
Section CompactHausdorff.

Context {U} `{HausdorffSpace U}.
Existing Instance subspace_topology.

Theorem hausdorff_compact_disjoint : ∀ Y, compact (set_type Y) → ∀ x, ¬Y x →
    ∃ A B, open A ∧ open B ∧ A ∩ B = ∅ ∧ A x ∧ Y ⊆ B.
Proof.
    intros Y Y_compact x nYx.
    assert (∀ y, Y y → ∃ AB,
        neighborhood x (fst AB) ∧ neighborhood y (snd AB) ∧ fst AB ∩ snd AB = ∅)
        as B_ex.
    {
        intros y Yy.
        assert (x ≠ y) as neq by (intro; subst; contradiction).
        pose proof (hausdorff_space x y neq)
            as [A [B [A_open [B_open [Ax [By AB_dis]]]]]].
        exists (A, B).
        repeat split; assumption.
    }
    pose (AB_full (y : set_type Y) := ex_val (B_ex [y|] [|y])).
    pose (B_full S := ∃ y, S = snd (AB_full y)).
    assert (open_covering_of B_full Y) as B_cover.
    {
        split.
        -   intros y Yy.
            exists (snd (AB_full [y|Yy])).
            split.
            +   exists [y|Yy].
                reflexivity.
            +   unfold AB_full.
                rewrite_ex_val AB AB_H.
                apply AB_H.
        -   intros B [y B_eq].
            subst B.
            unfold AB_full.
            rewrite_ex_val AB AB_H.
            apply AB_H.
    }
    rewrite compact_subspace in Y_compact.
    specialize (Y_compact B_full B_cover) as [B_small [B_sub [B_fin sub_B]]].
    assert (∀ B, B_small B → ∃ A, neighborhood x A ∧ A ∩ B = ∅) as A_ex.
    {
        intros B B_in.
        apply B_sub in B_in.
        destruct B_in as [y B_eq].
        subst B.
        unfold AB_full; cbn.
        rewrite_ex_val AB AB_H.
        destruct AB as [A B]; cbn in *.
        exists A.
        split; apply AB_H.
    }
    pose (A_small A := ∃ B, A = ex_val (A_ex [B|] [|B])).
    exists (⋂ A_small), (⋃ B_small).
    repeat split.
    -   apply inter_open.
        +   intros A [B A_eq].
            subst A.
            rewrite_ex_val A A_H.
            apply A_H.
        +   apply (le_lt_trans2 B_fin).
            unfold le; equiv_simpl.
            exists (λ A : set_type A_small, ex_val [|A]).
            split.
            intros [A1 A_A1] [A2 A_A2] eq.
            rewrite_ex_val [B1 B_B1] B1_eq.
            rewrite_ex_val_with [|[A2|A_A2]] [B2 B_B2] B2_eq.
            cbn in *.
            inversion eq.
            apply set_type_eq; cbn.
            subst.
            rewrite (proof_irrelevance B_B1 B_B2).
            reflexivity.
    -   apply union_open.
        intros B B_B.
        apply B_cover.
        apply B_sub.
        exact B_B.
    -   apply empty_eq.
        intros c [Ac Bc].
        destruct Bc as [B [B_B Bc]].
        pose proof B_B as B_B2.
        apply B_sub in B_B.
        destruct B_B as [y B_eq].
        subst B.
        unfold AB_full in Bc, B_B2.
        rewrite_ex_val AB AB_H.
        destruct AB as [A' B]; cbn in *.
        assert (A_small (ex_val (A_ex B B_B2))) as A_A.
        {
            exists [B|B_B2].
            cbn.
            reflexivity.
        }
        rewrite_ex_val A [A_neigh AB_dis].
        specialize (Ac A A_A) as Ac.
        assert (∅ c) as contr.
        {
            rewrite <- AB_dis.
            split; assumption.
        }
        exact contr.
    -   intros A [B A_eq].
        subst A.
        rewrite_ex_val A A_H.
        apply A_H.
    -   exact sub_B.
Qed.

Theorem hausdorff_compact_closed : ∀ X, compact (set_type X) → closed X.
Proof.
    intros X X_compact.
    unfold closed.
    apply open_all_neigh.
    intros x nXx.
    pose proof (hausdorff_compact_disjoint X X_compact x nXx)
        as [A [B [A_open [B_open [AB_dis [Ax B_sub]]]]]].
    exists A.
    repeat split.
    -   exact A_open.
    -   exact Ax.
    -   intros y Ay Xy.
        apply B_sub in Xy.
        assert (∅ y) as contr.
        {
            rewrite <- AB_dis.
            split; assumption.
        }
        exact contr.
Qed.

End CompactHausdorff.
(* begin hide *)
Close Scope set_scope.
Close Scope card_scope.
(* end hide *)
