Require Import init.

Require Import zorn.
Require Import zorn_set.
Require Import set.

Section WellOrderingTheorem.

Context {U : Type}.

Local Existing Instance subset_order.
Local Open Scope set_scope.

Definition wo_conforming (W : (U → Prop) → Prop) :=
    (∀ x : U, (⋃ W) x → ∃ S : U → Prop, S x ∧ W S ∧ W (S - ❴x❵)) ∧
    well_orders le W.

Lemma wo_conforming_init : ∀ AA BB, wo_conforming AA → wo_conforming BB → AA ⊆ BB →
    ∀ A B, AA A → BB B → ¬AA B → A ⊆ B.
Proof.
    intros AA BB [AA_remove AA_wo] [BB_remove BB_wo] sub.
    intros A B AA_A BB_B AA_B.
    classic_case (B = A) as [eq|neq].
    1: subst; apply refl.
    destruct (well_orders_chain _ BB_wo A B (sub A AA_A) BB_B) as [leq|leq].
    1: exact leq.
    exfalso.
    assert (B ⊂ A) as ltq by (split; assumption).
    clear neq leq.
    pose proof (AA_wo (λ X, AA X ∧ B ⊂ X)) as C_ex.
    prove_parts C_ex.
    1: apply inter_lsub.
    1: exists A; split; assumption.
    clear A AA_A ltq.
    destruct C_ex as [C [[AA_C BC] C_least]].
    pose proof (strict_subset_ex _ _ BC) as [x [Bx Cx]].
    pose proof (AA_remove x (ex_intro _ _ (make_and AA_C Cx)))
        as [D [Dx [AA_D AA_Dx]]].
    assert (B ⊂ (D - ❴x❵)) as BD.
    {
        split; [>|intro; subst; contradiction].
        assert (B ⊆ D → B ⊆ (D - ❴x❵)) as sub'.
        {
            intros sub' a Ba.
            split.
            -   exact (sub' a Ba).
            -   intros contr.
                rewrite singleton_eq in contr.
                subst a; contradiction.
        }
        apply sub'.
        apply sub in AA_D.
        pose proof (well_orders_chain _ BB_wo _ _ BB_B AA_D) as [leq|leq].
        -   exact leq.
        -   apply leq in Dx.
            contradiction.
    }
    specialize (C_least _ (make_and AA_Dx BD)).
    apply C_least in Cx.
    destruct Cx as [Dx' neq].
    contradiction neq.
    reflexivity.
Qed.

Lemma well_order_chain_union : ∀ F : set_type wo_conforming → Prop,
    is_chain le F → wo_conforming (⋃ (image_under (λ S, [S|]) F)).
Proof.
    intros F F_chain.
    split.
    -   intros x [A [A_in Ax]].
        destruct A_in as [AA' [[[AA AA_wo] [F_AA AA_eq]] AA_A]]; subst AA'.
        pose proof AA_wo as [AA_init AA_wo'].
        pose proof (AA_init x (ex_intro _ A (make_and AA_A Ax)))
            as [B [Bx [AA_B AA_Bx]]].
        exists B.
        split; [>exact Bx|].
        split.
        +   exists AA.
            split; [>|exact AA_B].
            exists [AA|AA_wo].
            split; trivial.
        +   exists AA.
            split; [>|exact AA_Bx].
            exists [AA|AA_wo].
            split; trivial.
    -   intros AA AA_sub [A AA_A].
        pose proof (AA_sub A AA_A) as [BB' [[[BB BB_wo] [F_BB BB_eq]] BB_A]]; subst.
        cbn in BB_A.
        pose proof (rand BB_wo (AA ∩ BB) (inter_rsub _ _)
            (ex_intro _ A (make_and AA_A BB_A))) as [M [[AA_M BB_M] M_least]].
        exists M.
        split; [>exact AA_M|].
        intros Y AA_Y.
        pose proof (AA_sub Y AA_Y) as [CC' [[[CC CC_wo] [F_CC CC_eq]] CC_A]]; subst.
        cbn in CC_A.
        specialize (F_chain _ _ F_BB F_CC).
        unfold le in F_chain; cbn in F_chain.
        destruct F_chain as [leq|leq].
        2: apply leq in CC_A; apply M_least; split; assumption.
        classic_case (BB Y) as [BB_Y|nBB_Y].
        1: apply M_least; split; assumption.
        clear AA AA_sub A AA_A BB_A AA_M M_least AA_Y.
        apply (wo_conforming_init BB CC); assumption.
Qed.

Lemma well_order_sets_ex :
    ∃ W : set_type wo_conforming, ∀ A : set_type wo_conforming, ¬([W|] < [A|]).
Proof.
    apply set_zorn.
    intros F F_chain.
    apply well_order_chain_union.
    exact F_chain.
Qed.

Definition well_order_sets := [ex_val well_order_sets_ex|].
Definition well_order_sets_wo := [|ex_val well_order_sets_ex]
    : wo_conforming well_order_sets.
Lemma well_order_sets_max : ∀ A, ¬([well_order_sets|well_order_sets_wo] < A).
Proof.
    intros A.
    pose proof (ex_proof well_order_sets_ex A) as ltq.
    unfold well_order_sets, well_order_sets_wo.
    change (ex_type_val (ex_to_type well_order_sets_ex)) with
        (ex_val well_order_sets_ex) in ltq.
    rewrite_ex_val W W_max.
    replace [[W|] | [|W]] with W by (apply set_type_eq; reflexivity).
    rewrite set_type_lt in ltq.
    exact ltq.
Qed.

Lemma wo_conforming_add : ∀ S T, wo_conforming S →
    (∃ X, T - ❴X❵ = S ∧ ⋃S ⊆ X ∧ ∀ x, X x → ¬(⋃S) x → S (X - ❴x❵)) →
    wo_conforming T.
Proof.
    intros SS TT SS_conf [X [X_eq [X_sub X_in]]].
    assert (SS ⊆ TT) as sub.
    {
        intros x Sx.
        rewrite <- X_eq in Sx.
        apply Sx.
    }
    split.
    -   intros x [A [TT_A Ax]].
        classic_case ((⋃ SS) x) as [x_ex|x_nex].
        +   destruct x_ex as [B [SS_B Bx]].
            pose proof (land SS_conf x (ex_intro _ _ (make_and SS_B Bx)))
                as [S [Sx [SS_S SS_Sx]]].
            exists S.
            apply sub in SS_S, SS_Sx.
            repeat split; assumption.
        +   assert (A = X) as eq.
            {
                rewrite not_ex in x_nex.
                specialize (x_nex A).
                rewrite and_comm, not_and_impl in x_nex.
                apply x_nex in Ax.
                rewrite <- X_eq in Ax.
                unfold set_minus in Ax.
                rewrite not_and_impl, not_not in Ax.
                symmetry; apply Ax.
                exact TT_A.
            }
            subst A.
            exists X.
            split; [>exact Ax|].
            split; [>exact TT_A|].
            apply sub.
            apply X_in; assumption.
    -   intros AA AA_sub [A AA_A].
        classic_case (∃ Y, AA Y ∧ SS Y) as [Y_ex|Y_nex].
        +   destruct Y_ex as [Y [AA_Y SS_Y]].
            pose proof (rand SS_conf (AA ∩ SS)
                (inter_rsub _ _) (ex_intro _ _ (make_and AA_Y SS_Y)))
                as [a [[AA_a SS_a] a_least]].
            exists a.
            split; [>exact AA_a|].
            intros y AA_y.
            classic_case (SS y) as [SS_y|SS_y].
            *   apply a_least.
                split; assumption.
            *   apply AA_sub in AA_y.
                rewrite <- X_eq in SS_y.
                unfold set_minus in SS_y.
                rewrite not_and_impl, not_not in SS_y.
                apply SS_y in AA_y.
                rewrite singleton_eq in AA_y.
                subst y.
                intros s sa.
                apply X_sub.
                exists a.
                split; assumption.
        +   exists X.
            assert (∀ Z, AA Z → Z = X) as Z_eq.
            {
                intros Z SZ.
                rewrite not_ex in Y_nex.
                specialize (Y_nex Z).
                rewrite not_and_impl in Y_nex.
                specialize (Y_nex SZ).
                rewrite <- X_eq in Y_nex.
                unfold set_minus in Y_nex.
                rewrite not_and_impl, not_not in Y_nex.
                apply AA_sub in SZ.
                apply Y_nex in SZ.
                symmetry; exact SZ.
            }
            rewrite (Z_eq _ AA_A) in AA_A.
            split; [>exact AA_A|].
            intros y AA_y.
            rewrite (Z_eq _ AA_y).
            apply refl.
Qed.

Lemma well_order_sets_union : well_order_sets (⋃ well_order_sets).
Proof.
    classic_contradiction contr.
    pose (A := well_order_sets ∪ ❴⋃ well_order_sets❵).
    assert (wo_conforming A) as A_wo.
    {
        apply (wo_conforming_add well_order_sets).
        -   apply well_order_sets_wo.
        -   exists (⋃ well_order_sets).
            unfold A.
            split; [>|split].
            +   apply union_minus.
                apply empty_eq.
                intros x [x_in1 x_in2].
                apply contr.
                rewrite singleton_eq in x_in2; subst x.
                exact x_in1.
            +   apply refl.
            +   intros x x_in x_nin.
                contradiction.
    }
    apply (well_order_sets_max [A|A_wo]).
    split.
    -   intros a a_wo.
        left.
        exact a_wo.
    -   intros eq.
        rewrite set_type_eq2 in eq.
        apply contr.
        rewrite eq.
        right.
        rewrite eq.
        reflexivity.
Qed.

Definition well_order_set_base (x : U) := λ S, S x ∧ well_order_sets S.

Lemma well_order_set_sub : ∀ x, well_order_set_base x ⊆ well_order_sets.
Proof.
    intros x S [Sx S_in].
    exact S_in.
Qed.

Lemma well_order_set_ex : ∀ x : U, ∃ S, well_order_set_base x S.
Proof.
    intros x.
    classic_contradiction contr.
    pose (A := well_order_sets ∪ ❴⋃ well_order_sets ∪ ❴x❵❵).
    assert (wo_conforming A) as A_wo.
    {
        apply (wo_conforming_add well_order_sets).
        -   exact well_order_sets_wo.
        -   exists (⋃ well_order_sets ∪ ❴x❵).
            unfold A.
            split; [>|split].
            +   apply union_minus.
                apply empty_eq.
                intros a [a_in1 a_in2].
                rewrite singleton_eq in a_in2; subst a.
                apply contr.
                exists (⋃ well_order_sets ∪ ❴x❵).
                split; [>|exact a_in1].
                right; reflexivity.
            +   apply union_lsub.
            +   intros a a_in a_nin.
                destruct a_in as [a_in|a_eq]; [>contradiction|].
                rewrite singleton_eq in a_eq; subst a.
                rewrite union_minus; [>apply well_order_sets_union|].
                apply empty_eq.
                intros a [a_in1 a_in2].
                rewrite singleton_eq in a_in2; subst a.
                contradiction.
    }
    apply (well_order_sets_max [A|A_wo]).
    split.
    -   intros a a_wo.
        left.
        exact a_wo.
    -   intros eq.
        rewrite set_type_eq2 in eq.
        apply contr.
        exists (⋃well_order_sets ∪ ❴x❵).
        split.
        +   right; reflexivity.
        +   rewrite eq.
            right.
            rewrite eq.
            reflexivity.
Qed.

Definition well_order_set (x : U) := ex_val (rand well_order_sets_wo
    (well_order_set_base x) (well_order_set_sub x) (well_order_set_ex x)).
Lemma well_order_set_in : ∀ x, well_order_set x x.
Proof.
    intros x.
    unfold well_order_set.
    rewrite_ex_val S [H H'].
    apply H.
Qed.
Lemma well_order_set_wo : ∀ x, well_order_sets (well_order_set x).
Proof.
    intros x.
    unfold well_order_set.
    rewrite_ex_val S [H H'].
    apply H.
Qed.
Lemma well_order_set_min : ∀ x,
    ∀ S, well_order_set_base x S → well_order_set x ⊆ S.
Proof.
    intros x S Sx.
    unfold well_order_set.
    unfold ex_val.
    destruct (ex_to_type _) as [T [H H']]; cbn.
    apply H'.
    exact Sx.
Qed.

Lemma well_order_set_minus : ∀ a, well_order_sets (well_order_set a - ❴a❵).
Proof.
    intros a.
    pose proof (well_order_set_wo a) as a_wo.
    pose proof (well_order_set_in a) as a_in.
    pose proof (well_order_sets_wo) as [init wo].
    specialize (init a (ex_intro _ _ (make_and a_wo a_in)))
        as [S [Sa [S_wo Sa_wo]]].
    applys_eq Sa_wo.
    apply f_equal2; [>|reflexivity].
    pose proof (well_order_set_min a) as a_min.
    apply antisym; [>apply a_min; split; assumption|].
    intros x Sx.
    pose proof (well_orders_chain _ (rand well_order_sets_wo)) as chain.
    specialize (chain _ _ Sa_wo (well_order_set_wo a)) as [leq|leq].
    -   classic_case (a = x) as [eq|neq].
        1: subst; apply well_order_set_in.
        apply leq.
        split; assumption.
    -   specialize (leq a (well_order_set_in a)).
        destruct leq as [Sa' contr].
        contradiction contr; reflexivity.
Qed.

Local Instance wo_le : Order U := {
    le a b := well_order_set a ⊆ well_order_set b
}.

Local Instance wo_antisym : Antisymmetric le.
Proof.
    split.
    unfold le; cbn.
    intros a b ab_sub ba_sub.
    pose proof (antisym ab_sub ba_sub) as set_eq.
    classic_contradiction contr.
    pose proof (well_order_set_minus a) as a'_in.
    assert ((well_order_set a - ❴a❵) b) as b_in'.
    {
        split.
        -   rewrite set_eq.
            apply well_order_set_in.
        -   exact contr.
    }
    pose proof (well_order_set_min b (well_order_set a - ❴a❵)) as sub.
    prove_parts sub; [>split; assumption|].
    pose proof (well_order_set_in a) as a_in.
    rewrite set_eq in a_in.
    apply sub in a_in.
    apply a_in.
    reflexivity.
Qed.

Local Instance wo_wo : WellOrdered le.
Proof.
    split.
    intros S S_ex.
    pose (S' := image_under well_order_set S).
    pose proof (rand well_order_sets_wo S') as A_ex.
    prove_parts A_ex.
    {
        intros X [x [Sx x_eq]]; subst X.
        apply well_order_set_wo.
    }
    {
        destruct S_ex as [x Sx].
        exists (well_order_set x).
        exists x.
        split; trivial.
    }
    destruct A_ex as [A [[a [Sa A_eq]] A_min]]; subst A.
    exists a.
    split; [>exact Sa|].
    intros y Sy.
    apply A_min.
    exists y.
    split; trivial.
Qed.

End WellOrderingTheorem.
