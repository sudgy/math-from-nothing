Require Import init.

Require Export card_base.
Require Import card_order.
Require Import card_plus.
Require Import card_mult.
Require Import card_infinite1.
Require Import card_nat0.
Require Import nat0.
Require Import set.
Require Import well_order.

(* begin hide *)
Open Scope card_scope.

Section InfiniteOrder.

Context {U : Type} {op : U → U → Prop}.
Context `{Reflexive U op, Antisymmetric U op, Transitive U op}.

Section Proof.

Variable x : U.
Hypothesis all_greater : ∀ a, ∃ b, strict op a b.

Fixpoint create_greater n :=
    match n with
    | nat0_zero => x
    | nat0_suc n' => ex_val (all_greater (create_greater n'))
    end.

Lemma create_greater_suc :
        ∀ n, strict op (create_greater n) (create_greater (nat0_suc n)).
    intros n; cbn.
    rewrite_ex_val n' n'_eq.
    exact n'_eq.
Qed.

Lemma create_greater_zero : ∀ n, op x (create_greater n).
    nat0_induction n.
    -   apply refl.
    -   apply (trans IHn).
        apply create_greater_suc.
Qed.
Lemma create_greater_zero_suc :
        ∀ n, strict op x (create_greater (nat0_suc n)).
    nat0_induction n.
    -   unfold one; cbn.
        rewrite_ex_val x' x'_eq.
        exact x'_eq.
    -   cbn in *.
        rewrite_ex_val x' x'_eq.
        exact (trans IHn x'_eq).
Qed.

Lemma create_greater_lt :
        ∀ a b, a < b → strict op (create_greater a) (create_greater b).
    intros a b ltq.
    apply nat0_lt_ex in ltq as [c [c_nz c_eq]].
    subst b.
    nat0_destruct c; try contradiction.
    clear c_nz.
    nat0_induction c.
    -   rewrite plus_comm.
        unfold one, plus; cbn.
        apply create_greater_suc.
    -   apply (trans IHc).
        rewrite (nat0_plus_rsuc a (nat0_suc c)).
        apply create_greater_suc.
Qed.

Theorem all_greater_inf_base : infinite (|U|).
    unfold infinite, le; equiv_simpl.
    exists create_greater.
    intros a.
    nat0_induction a; intros b eq.
    -   nat0_destruct b; try reflexivity.
        pose proof (create_greater_zero_suc b) as [leq neq].
        contradiction.
    -   nat0_destruct b.
        +   symmetry in eq.
            pose proof (create_greater_zero_suc a) as [leq neq].
            contradiction.
        +   apply f_equal.
            apply IHa.
            destruct (trichotomy a b) as [[leq|eq']|leq].
            *   rewrite <- nat0_sucs_lt in leq.
                apply create_greater_lt in leq.
                destruct leq; contradiction.
            *   rewrite eq'; reflexivity.
            *   symmetry in eq.
                rewrite <- nat0_sucs_lt in leq.
                apply create_greater_lt in leq.
                destruct leq; contradiction.
Qed.

End Proof.
(* end hide *)
Theorem all_greater_inf : U → (∀ a, ∃ b, strict op a b) → infinite (|U|).
    apply all_greater_inf_base.
Qed.

(* begin hide *)
End InfiniteOrder.

Section InfiniteOrder2.

Context {U : Type} {op : U → U → Prop}.
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op,
    Connex U op
}.
(* end hide *)
Theorem all_greater_inf_set : ∀ S : U → Prop,
        (∃ x, S x) → (∀ a : set_type S, ∃ b : set_type S, strict op [a|] [b|]) →
        infinite (|set_type S|).
    intros S S_ex a_gt.
    pose (op' (a b : set_type S) := op [a|] [b|]).
    assert (Antisymmetric op').
    {
        split.
        intros a b ab ba.
        apply set_type_eq.
        apply (antisym (op := op)); assumption.
    }
    assert (Transitive op').
    {
        split.
        intros a b c ab bc.
        unfold op' in *.
        exact (trans ab bc).
    }
    apply (all_greater_inf (op := op')).
    -   apply ex_to_type in S_ex; destruct S_ex as [x Sx].
        split with x.
        exact Sx.
    -   intros a.
        specialize (a_gt a) as [b b_eq].
        exists b.
        split; try apply b_eq.
        intro contr; subst.
        destruct b_eq; contradiction.
Qed.

Theorem finite_well_founded_max :
        finite (|U|) → ∀ S : U → Prop, (∃ x, S x) → ∃ x, is_maximal op S x.
    intros U_fin S S_ex.
    classic_contradiction contr.
    rewrite not_ex in contr.
    unfold is_minimal in contr.
    setoid_rewrite not_and in contr.
    setoid_rewrite not_all in contr.
    pose proof (le_lt_trans (card_sub_le _ S) U_fin) as S_fin.
    unfold finite in S_fin.
    rewrite <- nle_lt in S_fin.
    apply S_fin.
    apply all_greater_inf_set; try exact S_ex.
    intros [a Sa].
    specialize (contr a) as [contr|contr]; try contradiction.
    destruct contr as [b contr].
    do 2 rewrite not_impl in contr.
    rewrite not_not in contr.
    destruct contr as [Sb [neq leq]].
    exists [b|Sb].
    cbn.
    rewrite neq_sym in neq.
    split; assumption.
Qed.

Theorem finite_well_ordered_max :
        finite (|U|) → ∀ S : U → Prop, (∃ x, S x) → ∃ x, is_greatest op S x.
    intros U_fin S S_ex.
    pose proof (finite_well_founded_max U_fin S S_ex) as [x [Sx x_max]].
    exists x.
    split; try exact Sx.
    intros y Sy.
    classic_contradiction contr.
    rewrite op_nle_lt in contr.
    destruct contr as [leq neq].
    rewrite neq_sym in neq.
    apply (x_max y Sy); assumption.
Qed.

(* begin hide *)
End InfiniteOrder2.

Section InfiniteOrder3.

Context {U : Type} {op : U → U → Prop}.
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op
}.
(* end hide *)
Theorem finite_well_founded :
        finite (|U|) → ∀ S : U → Prop, (∃ x, S x) → ∃ x, is_minimal op S x.
    make_dual_op op.
    intros U_fin S S_ex.
    pose proof (finite_well_founded_max (op := dual_op op) U_fin S S_ex) as x.
    exact x.
Qed.

(* begin hide *)
Context `{Connex U op}.
(* end hide *)
Theorem finite_well_ordered :
        finite (|U|) → ∀ S : U → Prop, (∃ x, S x) → ∃ x, is_least op S x.
    make_dual_op op.
    intros U_fin S S_ex.
    pose proof (finite_well_ordered_max (op := dual_op op) U_fin S S_ex) as x.
    exact x.
Qed.

(* begin hide *)
End InfiniteOrder3.

Section InfiniteOrder4.

Context {U : Type} {op : U → U → Prop}.
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op,
    Connex U op
}.

Local Instance op_le : Order U := {
    le := op
}.
(* end hide *)
Theorem finite_well_founded_set : ∀ S : U → Prop,
        finite (|set_type S|) → (∃ x, S x) → ∃ x, is_minimal op S x.
    intros S S_fin S_ex.
    assert (set_type S) as x.
    {
        apply ex_to_type in S_ex.
        destruct S_ex.
        split with x; exact s.
    }
    pose proof
        (finite_well_founded (op := le) S_fin (λ x, True) (ex_intro _ x true))
        as [[y Sy] [C0 y_min]].
    exists y.
    split; try exact Sy.
    intros z Sz neq leq.
    apply (y_min [z|Sz] true).
    -   intro contr.
        inversion contr.
        contradiction.
    -   apply leq.
Qed.

Theorem finite_well_founded_set_max : ∀ S : U → Prop,
        finite (|set_type S|) → (∃ x, S x) → ∃ x, is_maximal op S x.
    intros S S_fin S_ex.
    assert (set_type S) as x.
    {
        apply ex_to_type in S_ex.
        destruct S_ex.
        split with x; exact s.
    }
    pose proof
        (finite_well_founded_max (op := le) S_fin (λ x, True) (ex_intro _ x true))
        as [[y Sy] [C0 y_min]].
    exists y.
    split; try exact Sy.
    intros z Sz neq leq.
    apply (y_min [z|Sz] true).
    -   intro contr.
        inversion contr.
        contradiction.
    -   apply leq.
Qed.

Theorem finite_well_ordered_set : ∀ S : U → Prop,
        finite (|set_type S|) → (∃ x, S x) → ∃ x, is_least op S x.
    intros S S_fin S_ex.
    pose proof (finite_well_founded_set S S_fin S_ex) as [x [Sx x_least]].
    exists x.
    split; try exact Sx.
    intros y Sy.
    classic_contradiction contr.
    rewrite op_nle_lt in contr.
    destruct contr as [leq neq].
    exact (x_least y Sy neq leq).
Qed.

Theorem finite_well_ordered_set_max : ∀ S : U → Prop,
        finite (|set_type S|) → (∃ x, S x) → ∃ x, is_greatest op S x.
    intros S S_fin S_ex.
    pose proof (finite_well_founded_set_max S S_fin S_ex) as [x [Sx x_least]].
    exists x.
    split; try exact Sx.
    intros y Sy.
    classic_contradiction contr.
    rewrite op_nle_lt in contr.
    destruct contr as [leq neq].
    rewrite neq_sym in neq.
    exact (x_least y Sy neq leq).
Qed.

(* begin hide *)
End InfiniteOrder4.
(* end hide *)
Theorem empty_finite {U} : finite (|set_type (@empty U)|).
    rewrite <- empty_set_size.
    unfold zero; cbn.
    apply nat0_is_finite.
Qed.

Theorem singleton_finite {U} : ∀ a : U, finite (|set_type (singleton a)|).
    intros a.
    rewrite singleton_size.
    apply nat0_is_finite.
Qed.

Theorem card_pos_ex {U} : 0 ≠ |U| → U.
    intros U_neq.
    classic_contradiction contr.
    apply card_false_0 in contr.
    symmetry in contr.
    contradiction.
Qed.

Theorem infinite_ex {U} : infinite (|U|) → U.
    intros U_inf.
    apply card_pos_ex.
    intros contr.
    rewrite <- contr in U_inf.
    apply (lt_le_trans (nat0_is_finite 0)) in U_inf.
    destruct U_inf; contradiction.
Qed.

Theorem infinite_seq_ex {U} :
        infinite (|U|) → ∃ f : sequence U, ∀ i j, i ≠ j → f i ≠ f j.
    intros U_inf.
    unfold infinite in U_inf.
    unfold le in U_inf; equiv_simpl in U_inf.
    destruct U_inf as [f f_inj].
    exists f.
    intros i j neq eq.
    apply f_inj in eq.
    contradiction.
Qed.

Theorem finite_union_finite {U} : ∀ SS : (U → Prop) → Prop,
        finite (|set_type SS|) → (∀ S, SS S → finite (|set_type S|)) →
        finite (|set_type (⋃ SS)|).
    intros SS SS_fin S_fin.
    classic_case (U → False) as [U_nex|u_ex].
    {
        assert (⋃ SS = ∅) as eq.
        {
            apply not_ex_empty.
            intros x [A [SS_A Ax]].
            exact (U_nex x).
        }
        rewrite eq.
        rewrite <- empty_set_size.
        apply nat0_is_finite.
    }
    apply fin_nat0_ex in SS_fin as [n n_eq].
    revert SS n_eq S_fin.
    nat0_induction n.
    -   intros SS SS_empty S_fin.
        assert (⋃ SS = ∅) as eq.
        {
            apply not_ex_empty.
            intros x [A [SS_A Ax]].
            apply zero_is_empty in SS_empty.
            rewrite SS_empty in SS_A.
            exact SS_A.
        }
        rewrite eq.
        rewrite <- empty_set_size.
        apply nat0_is_finite.
    -   intros SS SS_size S_fin.
        assert U as x.
        {
            classic_contradiction contr.
            contradiction.
        }
        assert (set_type SS) as S.
        {
            classic_contradiction contr.
            apply card_false_0 in contr.
            rewrite contr in SS_size.
            change 0 with (nat0_to_card 0) in SS_size.
            apply nat0_to_card_eq in SS_size.
            inversion SS_size.
        }
        symmetry in SS_size.
        pose proof (card_plus_one_nat0 _ _ S SS_size) as SS_size2.
        destruct S as [S SS_S]; cbn in *.
        symmetry in SS_size2.
        assert (∀ T, (SS - singleton S)%set T → finite (|set_type T|))as S_fin2.
        {
            intros T [SS_T ST].
            apply S_fin.
            exact SS_T.
        }
        specialize (IHn _ SS_size2 S_fin2).
        apply S_fin in SS_S.
        apply fin_nat0_ex in IHn as [m1 m1_eq].
        apply fin_nat0_ex in SS_S as [m2 m2_eq].
        pose proof (lrplus m1_eq m2_eq) as eq.
        rewrite nat0_to_card_plus in eq.
        unfold plus in eq at 2; equiv_simpl in eq.
        assert (finite (nat0_to_card (m1 + m2))) as SS_fin
            by apply nat0_is_finite.
        rewrite eq in SS_fin.
        apply (le_lt_trans2 SS_fin).
        unfold le; equiv_simpl.
        assert (∀ x : set_type (⋃ SS),
            ¬S [x|] → (⋃ (SS - singleton S)%set) [x|]) as f_in.
        {
            intros [y [T [SS_T Ty]]] nSy; cbn in nSy.
            exists T.
            repeat split; cbn; try assumption.
            intros contr.
            rewrite contr in nSy.
            contradiction.
        }
        exists (λ x, match strong_excluded_middle (S [x|]) with
            | strong_or_left Sx => inr [[x|] | Sx]
            | strong_or_right nSx => inl [_|f_in _ nSx]
            end).
        clear.
        intros a b.
        destruct (strong_excluded_middle _) as [Sa|nSa];
        destruct (strong_excluded_middle _) as [Sb|nSb].
        +   intros eq.
            inversion eq as [eq2].
            apply set_type_eq.
            exact eq2.
        +   intros eq; inversion eq.
        +   intros eq; inversion eq.
        +   intros eq.
            inversion eq as [eq2].
            apply set_type_eq.
            exact eq2.
Qed.

Theorem inter_le {U} : ∀ (SS : (U → Prop) → Prop) S μ,
        SS S → |set_type S| <= μ → |set_type (⋂ SS)| <= μ.
    intros SS S μ SS_S eq.
    apply (trans2 eq); clear eq μ.
    unfold le; equiv_simpl.
    exists (λ x : set_type (⋂ SS), [[x|] | [|x] S SS_S]).
    intros a b eq.
    inversion eq as [eq2].
    apply set_type_eq; exact eq2.
Qed.

Theorem finite_inter_finite {U} : ∀ SS : (U → Prop) → Prop,
        (∃ S, SS S ∧ finite (|set_type S|)) →
        finite (|set_type (⋂ SS)|).
    intros SS [S [SS_S S_fin]].
    apply (le_lt_trans2 S_fin).
    unfold le; equiv_simpl.
    exists (λ x : set_type (⋂ SS), [[x|] | [|x] S SS_S]).
    intros a b eq.
    inversion eq as [eq2].
    apply set_type_eq in eq2.
    exact eq2.
Qed.

Theorem union_size_mult {U} : ∀ (SS : (U → Prop) → Prop) κ μ,
        |set_type SS| <= κ → (∀ S, SS S → |set_type S| <= μ) →
        |set_type (⋃ SS)| <= κ * μ.
    intros SS A B A_eq B_ge'.
    classic_case (0 = B) as [B_z|B_nz].
    1: {
        subst B.
        rewrite mult_ranni.
        classic_contradiction contr.
        rewrite nle_lt in contr.
        destruct contr as [C0 contr]; clear C0.
        apply card_pos_ex in contr.
        destruct contr as [x [S [SS_S Sx]]].
        specialize (B_ge' S SS_S).
        apply (antisym (card_le_zero _)) in B_ge'.
        apply zero_is_empty in B_ge'.
        rewrite B_ge' in Sx.
        contradiction Sx.
    }
    equiv_get_value A B.
    apply card_pos_ex in B_nz as b_val.
    assert (∀ S : set_type SS, ∃ f : set_type [S|] → B, injective f) as B_ge.
    {
        intros [S SS_S].
        specialize (B_ge' S SS_S).
        unfold le in B_ge'; equiv_simpl in B_ge'.
        exact B_ge'.
    }
    clear B_ge'.
    unfold le in A_eq; equiv_simpl in A_eq.
    destruct A_eq as [f f_inj].
    unfold le, mult; equiv_simpl.
    pose (x_to_S (x : set_type (⋃ SS)) := ex_val [|x]).
    assert (∀ S : set_type SS, ∃ g : U → B,
            ∀ a b, [S|] a → [S|] b → g a = g b → a = b) as g_ex.
    {
        intros S.
        specialize (B_ge S) as [g g_inj].
        exists (λ x, match (strong_excluded_middle ([S|] x)) with
        | strong_or_left H => g [x|H]
        | strong_or_right _ => b_val
        end).
        intros a b Sa Sb.
        do 2 destruct (strong_excluded_middle _); try contradiction.
        intros eq.
        apply g_inj in eq.
        inversion eq.
        reflexivity.
    }
    pose (S_in_SS (x : set_type (⋃ SS)) := land (ex_proof [|x])).
    pose (x_to_g (x : set_type (⋃ SS)) := ex_val (g_ex [x_to_S x|S_in_SS x])).
    pose (x_in_S (x : set_type (⋃ SS)) := rand (ex_proof [|x])).
    exists (λ x : set_type (⋃ SS), (
        f [x_to_S x | S_in_SS x],
        x_to_g x [x|]
    )).
    intros a b eq.
    inversion eq as [[eq1 eq2]]; clear eq.
    apply f_inj in eq1.
    inversion eq1 as [eq3].
    unfold x_to_g in eq2.
    rewrite eq1 in eq2.
    rewrite_ex_val g g_inj; cbn in *.
    apply set_type_eq.
    apply g_inj.
    -   rewrite <- eq3.
        apply x_in_S.
    -   apply x_in_S.
    -   exact eq2.
Qed.

Theorem countable_union_countable {U} : ∀ (SS : (U → Prop) → Prop),
        countable (|set_type SS|) → (∀ S, SS S → countable (|set_type S|)) →
        countable (|set_type (⋃ SS)|).
    intros SS SS_count S_count.
    pose proof (union_size_mult SS _ _ SS_count S_count) as leq.
    rewrite nat0_mult_nat0 in leq.
    exact leq.
Qed.
(* begin hide *)
Close Scope card_scope.
(* end hide *)
