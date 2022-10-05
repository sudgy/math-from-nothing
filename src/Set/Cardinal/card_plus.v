Require Import init.

Require Export card_base.
Require Import card_order.
Require Import set.
Require Import function.
Require Export plus_group.
Require Import nat.

(* begin hide *)
Open Scope card_scope.
(* end hide *)
Lemma card_plus_wd : ∀ A B C D, A ~ B → C ~ D → sum A C ~ sum B D.
Proof.
    intros A B C D [f f_bij] [g g_bij].
    exists (λ x, match x with
                 | inl a => inl (f a)
                 | inr c => inr (g c)
                 end).
    split.
    -   intros [a1|c1] [a2|c2] eq.
        all: inversion eq as [eq2].
        all: apply f_equal.
        +   apply f_bij.
            exact eq2.
        +   apply g_bij.
            exact eq2.
    -   intros [b|d].
        +   pose proof (rand f_bij b) as [a eq].
            exists (inl a).
            apply f_equal.
            exact eq.
        +   pose proof (rand g_bij d) as [c eq].
            exists (inr c).
            apply f_equal.
            exact eq.
Qed.

Global Instance card_plus_class : Plus card := {
    plus := binary_self_op card_plus_wd
}.

(* begin hide *)
Lemma card_plus_assoc : ∀ κ μ ν, κ + (μ + ν) = (κ + μ) + ν.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold plus; equiv_simpl.
    exists (λ x,
        match x with
        | inl a => inl (inl a)
        | inr x' => match x' with
                    | inl b => inl (inr b)
                    | inr c => inr c
                    end
        end).
    split.
    -   intros [a1|[b1|c1]] [a2|[b2|c2]] eq.
        all: inversion eq.
        all: reflexivity.
    -   intros [[a|b]|c].
        +   exists (inl a).
            reflexivity.
        +   exists (inr (inl b)).
            reflexivity.
        +   exists (inr (inr c)).
            reflexivity.
Qed.
Global Instance card_plus_assoc_class : PlusAssoc card := {
    plus_assoc := card_plus_assoc
}.

Lemma card_plus_comm : ∀ κ μ, κ + μ = μ + κ.
Proof.
    intros A B.
    equiv_get_value A B.
    unfold plus; equiv_simpl.
    exists (λ x, match x with
                 | inl a => inr a
                 | inr b => inl b
                 end).
    split.
    -   intros [a1|b1] [a2|b2] eq.
        all: inversion eq.
        all: reflexivity.
    -   intros [b|a].
        +   exists (inr b).
            reflexivity.
        +   exists (inl a).
            reflexivity.
Qed.
Global Instance card_plus_comm_class : PlusComm card := {
    plus_comm := card_plus_comm
}.

Global Instance card_zero : Zero card := {
    zero := nat_to_card 0
}.

Lemma card_plus_lid : ∀ κ, 0 + κ = κ.
Proof.
    intros A.
    equiv_get_value A.
    unfold zero; cbn.
    unfold nat_to_card, plus; equiv_simpl.
    assert (set_type (λ x : nat, x < 0) → False) as xf.
    {
        intros [x x_lt].
        exact (nat_neg2 x_lt).
    }
    exists (λ x, match x with
                 | inl y => False_rect _ (xf y)
                 | inr a => a
                 end).
    split.
    -   intros [x|a1]; try contradiction (xf x).
        intros [x|a2]; try contradiction (xf x).
        intro eq.
        rewrite eq; reflexivity.
    -   intros a.
        exists (inr a).
        reflexivity.
Qed.
Global Instance card_plus_lid_class : PlusLid card := {
    plus_lid := card_plus_lid
}.

Theorem card_le_lplus : ∀ κ μ ν, κ ≤ μ → ν + κ ≤ ν + μ.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold le, plus; equiv_simpl.
    intros [f f_inj].
    exists (λ x, match x with
                 | inl c => inl c
                 | inr a => inr (f a)
                 end).
    intros [c1|a1] [c2|a2] eq.
    all: inversion eq as [eq2].
    -   reflexivity.
    -   apply f_inj in eq2.
        rewrite eq2; reflexivity.
Qed.
Global Instance card_le_lplus_class : OrderLplus card := {
    le_lplus := card_le_lplus
}.
(* end hide *)
Theorem card_le_zero : ∀ κ, 0 ≤ κ.
Proof.
    intros A.
    equiv_get_value A.
    unfold zero; cbn.
    unfold nat_to_card, le; equiv_simpl.
    assert (set_type (λ x : nat, x < 0) → False) as xf.
    {
        intros [x x_lt].
        exact (nat_neg2 x_lt).
    }
    exists (empty_function _ _ xf).
    apply empty_inj.
Qed.

Theorem card_union_left {U} : ∀ S T : U → Prop,
    |set_type S| ≤ |set_type (S ∪ T)%set|.
Proof.
    intros S T.
    unfold le; equiv_simpl.
    exists (λ (x : set_type S), [[x|] | make_lor [|x]]).
    intros a b eq.
    inversion eq as [eq2].
    apply set_type_eq in eq2.
    exact eq2.
Qed.

Theorem card_union_right {U} : ∀ S T : U → Prop,
    |set_type T| ≤ |set_type (S ∪ T)%set|.
Proof.
    intros S T.
    rewrite union_comm.
    apply card_union_left.
Qed.

Theorem card_plus_union {U} : ∀ S T : U → Prop,
    |set_type (S ∪ T)%set| ≤ |set_type S| + |set_type T|.
Proof.
    intros S T.
    unfold plus, le; equiv_simpl.
    exists (λ (x : set_type (S ∪ T)%set),
        match or_to_strong _ _ [|x] with
        | strong_or_left H => inl [[x|] | H]
        | strong_or_right H => inr [[x|] | H]
        end).
    intros [a a_in] [b b_in] eq.
    destruct (or_to_strong _ _ _) as [Sa|Ta].
    all: destruct (or_to_strong _ _ _) as [Sb|Tb].
    all: inversion eq.
    all: subst.
    all: apply set_type_eq; reflexivity.
Qed.

Theorem card_false_0 : ∀ A, (A → False) → |A| = 0.
Proof.
    intros A A_false.
    unfold zero; cbn.
    unfold nat_to_card; equiv_simpl.
    exists (λ x, False_rect _ (A_false x)).
    split.
    -   intros a b eq.
        contradiction (A_false a).
    -   intros a.
        contradiction (nat_lt_0_false a).
Qed.

Theorem card_plus_one_nat {U} : ∀ (S : U → Prop) n (a : set_type S),
    |set_type S| = nat_to_card (nat_suc n) →
    |set_type (S - ❴[a|]❵)%set| = nat_to_card n.
Proof.
    intros S n a S_eq.
    unfold nat_to_card; equiv_simpl.
    unfold nat_to_card in S_eq; equiv_simpl in S_eq.
    destruct S_eq as [f [f_inj f_sur]].
    classic_case ([f a|] = n) as [fa_eq|fa_neq].
    -   pose (f' (x : set_type (S - ❴[a|]❵)%set)
            := f [[x|] | land [|x]]).
        assert (∀ x, [f' x|] < n) as f'_lt.
        {
            intros x.
            split.
            -   rewrite <- nat_lt_suc_le.
                exact [|f' x].
            -   intro contr.
                rewrite <- fa_eq in contr.
                apply set_type_eq in contr.
                unfold f' in contr.
                apply f_inj in contr.
                destruct x as [x [Sx xa]].
                destruct a as [a Sa].
                cbn in contr.
                unfold list_to_set in xa.
                cbn in xa.
                inversion contr.
                symmetry in H0.
                contradiction.
        }
        exists (λ x, [[f' x|]|f'_lt x]).
        split.
        +   intros x y eq.
            unfold f' in eq.
            inversion eq as [eq2].
            apply set_type_eq in eq2.
            apply f_inj in eq2.
            inversion eq2 as [eq3].
            apply set_type_eq in eq3.
            exact eq3.
        +   intros [y y_lt].
            assert (y < nat_suc n) as y_lt2.
            {
                apply (trans y_lt).
                apply nat_lt_suc.
            }
            pose proof (f_sur [y|y_lt2]) as [x x_eq].
            assert ([a|] ≠ [x|]) as x_neq.
            {
                intros eq.
                apply set_type_eq in eq.
                subst.
                rewrite x_eq in fa_eq.
                cbn in fa_eq.
                subst.
                destruct y_lt; contradiction.
            }
            exists [[x|] | make_and [|x] x_neq].
            unfold f'; cbn.
            apply set_type_eq; cbn.
            destruct x as [x Sx].
            cbn.
            rewrite (proof_irrelevance _ Sx).
            rewrite x_eq.
            reflexivity.
    -   pose (f' (x : set_type (S - ❴[a|]❵)%set) :=
            let x' := [[x|] | land [|x]] in
            If [f x'|] = n then [f a|]
            else [f x'|]).
        assert (∀ x, f' x < n) as f'_lt.
        {
            intros x.
            unfold f'.
            case_if.
            -   split; try exact fa_neq.
                rewrite <- nat_lt_suc_le.
                exact [|f a].
            -   split; try exact n0.
                rewrite <- nat_lt_suc_le.
                exact [|f [[x|] | land [|x]]].
        }
        exists (λ x, [f' x|f'_lt x]).
        split.
        +   intros x y eq.
            unfold f' in eq.
            inversion eq as [eq2]; clear eq.
            repeat case_if.
            *   rewrite <- e0 in e.
                apply set_type_eq in e.
                apply f_inj in e.
                inversion e.
                apply set_type_eq.
                exact H0.
            *   apply set_type_eq in eq2.
                apply f_inj in eq2.
                destruct y as [y [Sy y_neq]].
                unfold list_to_set in y_neq; cbn in eq2.
                destruct a as [a Sa].
                inversion eq2.
                contradiction.
            *   apply set_type_eq in eq2.
                apply f_inj in eq2.
                destruct x as [x [Sx x_neq]].
                unfold list_to_set in x_neq; cbn in eq2.
                destruct a as [a Sa].
                inversion eq2.
                symmetry in H0.
                contradiction.
            *   apply set_type_eq in eq2.
                apply f_inj in eq2.
                inversion eq2 as [eq3].
                apply set_type_eq in eq3.
                exact eq3.
        +   intros [y y_lt].
            classic_case ([f a|] = y) as [fay|fay].
            *   pose proof (f_sur [n|nat_lt_suc n]) as [x x_eq].
                assert ([a|] ≠ [x|]) as neq.
                {
                    intros contr.
                    apply set_type_eq in contr.
                    subst.
                    rewrite x_eq in fa_neq.
                    contradiction.
                }
                exists [[x|] | make_and [|x] neq].
                unfold f'; cbn.
                apply set_type_eq; cbn.
                case_if; cbn.
                --  exact fay.
                --  destruct x as [x Sx]; cbn in *.
                    rewrite (proof_irrelevance _ Sx) in n0.
                    rewrite x_eq in n0.
                    contradiction.
            *   pose proof (f_sur [y|trans y_lt (nat_lt_suc n)]) as [x x_eq].
                assert ([a|] ≠ [x|]) as neq.
                {
                    intros contr.
                    apply set_type_eq in contr.
                    subst.
                    rewrite x_eq in fay.
                    contradiction.
                }
                exists [[x|] | make_and [|x] neq].
                unfold f'; cbn.
                apply set_type_eq; cbn.
                destruct x as [x Sx]; cbn in *.
                case_if; cbn.
                --  rewrite (proof_irrelevance _ Sx) in e.
                    rewrite x_eq in e.
                    cbn in e.
                    subst.
                    destruct y_lt; contradiction.
                --  rewrite (proof_irrelevance _ Sx).
                    rewrite x_eq.
                    reflexivity.
Qed.

Theorem zero_is_empty {U} : ∀ S : U → Prop, 0 = |set_type S| → S = empty.
Proof.
    intros S S_0.
    symmetry in S_0.
    apply empty_eq.
    intros x Sx.
    unfold zero in S_0; cbn in S_0.
    unfold nat_to_card in S_0; equiv_simpl in S_0.
    destruct S_0 as [f f_bij].
    contradiction (nat_lt_0_false (f [x|Sx])).
Qed.

Theorem empty_set_size {U} : 0 = |set_type (U := U) ∅|.
Proof.
    symmetry; apply card_false_0.
    intros [x C].
    exact C.
Qed.

Theorem disjoint_union_plus {U} : ∀ (A B : U → Prop), A ∩ B = ∅ →
    |set_type A| + |set_type B| = |set_type (A ∪ B)|.
Proof.
    intros A B dis.
    unfold plus; equiv_simpl.
    exists (λ x, match x with
        | inl a => [[a|]|make_lor [|a]]
        | inr b => [[b|]|make_ror [|b]]
        end).
    split.
    -   intros [[a1 Aa1]|[b1 Bb1]] [[a2 Aa2]|[b2 Bb2]] eq.
        all: apply set_type_eq in eq; cbn in eq; subst.
        +   apply f_equal.
            apply set_type_eq; reflexivity.
        +   assert ((A ∩ B) b2) as b2_in by (split; assumption).
            rewrite dis in b2_in.
            contradiction b2_in.
        +   assert ((A ∩ B) a2) as a2_in by (split; assumption).
            rewrite dis in a2_in.
            contradiction a2_in.
        +   apply f_equal.
            apply set_type_eq; reflexivity.
    -   intros [y [Ay|By]].
        +   exists (inl [y|Ay]).
            reflexivity.
        +   exists (inr [y|By]).
            reflexivity.
Qed.

Theorem card_nz_ex {U} : 0 ≠ |U| → U.
Proof.
    intros neq.
    classic_contradiction contr.
    apply card_false_0 in contr.
    symmetry in contr.
    contradiction.
Qed.
(* begin hide *)
Close Scope card_scope.
(* end hide *)
