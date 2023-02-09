Require Import init.

Require Export set.
Require Export card.

Open Scope card_scope.
Open Scope set_scope.

#[universes(template)]
Class Topology U := {
    open : (U → Prop) → Prop;
    empty_open : open ∅;
    all_open : open all;
    union_open : ∀ S, S ⊆ open → open (⋃ S);
    inter_open : ∀ S, S ⊆ open → (finite (|set_type S|)) → open (⋂ S);
}.
Arguments open: simpl never.

Definition closed {U} `{Topology U} S := open (𝐂 S).
Definition clopen {U} `{Topology U} S := open S ∧ closed S.
Definition neighborhood {U} `{Topology U} x S := open S ∧ S x.

(* T1 is finer than T2 *)
Definition topology_finer {U} (T1 T2 : Topology U) :=
    @open U T2 ⊆ @open U T1.
Definition topology_strictly_finer {U} (T1 T2 : Topology U) :=
    @open U T2 ⊂ @open U T1.
Definition topology_comparable {U} (T1 T2 : Topology U) :=
    topology_finer T1 T2 ∨ topology_finer T2 T1.

(* begin hide *)
Section BasicTopology.

Context {U : Type}.
(* end hide *)
Program Instance discrete_topology : Topology U := {
    open := @all (U → Prop)
}.
Next Obligation.
    exact true.
Qed.
Next Obligation.
    exact true.
Qed.
Next Obligation.
    exact true.
Qed.
Next Obligation.
    exact true.
Qed.
Remove Hints discrete_topology : typeclass_instances.

Program Instance trivial_topology : Topology U := {
    open := λ S, S = ∅ ∨ S = all
}.
Next Obligation.
    classic_case (S all) as [all_in|all_nin].
    -   right.
        apply predicate_ext.
        intros x; split.
        +   intros; exact true.
        +   intros C0; clear C0.
            exists all.
            split.
            *   exact all_in.
            *   exact true.
    -   left.
        apply predicate_ext.
        intros x; split.
        +   intros [A [SA Ax]].
            specialize (H A SA).
            destruct H.
            *   subst.
                exact Ax.
            *   subst.
                contradiction.
        +   intros contr.
            contradiction contr.
Qed.
Next Obligation.
    clear H0.
    classic_case (S ∅) as [empty_in|empty_nin].
    -   left.
        apply predicate_ext.
        intros x; split.
        +   intros A.
            apply A in empty_in.
            exact empty_in.
        +   intros contr.
            contradiction contr.
    -   right.
        apply predicate_ext.
        intros x; split.
        +   intros; exact true.
        +   intros C0 A SA; clear C0.
            specialize (H A SA).
            destruct H; subst.
            *   contradiction.
            *   exact true.
Qed.
Remove Hints trivial_topology : typeclass_instances.

(* begin hide *)
End BasicTopology.

Section Topology.

Context {U} `{Top : Topology U}.
(* end hide *)
Theorem discrete_finer : topology_finer discrete_topology Top.
Proof.
    intros S S_open.
    exact true.
Qed.

Theorem inter_open2 : ∀ A B, open A → open B → open (A ∩ B).
Proof.
    intros A B A_open B_open.
    pose (S := ❴A❵ ∪ ❴B❵).
    assert (⋂ S = A ∩ B) as eq.
    {
        apply predicate_ext.
        intros x.
        split.
        -   intros S_all.
            split.
            +   apply S_all.
                left.
                reflexivity.
            +   apply S_all.
                right.
                reflexivity.
        -   intros [Ax Bx] T ST.
            destruct ST as [TA|TB].
            +   rewrite <- TA.
                exact Ax.
            +   rewrite <- TB.
                exact Bx.
    }
    rewrite <- eq.
    apply inter_open.
    -   intros T [TA|TB].
        +   rewrite <- TA.
            exact A_open.
        +   rewrite <- TB.
            exact B_open.
    -   unfold S.
        apply (le_lt_trans (card_plus_union _ _)).
        do 2 rewrite singleton_size.
        unfold one; cbn.
        rewrite nat_to_card_plus.
        apply nat_is_finite.
Qed.

Theorem union_open2 : ∀ A B, open A → open B → open (A ∪ B).
Proof.
    intros A B A_open B_open.
    pose (S := ❴A❵ ∪ ❴B❵).
    assert (⋃ S = A ∪ B) as eq.
    {
        apply predicate_ext.
        intros x.
        split.
        -   intros [T [ST Tx]].
            destruct ST as [TA|TB].
            +   left.
                rewrite TA.
                exact Tx.
            +   right.
                rewrite TB.
                exact Tx.
        -   intros [Ax|Bx].
            +   exists A.
                split; try exact Ax.
                left; reflexivity.
            +   exists B.
                split; try exact Bx.
                right; reflexivity.
    }
    rewrite <- eq.
    apply union_open.
    -   intros T [TA|TB].
        +   rewrite <- TA.
            exact A_open.
        +   rewrite <- TB.
            exact B_open.
Qed.

Theorem empty_closed : closed ∅.
Proof.
    unfold closed, 𝐂, empty; cbn.
    rewrite not_false.
    exact all_open.
Qed.

Theorem all_closed : closed all.
Proof.
    unfold closed, 𝐂, all; cbn.
    rewrite not_true.
    exact empty_open.
Qed.

Theorem union_closed : ∀ S, S ⊆ closed → finite (|set_type S|) → closed (⋃ S).
Proof.
    intros S sub S_fin.
    unfold closed, 𝐂.
    pose (S' s := ∃ t, S t ∧ s = 𝐂 t).
    assert ((λ x, ¬(∃ A, S A ∧ A x)) = ⋂ S') as eq.
    {
        apply predicate_ext; intro x; split.
        -   intros not_A A [A' [SA' A'_eq]].
            rewrite not_ex in not_A.
            specialize (not_A A').
            rewrite not_and_impl in not_A.
            specialize (not_A SA').
            rewrite <- (compl_compl A') in not_A.
            rewrite <- A'_eq in not_A.
            unfold 𝐂 in not_A.
            rewrite not_not in not_A.
            exact not_A.
        -   intros all_A [A [SA Ax]].
            assert (S' (𝐂 A)) as S'A'.
            {
                exists A.
                split; auto.
            }
            specialize (all_A (𝐂 A) S'A').
            contradiction.
    }
    rewrite eq.
    apply inter_open.
    -   intros A [A' [SA' A_eq]].
        apply sub in SA'.
        rewrite A_eq.
        exact SA'.
    -   apply (le_lt_trans2 S_fin).
        unfold le; equiv_simpl.
        assert (∀ A : set_type S', S (𝐂 [A|])) as f_in.
        {
            intros [A [A' [SA' A_eq]]]; cbn.
            rewrite A_eq.
            rewrite compl_compl.
            exact SA'.
        }
        exists (λ A, [_|f_in A]).
        clear eq.
        split.
        intros [A [A' [SA' A_eq]]] [B [B' [SB' B_eq]]] eq; cbn in *.
        apply set_type_eq; cbn.
        inversion eq as [eq2]; clear eq.
        apply compl_eq.
        exact eq2.
Qed.

Theorem inter_closed : ∀ S, S ⊆ closed → closed (⋂ S).
Proof.
    intros S sub.
    unfold closed, 𝐂.
    pose (S' s := ∃ t, S t ∧ s = 𝐂 t).
    assert ((λ x, ¬(∀ A, S A → A x)) = ⋃ S') as eq.
    {
        apply predicate_ext; intro x; split.
        -   intros not_A.
            rewrite not_all in not_A.
            destruct not_A as [A not_A].
            rewrite not_impl in not_A.
            destruct not_A as [SA nAx].
            exists (𝐂 A).
            split.
            +   exists A.
                split; auto.
            +   exact nAx.
        -   intros [A [[A' [SA' A_eq]] Ax]] all_A.
            specialize (all_A A' SA').
            rewrite A_eq in Ax.
            contradiction.
    }
    rewrite eq.
    apply union_open.
    intros A [A' [SA' A_eq]].
    apply sub in SA'.
    rewrite A_eq.
    exact SA'.
Qed.

Theorem union_closed2 : ∀ A B, closed A → closed B → closed (A ∪ B).
Proof.
    intros A B A_closed B_closed.
    unfold closed.
    rewrite union_compl.
    apply inter_open2; assumption.
Qed.

Theorem inter_closed2 : ∀ A B, closed A → closed B → closed (A ∩ B).
Proof.
    intros A B A_closed B_closed.
    unfold closed.
    rewrite inter_compl.
    apply union_open2; assumption.
Qed.

Theorem open_complement_closed : ∀ A, open A → closed (𝐂 A).
Proof.
    intros A A_open.
    unfold closed.
    rewrite compl_compl.
    exact A_open.
Qed.

Theorem open_all_neigh :
    ∀ A : U → Prop, (∀ x, A x → ∃ S, neighborhood x S ∧ S ⊆ A) → open A.
Proof.
    intros A all_neighs.
    pose (SS S := ∃ x, S = ex_val (all_neighs [x|] [|x])).
    assert (A = ⋃ SS) as eq.
    {
        apply antisym.
        -   intros x Ax.
            exists (ex_val (all_neighs x Ax)).
            split.
            +   exists [x|Ax].
                reflexivity.
            +   rewrite_ex_val S S_H.
                apply S_H.
        -   intros x [S [[a S_eq] Sx]].
            subst S.
            rewrite_ex_val S S_sub.
            apply S_sub.
            exact Sx.
    }
    rewrite eq; clear eq.
    apply union_open.
    intros S [x S_eq]; subst S.
    rewrite_ex_val S S_H.
    apply S_H.
Qed.

(* begin hide *)
End Topology.
(* end hide *)
Theorem topology_equal : ∀ U (T1 : Topology U) (T2 : Topology U),
    (∀ S, @open U T1 S ↔ @open U T2 S) → T1 = T2.
Proof.
    intros U [open1 empty1 all1 union1 inter1]
             [open2 empty2 all2 union2 inter2] all_open.
    apply predicate_ext in all_open.
    unfold open in all_open; cbn in all_open.
    subst.
    rewrite (proof_irrelevance empty1 empty2).
    rewrite (proof_irrelevance all1 all2).
    rewrite (proof_irrelevance union1 union2).
    rewrite (proof_irrelevance inter1 inter2).
    reflexivity.
Qed.

Theorem topology_finer_antisym {U} : ∀ (T1 T2 : Topology U),
    topology_finer T1 T2 → topology_finer T2 T1 → T1 = T2.
Proof.
    intros T1 T2 T12 T21.
    apply topology_equal.
    intros S.
    split; intros S_open.
    -   apply T21 in S_open.
        exact S_open.
    -   apply T12 in S_open.
        exact S_open.
Qed.

Theorem topology_not_finer_strict {U} : ∀ (T1 T2 : Topology U),
    topology_finer T1 T2 → ¬topology_finer T2 T1
    → topology_strictly_finer T1 T2.
Proof.
    intros T1 T2 T12 T21.
    split.
    -   exact T12.
    -   intros contr.
        assert (T1 = T2) as eq.
        {
            apply topology_equal.
            rewrite contr.
            reflexivity.
        }
        subst.
        contradiction.
Qed.

(* begin hide *)
Section SingleOpenDiscrete.

Context {U} `{T : Topology U}.
(* end hide *)
Theorem single_open_discrete :
    (∀ x, open ❴x❵) → T = discrete_topology.
Proof.
    intros single_open.
    apply topology_equal.
    intros S.
    split; intros S_open.
    -   exact true.
    -   clear S_open.
        pose (SS A := ∃ a : U, S a ∧ A = ❴a❵).
        assert (S = ⋃ SS) as eq.
        {
            apply antisym.
            -   intros x Sx.
                exists ❴x❵.
                split.
                +   exists x.
                    split.
                    *   exact Sx.
                    *   reflexivity.
                +   reflexivity.
            -   intros x [A [SS_A Ax]].
                destruct SS_A as [x' [Sx' A_eq]].
                subst A.
                rewrite Ax in Sx'.
                exact Sx'.
        }
        rewrite eq.
        apply union_open.
        intros A [x [Sx A_eq]].
        subst A.
        apply single_open.
Qed.
(* begin hide *)
End SingleOpenDiscrete.

Close Scope set_scope.
Close Scope card_scope.
(* end hide *)
