Require Import init.

Require Export order_def.

(* begin hide *)
Section OrderDictionary.

Variables U V : Type.

Context `{
    WellOrder U,
    WellOrder V
}.
(* end hide *)
Instance dictionary_order : Order (U * V) := {
    le a b := match a, b with
        | (a1, b1), (a2, b2) => (b1 < b2) ∨ (a1 ≤ a2 ∧ b1 = b2)
        end
}.
(* begin hide *)
Global Instance dict_order_connex : @Connex (U * V) le.
Proof.
    split.
    intros [a1 b1] [a2 b2].
    unfold le; cbn.
    destruct (trichotomy b1 b2) as [[ltq|eq]|ltq].
    -   left; left.
        exact ltq.
    -   destruct (connex a1 a2) as [leq|leq].
        +   left; right.
            split; assumption.
        +   symmetry in eq.
            right; right.
            split; assumption.
    -   right; left.
        exact ltq.
Qed.

Global Instance dict_order_antisym : @Antisymmetric (U * V) le.
Proof.
    split.
    intros [a1 b1] [a2 b2] eq1 eq2.
    unfold le in eq1, eq2; cbn in eq1, eq2.
    destruct eq1 as [ltq1|[leq1 eq1]];
    destruct eq2 as [ltq2|[leq2 eq2]].
    -   destruct (trans ltq1 ltq2); contradiction.
    -   subst.
        destruct ltq1; contradiction.
    -   subst.
        destruct ltq2; contradiction.
    -   pose proof (antisym leq1 leq2).
        subst.
        reflexivity.
Qed.

Global Instance dict_order_trans : @Transitive (U * V) le.
Proof.
    split.
    intros [a1 b1] [a2 b2] [a3 b3] xy yz.
    unfold le in xy, yz; unfold le; cbn in *.
    destruct xy as [ltq1|[leq1 eq1]];
    destruct yz as [ltq2|[leq2 eq2]].
    -   left.
        exact (trans ltq1 ltq2).
    -   subst.
        left.
        exact ltq1.
    -   subst.
        left.
        exact ltq2.
    -   subst.
        right.
        split; [>|reflexivity].
        exact (trans leq1 leq2).
Qed.

Global Instance dict_order_well_founded : @WellOrdered (U * V) le.
Proof.
    split.
    intros S [[a b] Sx].
    pose (SV (b : V) := ∃ a, S (a, b)).
    pose proof (well_ordered SV) as SV_wo.
    prove_parts SV_wo; [>exists b; exists a; exact Sx|].
    destruct SV_wo as [b' [Sb' b'_least]].
    pose (SU (a : U) := S (a, b')).
    pose proof (well_ordered SU Sb') as [a' [Sa' a'_least]].
    exists (a', b').
    split; [>exact Sa'|].
    intros [x y] Sxy.
    unfold le; cbn.
    specialize (b'_least y).
    prove_parts b'_least; [>exists x; exact Sxy|].
    classic_case (b' = y) as [eq|neq].
    -   subst y.
        right.
        split; [>|reflexivity].
        apply a'_least.
        exact Sxy.
    -   left.
        split; assumption.
Qed.

End OrderDictionary.
(* end hide *)
