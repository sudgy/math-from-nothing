Require Import init.

Require Export relation.

(* begin hide *)
Section OrderDictionary.

Variables U V : Type.

Context `{
    Order U,
    Order V,
    Connex U le,
    Antisymmetric U le,
    Transitive U le,
    Reflexive U le,
    Connex V le,
    Antisymmetric V le,
    Transitive V le,
    Reflexive V le
}.
(* end hide *)
Instance dictionary_order : Order (U * V) := {
    le a b := match a, b with
        | (a1, b1), (a2, b2) => (b1 < b2) ∨ (a1 <= a2 ∧ b1 = b2)
        end
}.
(* begin hide *)
Global Program Instance dict_order_connex : @Connex (U * V) le.
Next Obligation.
    destruct x as [a1 b1], y as [a2 b2].
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

Global Program Instance dict_order_antisym : @Antisymmetric (U * V) le.
Next Obligation.
    rename H9 into eq1, H10 into eq2.
    destruct x as [a1 b1], y as [a2 b2].
    unfold le in eq1, eq2; cbn in *.
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

Global Program Instance dict_order_trans : @Transitive (U * V) le.
Next Obligation.
    rename H9 into xy, H10 into yz.
    destruct x as [a1 b1], y as [a2 b2], z as [a3 b3].
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
        split.
        2: reflexivity.
        exact (trans leq1 leq2).
Qed.

Global Program Instance dict_order_refl : @Reflexive (U * V) le.
Next Obligation.
    destruct x as [a1 b1].
    right.
    split.
    -   apply refl.
    -   reflexivity.
Qed.

End OrderDictionary.
(* end hide *)
