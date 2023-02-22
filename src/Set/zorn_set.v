Require Import init.

Require Import zorn.

Require Export set.

Section ZornSet.

Context {U : Type}.

Local Instance subset_order : Order (U → Prop) := {le := subset}.

Variable SS : (U → Prop) → Prop.
Hypothesis SS_union : ∀ F : (set_type SS) → Prop, is_chain le F →
    SS (⋃ (image_under (λ S, [S|]) F)).

Theorem set_zorn : ∃ S : set_type SS, ∀ A : set_type SS, ¬([S|] ⊂ [A|]).
Proof.
    pose proof (zorn (le (U := set_type SS))) as S_ex.
    prove_parts S_ex.
    {
        intros F F_chain.
        specialize (SS_union F F_chain).
        exists [_|SS_union].
        intros A FA.
        unfold le; cbn.
        apply union_sub.
        exact (image_under_in FA).
    }
    destruct S_ex as [S S_max].
    exists S.
    intros A.
    specialize (S_max A).
    setoid_rewrite <- set_type_lt in S_max.
    exact S_max.
Qed.

End ZornSet.
