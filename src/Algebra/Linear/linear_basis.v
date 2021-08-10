Require Import init.

Require Export linear_base.
Require Import linear_span.
Require Import linear_subspace.
Require Import list.
Require Import set.

Definition linearly_independent {U V} `{Zero U, Zero V, Plus V, ScalarMult U V}
    (S : V → Prop) :=
    ∀ l1 l2 eq, (∀ v, in_list l2 v → S v) → list_unique l2 →
    0 = linear_combination l1 l2 eq → (∀ α, in_list l1 α → 0 = α).
Definition linearly_dependent {U V} `{Zero U, Zero V, Plus V, ScalarMult U V}
    (S : V → Prop) := ¬linearly_independent S.

Definition basis {U V} `{Zero U, Zero V, Plus V, Neg V, ScalarMult U V}
    (S : V → Prop) := linearly_independent S ∧ linear_span U S = all.

Section Basis.

Context {U V} `{
    UZ : Zero U,
    UO : One U,
    UM : Mult U,
    UD : Div U,
    @MultLinv U UZ UM UO UD,
    @NotTrivial U UZ UO,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarComp U V UM SM,
    @ScalarLdist U V VP SM,
    @ScalarId U V UO SM
}.

Theorem zero_linearly_dependent : ∀ (S : V → Prop), S 0 → linearly_dependent S.
    intros S S0 ind.
    pose (l1 := 1 :: list_end).
    pose (l2 := 0 :: list_end).
    assert (list_size l1 = list_size l2) as eq.
    {
        cbn.
        reflexivity.
    }
    apply not_trivial.
    apply (ind l1 l2 eq).
    -   intros v v_in.
        cbn in v_in.
        destruct v_in; try contradiction.
        subst v.
        exact S0.
    -   cbn.
        rewrite not_false.
        split; exact true.
    -   cbn.
        rewrite plus_rid.
        rewrite scalar_ranni.
        reflexivity.
    -   cbn.
        left.
        reflexivity.
Qed.

Theorem singleton_linearly_independent :
        ∀ v, 0 ≠ v → linearly_independent (singleton v).
    intros v v_neq l1 l2 l12_eq in_l2 uni eq α α_in.
    assert (l2 = v :: list_end) as l2_eq.
    {
        destruct l2.
        -   cbn in *.
            destruct l1.
            +   cbn in α_in.
                contradiction α_in.
            +   cbn in l12_eq.
                inversion l12_eq.
        -   cbn in *.
            destruct uni as [uni1 uni2].
            assert (v0 = v) as v_eq.
            {
                symmetry; apply in_l2.
                left; reflexivity.
            }
            subst v0.
            apply f_equal.
            destruct l2; try reflexivity.
            cbn in *.
            destruct uni2 as [uni2 uni3].
            rewrite not_or in uni1.
            exfalso; apply (land uni1).
            symmetry; apply in_l2.
            right; left.
            reflexivity.
    }
    subst l2.
    cbn in *.
    destruct l1.
    -   cbn in *.
        contradiction α_in.
    -   destruct l1.
        +   cbn in *.
            classic_contradiction contr.
            destruct α_in as [α_eq|C0]; try contradiction.
            subst u.
            rewrite plus_rid in eq.
            apply (lscalar (/α)) in eq.
            rewrite scalar_ranni in eq.
            rewrite scalar_comp in eq.
            rewrite mult_linv in eq by exact contr.
            rewrite scalar_id in eq.
            contradiction.
        +   cbn in l12_eq.
            inversion l12_eq.
Qed.

Lemma basis_unique : ∀ S v, basis S →
        ∃ l1 l2 eq,
        (∀ b, in_list l2 b → S b) ∧
        list_unique l2 ∧
        v = linear_combination l1 l2 eq ∧
        (∀ l1' l2' eq',
            (∀ b, in_list l2' b → S b) →
            list_unique l2' →
            v = linear_combination l1' l2' eq' →
            l1 = l1' ∧ l2 = l2').
    intros S v [S_ind S_span].
    assert (all v) as v_in by exact true.
    rewrite <- S_span in v_in.
    unfold linear_span in v_in.
    specialize (v_in (linear_span_subspace U S)).
    cbn in v_in.
    assert (S ⊆ linear_span U S) as S_sub.
    {
        rewrite S_span.
        apply sub_all.
    }
    specialize (v_in S_sub); clear S_sub.
    unfold linear_span in v_in.
Abort.

End Basis.
