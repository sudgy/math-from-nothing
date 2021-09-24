Require Import init.

Require Export linear_base.
Require Import linear_span.
Require Import linear_subspace.
Require Import list.
Require Import set.

Definition linearly_independent {U V} `{Zero U, Zero V, Plus V, ScalarMult U V}
    (S : V → Prop) :=
    ∀ l, (∀ v, (∃ α, in_list [l|] (α, v)) → S v) →
    0 = linear_combination l → (∀ α, (∃ v, in_list [l|] (α, v)) → 0 = α).
Definition linearly_dependent {U V} `{Zero U, Zero V, Plus V, ScalarMult U V}
    (S : V → Prop) := ¬linearly_independent S.

Definition basis {U V} `{Zero U, Zero V, Plus V, Neg V, ScalarMult U V}
    (S : V → Prop) := linearly_independent S ∧ linear_span U S = all.

Section Basis.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    UD : Div U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    @MultAssoc U UM,
    @MultLid U UM UO,
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
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM
}.

Theorem zero_linearly_dependent : ∀ (S : V → Prop), S 0 → linearly_dependent S.
    intros S S0 ind.
    pose (l := (1, 0) :: list_end).
    assert (linear_combination_set l) as l_comb.
    {
        cbn.
        rewrite not_false.
        split; exact true.
    }
    apply not_trivial.
    apply (ind [l|l_comb]).
    -   intros v [α v_in].
        cbn in v_in.
        destruct v_in as [v_in|v_in]; try contradiction.
        inversion v_in.
        exact S0.
    -   cbn.
        rewrite plus_rid.
        rewrite scalar_ranni.
        reflexivity.
    -   cbn.
        exists 0.
        left.
        reflexivity.
Qed.

Theorem singleton_linearly_independent :
        ∀ v, 0 ≠ v → linearly_independent (singleton v).
    intros v v_neq [l uni] in_l eq α α_in.
    classic_contradiction α_nz.
    assert (l = (1, v) :: list_end) as l_eq.
    {
        destruct l.
        -   cbn in *.
            destruct α_in; contradiction.
        -   cbn in *.
            destruct uni as [uni1 uni2].
            assert (p = (1, v)) as p_eq.
            {
                destruct p as [β v0]; cbn in *.
                assert (v0 = v) as eq'.
                {
                    symmetry; apply in_l.
                    exists β.
                    left; reflexivity.
                }
                subst v0.
                apply f_equal2.
                2: reflexivity.
                destruct l.
                -   cbn in *.
                    destruct α_in as [u α_in].
                    destruct α_in as [α_eq|α_in].
                    2: contradiction.
                    inversion α_eq.
                    subst β u.
                    rewrite plus_rid in eq.
                    apply lscalar with (/α) in eq.
                    rewrite scalar_ranni in eq.
                    rewrite scalar_comp in eq.
                    rewrite mult_linv in eq by exact α_nz.
                    rewrite scalar_id in eq.
                    contradiction.
                -   clear - uni1 in_l.
                    destruct p as [α v0]; cbn in *.
                    assert (v0 = v) as eq.
                    {
                        symmetry; apply in_l.
                        exists α.
                        right; left.
                        reflexivity.
                    }
                    subst v0.
                    rewrite not_or in uni1.
                    contradiction (land uni1).
                    reflexivity.
            }
            subst p.
            apply f_equal2.
            1: reflexivity.
            destruct l.
            1: reflexivity.
            cbn in *.
            destruct uni2 as [uni2 uni3].
            rewrite not_or in uni1.
            exfalso; apply (land uni1).
            symmetry; apply in_l.
            exists (fst p).
            right; left.
            destruct p; reflexivity.
    }
    subst l.
    cbn in *.
    rewrite plus_rid in eq.
    rewrite scalar_id in eq.
    contradiction.
Qed.

Theorem basis_linear_combination : ∀ S, basis S →
        ∀ v, linear_combination_of S v.
    intros S S_basis v.
    rewrite <- (span_linear_combination U).
    destruct S_basis as [S_ind S_eq].
    rewrite S_eq.
    exact true.
Qed.

Definition basis_coefficients (S : V → Prop) (S_basis : basis S) (v : V)
    := linear_remove_zeros (ex_val (basis_linear_combination S S_basis v)).

Theorem basis_coefficients_combination : ∀ S S_basis v,
        v = linear_combination (basis_coefficients S S_basis v).
    intros S S_basis v.
    unfold basis_coefficients.
    rewrite_ex_val l [v_eq Sl].
    rewrite <- linear_combination_remove_zeros.
    exact v_eq.
Qed.

End Basis.
