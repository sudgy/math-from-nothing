Require Import init.

Require Export linear_base.
Require Import set.
Require Import card.

Open Scope card_scope.

#[universes(template)]
Record free_linear U V `{Zero U} := make_free {
    free_f : V → U;
    free_fin : finite (|set_type (λ x, free_f x ≠ 0)|);
}.
Arguments make_free {U V H}.
Arguments free_f {U V H}.
Arguments free_fin {U V H}.

Section LinearFree.

Context (U V : Type) `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @MultComm U UM,
    @MultAssoc U UM,
    @MultLid U UM UO,
    @Ldist U UP UM,
    @NotTrivial U UZ UO
}.

Theorem free_eq :
        ∀ (A B : free_linear U V), (∀ x, free_f A x = free_f B x) → A = B.
    intros [Af A_fin] [Bf B_fin] eq.
    apply functional_ext in eq.
    cbn in eq.
    subst.
    rewrite (proof_irrelevance A_fin B_fin).
    reflexivity.
Qed.

Let to_free_base (v : V) : (V → U) := λ x, If x = v then 1 else 0.
Lemma to_free_fin : ∀ v, finite (|set_type (λ x, to_free_base v x ≠ 0)|).
    intros v.
    replace (λ x, to_free_base v x ≠ 0) with (singleton v).
    1: apply singleton_finite.
    unfold to_free_base.
    apply antisym.
    -   intros x vx.
        case_if.
        +   rewrite neq_sym.
            exact not_trivial.
        +   unfold singleton in vx.
            symmetry in vx.
            contradiction.
    -   intros x; cbn.
        case_if.
        +   intro neq.
            rewrite e.
            reflexivity.
        +   intros contr.
            contradiction.
Qed.
Definition to_free v := make_free (to_free_base v) (to_free_fin v).

Let free_plus (A B : free_linear U V) := λ x, free_f A x + free_f B x.

Lemma free_plus_fin : ∀ A B, finite (|set_type (λ x, free_plus A B x ≠ 0)|).
    intros [f f_fin] [g g_fin].
    unfold free_plus; cbn.
    apply fin_nat_ex in f_fin as [m f_fin].
    apply fin_nat_ex in g_fin as [n g_fin].
    pose proof (nat_is_finite (m + n)) as mn_fin.
    apply (le_lt_trans2 mn_fin).
    rewrite <- nat_to_card_plus.
    rewrite f_fin, g_fin.
    clear m f_fin n g_fin mn_fin.
    unfold plus at 2, le; equiv_simpl.
    assert (∀ x, f x + g x ≠ 0 → f x ≠ 0 ∨ g x ≠ 0) as fg_neq.
    {
        intros x eq.
        classic_case (f x = 0) as [f_eq|neq]; try (left; exact neq).
        right.
        intro g_eq.
        rewrite f_eq, g_eq in eq.
        rewrite plus_lid in eq.
        contradiction.
    }
    exists (λ x, match (or_to_strong _ _ (fg_neq [x|] [|x])) with
        | strong_or_left  H => inl [[x|]|H]
        | strong_or_right H => inr [[x|]|H]
        end).
    intros a b eq.
    destruct (or_to_strong _) as [a_neq|a_neq];
    destruct (or_to_strong _) as [b_neq|b_neq].
    -   inversion eq as [eq2].
        apply set_type_eq.
        exact eq2.
    -   inversion eq.
    -   inversion eq.
    -   inversion eq as [eq2].
        apply set_type_eq.
        exact eq2.
Qed.

Instance free_plus_class : Plus (free_linear U V) := {
    plus A B := make_free (free_plus A B) (free_plus_fin A B)
}.

Lemma free_plus_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
    intros [af a_fin] [bf b_fin] [cf c_fin].
    unfold plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply plus_assoc.
Qed.
Instance free_plus_assoc_class : PlusAssoc _ := {
    plus_assoc := free_plus_assoc
}.

Lemma free_plus_comm : ∀ a b, a + b = b + a.
    intros [af a_fin] [bf b_fin].
    unfold plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply plus_comm.
Qed.
Instance free_plus_comm_class : PlusComm _ := {
    plus_comm := free_plus_comm
}.

Lemma free_zero_fin : finite (|set_type (λ x : V, (zero (U := U)) ≠ 0)|).
    replace (λ x, (zero (U := U)) ≠ 0) with (empty (U := V)).
    {
        rewrite <- empty_set_size.
        apply nat_is_finite.
    }
    symmetry; apply not_ex_empty.
    intros x.
    rewrite not_not.
    reflexivity.
Qed.
Instance free_zero : Zero (free_linear U V) := {
    zero := make_free (λ x, 0) free_zero_fin
}.

Lemma free_plus_lid : ∀ a, 0 + a = a.
    intros [af a_fin].
    unfold zero, plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply plus_lid.
Qed.
Instance free_plus_lid_class : PlusLid _ := {
    plus_lid := free_plus_lid
}.

Lemma free_neg_fin :
        ∀ A : free_linear U V, finite (|set_type (λ x, -(free_f A x) ≠ 0)|).
    intros [f f_fin]; cbn.
    apply (le_lt_trans2 f_fin).
    unfold le; equiv_simpl.
    assert (∀ x, -f x ≠ 0 → f x ≠ 0) as x_in.
    {
        intros x neq eq.
        rewrite eq in neq.
        rewrite neg_zero in neq.
        contradiction.
    }
    exists (λ x, [[x|] | x_in [x|] [|x]]).
    intros a b eq.
    inversion eq as [eq2].
    apply set_type_eq.
    exact eq2.
Qed.
Instance free_neg : Neg (free_linear U V) := {
    neg A := make_free (λ x, -free_f A x) (free_neg_fin A)
}.

Lemma free_plus_linv : ∀ a, -a + a = 0.
    intros [af a_fin].
    unfold neg, plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply plus_linv.
Qed.
Instance free_plus_linv_class : PlusLinv _ := {
    plus_linv := free_plus_linv
}.

Lemma free_scalar_fin : ∀ (a : U) (A : free_linear U V),
        finite (|set_type (λ x, a * free_f A x ≠ 0)|).
    intros a [f f_fin]; cbn.
    apply (le_lt_trans2 f_fin).
    unfold le; equiv_simpl.
    assert (∀ x, a * f x ≠ 0 → f x ≠ 0) as x_ex.
    {
        intros x neq eq.
        rewrite eq in neq.
        rewrite mult_ranni in neq.
        contradiction.
    }
    exists (λ x, [[x|] | x_ex [x|] [|x]]).
    intros x y eq.
    inversion eq as [eq2].
    apply set_type_eq.
    exact eq2.
Qed.
Instance free_scalar : ScalarMult U (free_linear U V) := {
    scalar_mult a B := make_free (λ x, a * free_f B x) (free_scalar_fin a B)
}.

Lemma free_scalar_comp : ∀ a b v, a · (b · v) = (a * b) · v.
    intros a b [f f_fin].
    unfold scalar_mult; cbn.
    apply free_eq; cbn.
    intros x.
    apply mult_assoc.
Qed.
Instance free_scalar_comp_class : ScalarComp _ _ := {
    scalar_comp := free_scalar_comp
}.

Lemma free_scalar_id : ∀ v, 1 · v = v.
    intros [f f_fin].
    unfold scalar_mult; cbn.
    apply free_eq; cbn.
    intros x.
    apply mult_lid.
Qed.
Instance free_scalar_id_class : ScalarId _ _ := {
    scalar_id := free_scalar_id
}.

Lemma free_scalar_ldist : ∀ a u v, a · (u + v) = a · u + a · v.
    intros a [uf uf_fin] [vf vf_fin].
    unfold scalar_mult, plus; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply ldist.
Qed.
Instance free_scalar_ldist_class : ScalarLdist _ _ := {
    scalar_ldist := free_scalar_ldist
}.

Lemma free_scalar_rdist : ∀ a b v, (a + b) · v = a · v + b · v.
    intros a b [f f_fin].
    unfold scalar_mult, plus at 2; cbn.
    unfold free_plus.
    apply free_eq; cbn.
    intros x.
    apply rdist.
Qed.
Instance free_scalar_rdist_class : ScalarRdist _ _ := {
    scalar_rdist := free_scalar_rdist
}.

End LinearFree.
