Require Import init.

Require Export plus_group.
Require Import plus_sum.
Require Export mult_ring.
Require Import list.

#[universes(template)]
Class ScalarMult U V := {
    scalar_mult : U → V → V
}.
Infix "·" := scalar_mult : algebra_scope.
Arguments scalar_mult : simpl never.

Class ScalarComp U V `{Mult U, ScalarMult U V} := {
    scalar_comp : ∀ a b v, a · (b · v) = (a * b) · v
}.

Class ScalarId U V `{One U, ScalarMult U V} := {
    scalar_id : ∀ v, 1 · v = v
}.

Class ScalarLdist U V `{Plus V, ScalarMult U V} := {
    scalar_ldist : ∀ a u v, a · (u + v) = a · u + a · v
}.
Class ScalarRdist U V `{Plus U, Plus V, ScalarMult U V} := {
    scalar_rdist : ∀ a b v, (a + b) · v = a · v + b · v
}.

Class ScalarLMult U V `{Mult V, ScalarMult U V} := {
    scalar_lmult : ∀ a u v, (a · u) * v = a · (u * v)
}.
Class ScalarRMult U V `{Mult V, ScalarMult U V} := {
    scalar_rmult : ∀ a u v, u * (a · v) = a · (u * v)
}.

Definition linear_combination {U V} `{Zero V, Plus V, ScalarMult U V}
    (l1 : list U) (l2 : list V) (H : list_size l1 = list_size l2)
    := list_sum (list_image (list_zip l1 l2) (λ x, fst x · snd x)).

(* begin hide *)
Section LinearBase.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM
}.
(* end hide *)
Theorem lscalar : ∀ {u v} a, u = v → a · u = a · v.
    intros u v a eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem rscalar : ∀ {a b} v, a = b → a · v = b · v.
    intros u v a eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem lrscalar : ∀ {a b u v}, a = b → u = v → a · u = b · v.
    intros a b u v eq1 eq2.
    apply lscalar with b in eq2.
    apply rscalar with u in eq1.
    rewrite eq1, <- eq2.
    reflexivity.
Qed.

Theorem scalar_lanni : ∀ v, 0 · v = 0.
    intros v.
    assert (0 · v = 0 · v) as eq by reflexivity.
    rewrite <- (plus_lid 0) in eq at 1.
    rewrite scalar_rdist in eq.
    apply plus_0_a_ab_b in eq.
    symmetry; exact eq.
Qed.

Theorem scalar_ranni : ∀ a, a · 0 = 0.
    intros a.
    assert (a · 0 = a · 0) as eq by reflexivity.
    rewrite <- (plus_lid 0) in eq at 1.
    rewrite scalar_ldist in eq.
    apply plus_0_a_ab_b in eq.
    symmetry; exact eq.
Qed.

Theorem scalar_lneg : ∀ a b, -a · b = -(a · b).
    intros a b.
    apply plus_lcancel with (a · b).
    rewrite <- scalar_rdist.
    do 2 rewrite plus_rinv.
    apply scalar_lanni.
Qed.

Theorem scalar_rneg : ∀ a b, a · -b = -(a · b).
    intros a b.
    apply plus_lcancel with (a · b).
    rewrite <- scalar_ldist.
    do 2 rewrite plus_rinv.
    apply scalar_ranni.
Qed.

Theorem scalar_neg_one : ∀ a, (-(1)) · a = -a.
    intros a.
    rewrite scalar_lneg.
    rewrite scalar_id.
    reflexivity.
Qed.

(* begin hide *)
End LinearBase.
(* end hide *)
