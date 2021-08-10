Require Import init.

Require Export linear_base.
Require Import set.

#[universes(template)]
Record Subspace U V `{Plus V, Zero V, Neg V, ScalarMult U V} := make_subspace {
    subspace_set : V → Prop;
    subspace_zero : subspace_set 0;
    subspace_plus : ∀ a b, subspace_set a → subspace_set b → subspace_set (a+b);
    (*subspace_neg : ∀ v, subspace_set v → subspace_set (-v);*)
    subspace_scalar : ∀ a v, subspace_set v → subspace_set (a · v);
}.
Arguments make_subspace {U V H H0 H1 H2}.
Arguments subspace_set {U V H H0 H1 H2}.
Arguments subspace_zero {U V H H0 H1 H2}.
Arguments subspace_plus {U V H H0 H1 H2}.
(*Arguments subspace_neg {U V H H0 H1 H2}.*)
Arguments subspace_scalar {U V H H0 H1 H2}.

Section QuotientSpace.

Context {U V} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,

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
Variable S : Subspace U V.

Let subspace_eq a b := subspace_set S (a - b).
(* Declaring this in algebra_scope is a bit of a hack to allow us to redefine it
 * later.
 *)
Local Infix "~" := subspace_eq : algebra_scope.

Lemma subspace_eq_reflexive : ∀ a, a ~ a.
    intros a.
    unfold subspace_eq.
    rewrite plus_rinv.
    apply subspace_zero.
Qed.
Instance subspace_eq_reflexive_class : Reflexive _ := {
    refl := subspace_eq_reflexive
}.

Theorem subspace_neg : ∀ v, subspace_set S v → subspace_set S (-v).
    intros v v_in.
    rewrite <- (scalar_neg_one (U := U)).
    apply subspace_scalar.
    exact v_in.
Qed.

Lemma subspace_eq_symmetric : ∀ a b, a ~ b → b ~ a.
    unfold subspace_eq.
    intros a b ab.
    apply subspace_neg in ab.
    rewrite neg_plus in ab.
    rewrite neg_neg in ab.
    rewrite plus_comm in ab.
    exact ab.
Qed.
Instance subspace_eq_symmetric_class : Symmetric _ := {
    sym := subspace_eq_symmetric
}.

Lemma subspace_eq_transitive : ∀ a b c, a ~ b → b ~ c → a ~ c.
    unfold subspace_eq.
    intros a b c ab bc.
    pose proof (subspace_plus S _ _ ab bc) as eq.
    rewrite plus_assoc in eq.
    rewrite plus_rlinv in eq.
    exact eq.
Qed.
Instance subspace_eq_transitive_class : Transitive _ := {
    trans := subspace_eq_transitive
}.

Definition subspace_equiv := make_equiv _ subspace_eq_reflexive_class
    subspace_eq_symmetric_class subspace_eq_transitive_class.

Definition quotient_space := equiv_type subspace_equiv.

Local Infix "~" := (eq_equal subspace_equiv).

Lemma qspace_plus_wd : ∀ a b c d, a ~ b → c ~ d → a + c ~ b + d.
    unfold eq_equal; cbn.
    unfold subspace_eq.
    intros a b c d ab cd.
    pose proof (subspace_plus S _ _ ab cd) as eq.
    rewrite <- plus_assoc in eq.
    rewrite (plus_assoc (-b)) in eq.
    rewrite (plus_comm (-b)) in eq.
    rewrite <- plus_assoc in eq.
    rewrite plus_assoc in eq.
    rewrite <- neg_plus in eq.
    exact eq.
Qed.

Instance quotient_space_plus : Plus quotient_space := {
    plus := binary_self_op qspace_plus_wd
}.

Lemma qspace_plus_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
    intros a b c.
    equiv_get_value a b c.
    unfold plus; equiv_simpl.
    apply f_equal.
    apply plus_assoc.
Qed.
Instance quotient_space_plus_assoc : PlusAssoc quotient_space := {
    plus_assoc := qspace_plus_assoc
}.

Lemma qspace_plus_comm : ∀ a b, a + b = b + a.
    intros a b.
    equiv_get_value a b.
    unfold plus; equiv_simpl.
    apply f_equal.
    apply plus_comm.
Qed.
Instance quotient_space_plus_comm : PlusComm quotient_space := {
    plus_comm := qspace_plus_comm
}.

Instance quotient_space_zero : Zero quotient_space := {
    zero := to_equiv_type subspace_equiv 0
}.

Lemma qspace_plus_lid : ∀ a, 0 + a = a.
    intros a.
    equiv_get_value a.
    unfold zero, plus; equiv_simpl.
    apply f_equal.
    apply plus_lid.
Qed.
Instance quotient_space_plus_lid : PlusLid quotient_space := {
    plus_lid := qspace_plus_lid
}.

Lemma qspace_neg_wd : ∀ a b, a ~ b → -a ~ -b.
    unfold eq_equal; cbn.
    unfold subspace_eq.
    intros a b eq.
    apply subspace_neg in eq.
    rewrite neg_plus in eq.
    exact eq.
Qed.
Instance quotient_space_neg : Neg quotient_space := {
    neg := unary_self_op qspace_neg_wd
}.

Lemma qspace_plus_linv : ∀ a, -a + a = 0.
    intros a.
    equiv_get_value a.
    unfold neg, plus, zero; equiv_simpl.
    rewrite plus_linv.
    reflexivity.
Qed.
Instance quotient_space_plus_linv : PlusLinv quotient_space := {
    plus_linv := qspace_plus_linv
}.

Lemma qspace_scalar_wd : ∀ u v c, u ~ v → c · u ~ c · v.
    unfold eq_equal; cbn.
    unfold subspace_eq.
    intros u v c eq.
    apply (subspace_scalar S c) in eq.
    rewrite scalar_ldist in eq.
    rewrite scalar_rneg in eq.
    exact eq.
Qed.
Instance quotient_space_scalar_mult : ScalarMult U quotient_space := {
    scalar_mult := binary_rself_op qspace_scalar_wd
}.

Lemma qspace_scalar_comp : ∀ a b v, a · (b · v) = (a * b) · v.
    intros a b v.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    rewrite scalar_comp.
    reflexivity.
Qed.
Instance quotient_space_scalar_comp : ScalarComp _ _ := {
    scalar_comp := qspace_scalar_comp
}.

Lemma qspace_scalar_id : ∀ v, 1 · v = v.
    intros v.
    equiv_get_value v.
    unfold scalar_mult; equiv_simpl.
    rewrite scalar_id.
    reflexivity.
Qed.
Instance quotient_space_scalar_id : ScalarId _ _ := {
    scalar_id := qspace_scalar_id
}.

Lemma qspace_scalar_ldist : ∀ a u v, a · (u + v) = a · u + a · v.
    intros a u v.
    equiv_get_value u v.
    unfold scalar_mult, plus; equiv_simpl.
    rewrite scalar_ldist.
    reflexivity.
Qed.
Instance quotient_space_scalar_ldist : ScalarLdist _ _ := {
    scalar_ldist := qspace_scalar_ldist
}.

Lemma qspace_scalar_rdist : ∀ a b v, (a + b) · v = a · v + b · v.
    intros a b v.
    equiv_get_value v.
    unfold scalar_mult, plus at 2; equiv_simpl.
    rewrite scalar_rdist.
    reflexivity.
Qed.
Instance quotient_space_scalar_rdist : ScalarRdist _ _ := {
    scalar_rdist := qspace_scalar_rdist
}.

End QuotientSpace.
