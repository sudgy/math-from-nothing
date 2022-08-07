Require Import init.

Require Export linear_base.
Require Import set.
Require Import unordered_list.

#[universes(template)]
Record Subspace U V `{Plus V, Zero V, ScalarMult U V} := make_subspace {
    subspace_set : V → Prop;
    subspace_zero : subspace_set 0;
    subspace_plus : ∀ a b, subspace_set a → subspace_set b → subspace_set (a+b);
    subspace_scalar : ∀ a v, subspace_set v → subspace_set (a · v);
}.
Arguments make_subspace {U V H H0 H1}.
Arguments subspace_set {U V H H0 H1}.
Arguments subspace_zero {U V H H0 H1}.
Arguments subspace_plus {U V H H0 H1}.
Arguments subspace_scalar {U V H H0 H1}.

(* begin hide *)
Section Subspace.

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

(* end hide *)
Theorem subspace_eq : ∀ S1 S2 : Subspace U V, subspace_set S1 = subspace_set S2
    → S1 = S2.
Proof.
    intros [S1 S1_zero S1_plus S1_scalar] [S2 S2_zero S2_plus S2_scalar] eq.
    cbn in eq.
    subst S2.
    rewrite (proof_irrelevance S2_zero S1_zero).
    rewrite (proof_irrelevance S2_plus S1_plus).
    rewrite (proof_irrelevance S2_scalar S1_scalar).
    reflexivity.
Qed.

Variable S : Subspace U V.

Theorem subspace_neg : ∀ v, subspace_set S v → subspace_set S (-v).
Proof.
    intros v v_in.
    rewrite <- scalar_neg_one.
    apply subspace_scalar.
    exact v_in.
Qed.

Instance subspace_plus_class : Plus (set_type (subspace_set S)) := {
    plus a b := [[a|] + [b|] | subspace_plus S [a|] [b|] [|a] [|b]]
}.
Instance subspace_zero_class : Zero (set_type (subspace_set S)) := {
    zero := [0|subspace_zero S]
}.
Instance subspace_neg_class : Neg (set_type (subspace_set S)) := {
    neg a := [-[a|] | subspace_neg [a|] [|a]]
}.
Program Instance subspace_plus_comm : PlusComm (set_type (subspace_set S)).
Next Obligation.
    apply set_type_eq; cbn.
    apply plus_comm.
Qed.
Program Instance subspace_plus_assoc : PlusAssoc (set_type (subspace_set S)).
Next Obligation.
    apply set_type_eq; cbn.
    apply plus_assoc.
Qed.
Program Instance subspace_plus_lid : PlusLid (set_type (subspace_set S)).
Next Obligation.
    apply set_type_eq; cbn.
    apply plus_lid.
Qed.
Program Instance subspace_plus_linv : PlusLinv (set_type (subspace_set S)).
Next Obligation.
    apply set_type_eq; cbn.
    apply plus_linv.
Qed.
Instance subspace_scalar_class : ScalarMult U (set_type (subspace_set S)) := {
    scalar_mult a v := [a · [v|] | subspace_scalar S a [v|] [|v]]
}.
Program Instance subspace_scalar_comp : ScalarComp U (set_type (subspace_set S)).
Next Obligation.
    apply set_type_eq; cbn.
    apply scalar_comp.
Qed.
Program Instance subspace_scalar_id : ScalarId U (set_type (subspace_set S)).
Next Obligation.
    apply set_type_eq; cbn.
    apply scalar_id.
Qed.
Program Instance subspace_scalar_ldist : ScalarLdist U (set_type (subspace_set S)).
Next Obligation.
    apply set_type_eq; cbn.
    apply scalar_ldist.
Qed.
Program Instance subspace_scalar_rdist : ScalarRdist U (set_type (subspace_set S)).
Next Obligation.
    apply set_type_eq; cbn.
    apply scalar_rdist.
Qed.

(* begin hide *)
End Subspace.

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
(* end hide *)
Variable S : Subspace U V.

Theorem subspace_linear_combination :
    ∀ l, linear_list_in (subspace_set S) l →
    subspace_set S (linear_combination l).
Proof.
    intros [l l_unique] Sl.
    unfold linear_list_in in Sl.
    unfold linear_combination; cbn in *.
    clear l_unique.
    induction l using ulist_induction.
    -   cbn.
        rewrite ulist_image_end, ulist_sum_end.
        apply subspace_zero.
    -   rewrite ulist_image_add, ulist_sum_add.
        rewrite ulist_prop_add in Sl.
        apply subspace_plus.
        +   apply subspace_scalar.
            apply Sl.
        +   apply IHl.
            apply Sl.
Qed.

Let subspace_eq a b := subspace_set S (a - b).
(** Declaring this in algebra_scope is a bit of a hack to allow us to redefine
it later.
*)
(* begin show *)
Local Infix "~" := subspace_eq : algebra_scope.
(* end show *)

Lemma subspace_eq_reflexive : ∀ a, a ~ a.
Proof.
    intros a.
    unfold subspace_eq.
    rewrite plus_rinv.
    apply subspace_zero.
Qed.
Instance subspace_eq_reflexive_class : Reflexive _ := {
    refl := subspace_eq_reflexive
}.

Lemma subspace_eq_symmetric : ∀ a b, a ~ b → b ~ a.
Proof.
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
Proof.
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

(* begin show *)
Local Infix "~" := (eq_equal subspace_equiv).
(* end show *)

Lemma qspace_plus_wd : ∀ a b c d, a ~ b → c ~ d → a + c ~ b + d.
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
    intros a b v.
    equiv_get_value v.
    unfold scalar_mult, plus at 2; equiv_simpl.
    rewrite scalar_rdist.
    reflexivity.
Qed.
Instance quotient_space_scalar_rdist : ScalarRdist _ _ := {
    scalar_rdist := qspace_scalar_rdist
}.
(* begin hide *)

End QuotientSpace.
(* end hide *)
