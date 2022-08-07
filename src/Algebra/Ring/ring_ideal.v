Require Import init.

Require Export plus_group.
Require Export mult_ring.

Require Import set.
Require Import unordered_list.

#[universes(template)]
Record Ideal U `{Plus U, Mult U} := make_ideal {
    ideal_set : U → Prop;
    ideal_nempty : ∃ a, ideal_set a;
    ideal_plus : ∀ a b, ideal_set a → ideal_set b → ideal_set (a + b);
    ideal_lmult : ∀ a b, ideal_set b → ideal_set (a * b);
    ideal_rmult : ∀ a b, ideal_set a → ideal_set (a * b);
}.
Arguments make_ideal {U H H0}.
Arguments ideal_set {U H H0}.
Arguments ideal_nempty {U H H0}.
Arguments ideal_plus {U H H0}.
Arguments ideal_lmult {U H H0}.
Arguments ideal_rmult {U H H0}.

Theorem ideal_eq_set {U} `{Plus U, Mult U} : ∀ I J : Ideal U,
    ideal_set I = ideal_set J → I = J.
Proof.
    intros [I_set I_nempty I_plus I_lmult I_rmult]
           [J_set J_nempty J_plus J_lmult J_rmult] eq.
    cbn in eq.
    subst J_set.
    rewrite (proof_irrelevance J_nempty I_nempty).
    rewrite (proof_irrelevance J_plus I_plus).
    rewrite (proof_irrelevance J_lmult I_lmult).
    rewrite (proof_irrelevance J_rmult I_rmult).
    reflexivity.
Qed.

Theorem ideal_eq {U} `{Plus U, Mult U} : ∀ I J : Ideal U,
    (∀ x, ideal_set I x ↔ ideal_set J x) → I = J.
Proof.
    intros I J eq.
    apply ideal_eq_set.
    apply predicate_ext.
    exact eq.
Qed.

(* begin hide *)
Section RingIdeal.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    @Ldist U UP UM,
    @Rdist U UP UM,
    @MultAssoc U UM,
    @MultComm U UM,
    @MultLid U UM UO,
    @MultRid U UM UO
}.

(* end hide *)
Variable I : Ideal U.

Theorem ideal_neg : ∀ a, ideal_set I a → ideal_set I (-a).
Proof.
    intros a a_in.
    rewrite <- mult_neg_one.
    apply ideal_lmult.
    exact a_in.
Qed.

Theorem ideal_zero : ideal_set I 0.
Proof.
    pose proof (ideal_nempty I) as [a a_in].
    rewrite <- (plus_linv a).
    apply ideal_plus.
    1: apply ideal_neg.
    all: exact a_in.
Qed.

Let ideal_eq a b := ideal_set I (a - b).
Local Infix "~" := ideal_eq : algebra_scope.

Lemma ideal_eq_reflexive : ∀ a, a ~ a.
Proof.
    intros a.
    unfold ideal_eq.
    rewrite plus_rinv.
    apply ideal_zero.
Qed.
Instance ideal_eq_reflexive_class : Reflexive _ := {
    refl := ideal_eq_reflexive
}.

Lemma ideal_eq_symmetric : ∀ a b, a ~ b → b ~ a.
Proof.
    unfold ideal_eq.
    intros a b ab.
    apply ideal_neg in ab.
    rewrite neg_plus in ab.
    rewrite neg_neg in ab.
    rewrite plus_comm in ab.
    exact ab.
Qed.
Instance ideal_eq_symmetric_class : Symmetric _ := {
    sym := ideal_eq_symmetric
}.

Lemma ideal_eq_transitive : ∀ a b c, a ~ b → b ~ c → a ~ c.
Proof.
    unfold ideal_eq.
    intros a b c ab bc.
    pose proof (ideal_plus I _ _ ab bc) as eq.
    rewrite plus_assoc in eq.
    rewrite plus_rlinv in eq.
    exact eq.
Qed.
Instance ideal_eq_transitive_class : Transitive _ := {
    trans := ideal_eq_transitive
}.

Definition ideal_equiv := make_equiv _ ideal_eq_reflexive_class
    ideal_eq_symmetric_class ideal_eq_transitive_class.

Definition quotient_ring := equiv_type ideal_equiv.
Definition to_qring a := to_equiv_type ideal_equiv a.

(* begin show *)
Local Infix "~" := (eq_equal ideal_equiv).
(* end show *)

Lemma qring_plus_wd : ∀ a b c d, a ~ b → c ~ d → a + c ~ b + d.
Proof.
    cbn; unfold ideal_eq.
    intros a b c d ab cd.
    rewrite neg_plus.
    rewrite <- plus_assoc.
    rewrite (plus_assoc c).
    rewrite (plus_comm c).
    do 2 rewrite plus_assoc.
    rewrite <- plus_assoc.
    apply ideal_plus; assumption.
Qed.

Instance quotient_ring_plus : Plus quotient_ring := {
    plus := binary_self_op qring_plus_wd
}.

Program Instance quotient_ring_plus_assoc : PlusAssoc quotient_ring.
Next Obligation.
    equiv_get_value a b c.
    unfold plus; equiv_simpl.
    rewrite plus_assoc.
    reflexivity.
Qed.

Program Instance quotient_ring_plus_comm : PlusComm quotient_ring.
Next Obligation.
    equiv_get_value a b.
    unfold plus; equiv_simpl.
    rewrite plus_comm.
    reflexivity.
Qed.

Instance quotient_ring_zero : Zero quotient_ring := {
    zero := to_equiv_type ideal_equiv 0
}.

Program Instance quotient_ring_plus_lid : PlusLid quotient_ring.
Next Obligation.
    equiv_get_value a.
    unfold zero, plus; equiv_simpl.
    rewrite plus_lid.
    reflexivity.
Qed.

Lemma qring_neg_wd : ∀ a b, a ~ b → -a ~ -b.
Proof.
    cbn; unfold ideal_eq.
    intros a b eq.
    rewrite <- neg_plus.
    apply ideal_neg.
    exact eq.
Qed.
Instance quotient_ring_neg : Neg quotient_ring := {
    neg := unary_self_op qring_neg_wd
}.

Program Instance quotient_ring_plus_linv : PlusLinv quotient_ring.
Next Obligation.
    equiv_get_value a.
    unfold plus, neg, zero; equiv_simpl.
    rewrite plus_linv.
    reflexivity.
Qed.

Lemma qring_mult_wd : ∀ a b c d, a ~ b → c ~ d → a * c ~ b * d.
Proof.
    cbn; unfold ideal_eq.
    intros a b c d ab cd.
    rewrite <- (plus_llinv (-(b * d)) (b * c)).
    rewrite plus_assoc.
    apply ideal_plus.
    -   rewrite <- mult_lneg.
        rewrite <- rdist.
        apply ideal_rmult.
        exact ab.
    -   rewrite <- mult_rneg.
        rewrite <- ldist.
        apply ideal_lmult.
        exact cd.
Qed.

Instance quotient_ring_mult : Mult quotient_ring := {
    mult := binary_self_op qring_mult_wd
}.

Program Instance quotient_ring_ldist : Ldist quotient_ring.
Next Obligation.
    equiv_get_value a b c.
    unfold plus, mult; equiv_simpl.
    rewrite ldist.
    reflexivity.
Qed.

Program Instance quotient_ring_rdist : Rdist quotient_ring.
Next Obligation.
    equiv_get_value a b c.
    unfold plus, mult; equiv_simpl.
    rewrite rdist.
    reflexivity.
Qed.

Program Instance quotient_ring_mult_assoc : MultAssoc quotient_ring.
Next Obligation.
    equiv_get_value a b c.
    unfold mult; equiv_simpl.
    rewrite mult_assoc.
    reflexivity.
Qed.

Program Instance quotient_ring_mult_comm : MultComm quotient_ring.
Next Obligation.
    equiv_get_value a b.
    unfold mult; equiv_simpl.
    rewrite mult_comm.
    reflexivity.
Qed.

Instance quotient_ring_one : One quotient_ring := {
    one := to_equiv_type ideal_equiv 1
}.

Program Instance quotient_ring_mult_lid : MultLid quotient_ring.
Next Obligation.
    equiv_get_value a.
    unfold one, mult; equiv_simpl.
    rewrite mult_lid.
    reflexivity.
Qed.

Program Instance quotient_ring_mult_rid : MultRid quotient_ring.
Next Obligation.
    equiv_get_value a.
    unfold one, mult; equiv_simpl.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem to_qring_plus : ∀ a b, to_qring (a + b) = to_qring a + to_qring b.
Proof.
    intros a b.
    unfold plus at 2, to_qring; equiv_simpl.
    apply ideal_eq_reflexive.
Qed.

Theorem to_qring_zero : to_qring 0 = 0.
Proof.
    reflexivity.
Qed.

Theorem to_qring_neg : ∀ a, to_qring (-a) = -to_qring a.
Proof.
    intros a.
    unfold neg at 2, to_qring; equiv_simpl.
    apply ideal_eq_reflexive.
Qed.

Theorem to_qring_mult : ∀ a b, to_qring (a * b) = to_qring a * to_qring b.
Proof.
    intros a b.
    unfold mult at 2, to_qring; equiv_simpl.
    apply ideal_eq_reflexive.
Qed.

Theorem to_qring_one : to_qring 1 = 1.
Proof.
    reflexivity.
Qed.

(* begin hide *)
End RingIdeal.

Section IdealGenerated.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UM : Mult U,
    UO : One U,
    @PlusAssoc U UP,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    @Ldist U UP UM,
    @Rdist U UP UM,
    @MultAssoc U UM,
    @MultLid U UM UO,
    @MultRid U UM UO
}.

(* end hide *)
Variable S : U → Prop.

Definition ideal_generated_by_set x := ∃ l : ulist ((U * U) * set_type S),
    x = ulist_sum (ulist_image l (λ p, fst (fst p) * [snd p|] * snd (fst p))).

Lemma ideal_generated_by_nempty : ∃ x, ideal_generated_by_set x.
Proof.
    exists 0.
    exists ulist_end.
    rewrite ulist_image_end, ulist_sum_end.
    reflexivity.
Qed.

Lemma ideal_generated_by_plus : ∀ a b,
    ideal_generated_by_set a → ideal_generated_by_set b →
    ideal_generated_by_set (a + b).
Proof.
    intros a b [al al_eq] [bl bl_eq]; subst a b.
    exists (al +++ bl).
    rewrite ulist_image_conc, ulist_sum_plus.
    reflexivity.
Qed.

Lemma ideal_generated_by_lmult : ∀ a b,
    ideal_generated_by_set b → ideal_generated_by_set (a * b).
Proof.
    intros a b [l l_eq]; subst b.
    exists (ulist_image l (λ p, ((a * fst (fst p), snd (fst p)), snd p))).
    rewrite ulist_image_comp.
    cbn.
    induction l as [|b l] using ulist_induction.
    -   do 2 rewrite ulist_image_end, ulist_sum_end.
        apply mult_ranni.
    -   do 2 rewrite ulist_image_add, ulist_sum_add.
        rewrite ldist.
        rewrite IHl.
        apply rplus.
        do 2 rewrite mult_assoc.
        reflexivity.
Qed.

Lemma ideal_generated_by_rmult : ∀ a b,
    ideal_generated_by_set a → ideal_generated_by_set (a * b).
Proof.
    intros a b [l l_eq]; subst a.
    exists (ulist_image l (λ p, ((fst (fst p), snd (fst p) * b), snd p))).
    rewrite ulist_image_comp.
    cbn.
    induction l as [|a l] using ulist_induction.
    -   do 2 rewrite ulist_image_end, ulist_sum_end.
        apply mult_lanni.
    -   do 2 rewrite ulist_image_add, ulist_sum_add.
        rewrite rdist.
        rewrite IHl.
        apply rplus.
        rewrite mult_assoc.
        reflexivity.
Qed.

Definition ideal_generated_by := make_ideal
    ideal_generated_by_set
    ideal_generated_by_nempty
    ideal_generated_by_plus
    ideal_generated_by_lmult
    ideal_generated_by_rmult.
(* begin hide *)

End IdealGenerated.
(* end hide *)
