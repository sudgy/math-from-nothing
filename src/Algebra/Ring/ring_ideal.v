Require Import init.

Require Export plus_group.
Require Export ring_category.

Require Import set.
Require Import unordered_list.

Record Ideal (U : Ring) := make_ideal {
    ideal_set :> U → Prop;
    ideal_nempty : ∃ a, ideal_set a;
    ideal_plus : ∀ a b, ideal_set a → ideal_set b → ideal_set (a + b);
    ideal_lmult : ∀ a b, ideal_set b → ideal_set (a * b);
    ideal_rmult : ∀ a b, ideal_set a → ideal_set (a * b);
}.
Arguments make_ideal {U}.
Arguments ideal_set {U}.
Arguments ideal_nempty {U}.
Arguments ideal_plus {U}.
Arguments ideal_lmult {U}.
Arguments ideal_rmult {U}.

Theorem ideal_eq_set {U} : ∀ I J : Ideal U, ideal_set I = ideal_set J → I = J.
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

Theorem ideal_eq {U} : ∀ I J : Ideal U,
    (∀ x, I x ↔ J x) → I = J.
Proof.
    intros I J eq.
    apply ideal_eq_set.
    apply predicate_ext.
    exact eq.
Qed.

Section RingIdeal.

Context {U} (I : Ideal U).

Theorem ideal_neg : ∀ a, I a → I (-a).
Proof.
    intros a a_in.
    rewrite <- mult_neg_one.
    apply ideal_lmult.
    exact a_in.
Qed.

Lemma ideal_minus : ∀ a b, I (a - b) → I (b - a).
Proof.
    intros a b ab.
    rewrite <- (neg_neg b).
    rewrite <- neg_plus_group.
    apply ideal_neg.
    exact ab.
Qed.

Theorem ideal_zero : I 0.
Proof.
    pose proof (ideal_nempty I) as [a a_in].
    rewrite <- (mult_lanni a).
    apply ideal_lmult.
    exact a_in.
Qed.

Let ideal_eq a b := I (a - b).
Local Infix "~" := ideal_eq : algebra_scope.

Local Instance ideal_eq_reflexive_class : Reflexive ideal_eq.
Proof.
    split.
    intros a.
    unfold ideal_eq.
    rewrite plus_rinv.
    apply ideal_zero.
Qed.

Local Instance ideal_eq_symmetric_class : Symmetric ideal_eq.
Proof.
    split.
    unfold ideal_eq.
    intros a b ab.
    apply ideal_neg in ab.
    rewrite neg_plus in ab.
    rewrite neg_neg in ab.
    rewrite plus_comm in ab.
    exact ab.
Qed.

Local Instance ideal_eq_transitive_class : Transitive ideal_eq.
Proof.
    split.
    unfold ideal_eq.
    intros a b c ab bc.
    pose proof (ideal_plus I _ _ ab bc) as eq.
    rewrite plus_assoc in eq.
    rewrite plus_rlinv in eq.
    exact eq.
Qed.

Definition ideal_equiv := make_equiv _ ideal_eq_reflexive_class
    ideal_eq_symmetric_class ideal_eq_transitive_class.

Definition quotient_ring_type := equiv_type ideal_equiv.
Definition to_qring_type a := to_equiv ideal_equiv a.

(* begin show *)
Local Infix "~" := (eq_equal ideal_equiv).
(* end show *)

Lemma qring_plus_wd : ∀ a b c d, a ~ b → c ~ d → a + c ~ b + d.
Proof.
    cbn; unfold ideal_eq.
    intros a b c d ab cd.
    rewrite neg_plus.
    rewrite plus_4.
    apply ideal_plus; assumption.
Qed.

Local Instance quotient_ring_plus : Plus quotient_ring_type := {
    plus := binary_op (binary_self_wd qring_plus_wd)
}.

Local Instance quotient_ring_plus_assoc : PlusAssoc quotient_ring_type.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold plus; equiv_simpl.
    rewrite plus_assoc.
    reflexivity.
Qed.

Local Instance quotient_ring_plus_comm : PlusComm quotient_ring_type.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold plus; equiv_simpl.
    rewrite plus_comm.
    reflexivity.
Qed.

Local Instance quotient_ring_zero : Zero quotient_ring_type := {
    zero := to_equiv ideal_equiv 0
}.

Local Instance quotient_ring_plus_lid : PlusLid quotient_ring_type.
Proof.
    split.
    intros a.
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
Local Instance quotient_ring_neg : Neg quotient_ring_type := {
    neg := unary_op (unary_self_wd qring_neg_wd)
}.

Local Instance quotient_ring_plus_linv : PlusLinv quotient_ring_type.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold plus, neg, zero; equiv_simpl.
    rewrite plus_linv.
    reflexivity.
Qed.

Lemma qring_mult_wd : ∀ a b c d, a ~ b → c ~ d → a * c ~ b * d.
Proof.
    cbn; unfold ideal_eq.
    intros a b c d ab cd.
    apply (ideal_rmult I _ c) in ab.
    apply (ideal_lmult I b) in cd.
    pose proof (ideal_plus I _ _ ab cd) as eq.
    rewrite ldist, rdist in eq.
    rewrite mult_lneg, mult_rneg in eq.
    rewrite plus_assoc, plus_rlinv in eq.
    exact eq.
Qed.

Local Instance quotient_ring_mult : Mult quotient_ring_type := {
    mult := binary_op (binary_self_wd qring_mult_wd)
}.

Local Instance quotient_ring_ldist : Ldist quotient_ring_type.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold plus, mult; equiv_simpl.
    rewrite ldist.
    reflexivity.
Qed.

Local Instance quotient_ring_rdist : Rdist quotient_ring_type.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold plus, mult; equiv_simpl.
    rewrite rdist.
    reflexivity.
Qed.

Local Instance quotient_ring_mult_assoc : MultAssoc quotient_ring_type.
Proof.
    split.
    intros a b c.
    equiv_get_value a b c.
    unfold mult; equiv_simpl.
    rewrite mult_assoc.
    reflexivity.
Qed.

Local Instance quotient_ring_one : One quotient_ring_type := {
    one := to_equiv ideal_equiv 1
}.

Local Instance quotient_ring_mult_lid : MultLid quotient_ring_type.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold one, mult; equiv_simpl.
    rewrite mult_lid.
    reflexivity.
Qed.

Local Instance quotient_ring_mult_rid : MultRid quotient_ring_type.
Proof.
    split.
    intros a.
    equiv_get_value a.
    unfold one, mult; equiv_simpl.
    rewrite mult_rid.
    reflexivity.
Qed.

Local Instance to_qring_plus : HomomorphismPlus to_qring_type.
Proof.
    split.
    intros a b.
    unfold plus at 2, to_qring_type; equiv_simpl.
    apply refl.
Qed.

Local Instance to_qring_mult : HomomorphismMult to_qring_type.
Proof.
    split.
    intros a b.
    unfold mult at 2, to_qring_type; equiv_simpl.
    apply refl.
Qed.

Local Instance to_qring_one : HomomorphismOne to_qring_type.
Proof.
    split.
    reflexivity.
Qed.

Definition quotient_ring : Ring := make_ring quotient_ring_type
    quotient_ring_plus quotient_ring_zero quotient_ring_neg quotient_ring_mult
    _ _ _ _ _ _ _ quotient_ring_one _ _.

Definition to_qring : morphism U quotient_ring :=
    make_ring_homomorphism U quotient_ring to_qring_type
    to_qring_plus to_qring_mult to_qring_one.

Theorem to_qring_eq : ∀ x y, I (x - y) ↔ to_qring x = to_qring y.
Proof.
    intros x y.
    cbn; unfold to_qring_type.
    rewrite (equiv_eq (E := ideal_equiv)).
    reflexivity.
Qed.

Theorem to_qring_zero : ∀ x, I x ↔ 0 = to_qring x.
Proof.
    intros x.
    assert (0 = to_qring x ↔ to_qring x = 0) as eq
        by (split; intro; symmetry; assumption).
    rewrite eq.
    unfold zero; cbn.
    unfold to_qring_type; cbn.
    rewrite (equiv_eq (E := ideal_equiv)); cbn.
    unfold ideal_eq.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Theorem qring_unary_op {V} : ∀ (f : U → V) (wd : ∀ a b, a ~ b → f a = f b),
    ∀ x, unary_op wd (to_qring x) = f x.
Proof.
    intros f wd x.
    apply unary_op_eq.
Qed.

Theorem qring_binary_op {V} : ∀ (f : U → U → V)
    (wd : ∀ a b c d , a ~ b → c ~ d → f a c = f b d),
    ∀ x y, binary_op wd (to_qring x) (to_qring y) = f x y.
Proof.
    intros f wd x.
    apply binary_op_eq.
Qed.

Theorem qring_ex : ∀ x : quotient_ring, ∃ a, to_qring a = x.
Proof.
    intros x.
    equiv_get_value x.
    exists x.
    reflexivity.
Qed.

Theorem qring_f_ex : ∀ {V} (f : morphism U V), (∀ x, I x → 0 = f x) →
    ∃ g : morphism quotient_ring V, ∀ x, f x = g (to_qring x).
Proof.
    intros V f f_kern.
    assert (∀ a b, a ~ b → f a = f b) as wd.
    {
        intros a b eq.
        rewrite <- plus_0_anb_b_a.
        rewrite <- homo_neg, <- homo_plus.
        apply sym in eq.
        apply f_kern.
        exact eq.
    }
    pose (g := unary_op wd : quotient_ring → V).
    assert (g_plus : HomomorphismPlus g).
    {
        split.
        intros a b.
        equiv_get_value a b.
        unfold g, plus at 1; equiv_simpl.
        apply homo_plus.
    }
    assert (g_mult : HomomorphismMult g).
    {
        split.
        intros a b.
        equiv_get_value a b.
        unfold g, mult at 1; equiv_simpl.
        apply homo_mult.
    }
    assert (g_one : HomomorphismOne g).
    {
        split.
        unfold g, one at 1; equiv_simpl.
        apply homo_one.
    }
    exists (make_ring_homomorphism _ _ g g_plus g_mult g_one).
    intros x.
    cbn.
    unfold g; equiv_simpl.
    reflexivity.
Qed.

Definition qring_f {V} {f : morphism U V} (wd : ∀ x, I x → 0 = f x)
    := ex_val (qring_f_ex f wd).
Definition qring_f_eq {V} {f : morphism U V} {wd : ∀ x, I x → 0 = f x}
    := ex_proof (qring_f_ex f wd) : ∀ x, f x = qring_f wd (to_qring x).

End RingIdeal.

Arguments qring_f {U} {I} {V} {f}.
Arguments qring_f_eq {U} {I} {V} {f} {wd}.

Arguments quotient_ring : simpl never.
Arguments to_qring : simpl never.

Record CIdeal (U : CRing) := make_cideal {
    cideal_set :> U → Prop;
    cideal_nempty : ∃ a, cideal_set a;
    cideal_plus : ∀ a b, cideal_set a → cideal_set b → cideal_set (a + b);
    cideal_mult : ∀ a b, cideal_set a → cideal_set (a * b);
}.
Arguments make_cideal {U}.
Arguments cideal_set {U}.
Arguments cideal_nempty {U}.
Arguments cideal_plus {U}.
Arguments cideal_mult {U}.

Theorem cideal_eq_set {U} : ∀ I J : CIdeal U,
    cideal_set I = cideal_set J → I = J.
Proof.
    intros [I_set I_nempty I_plus I_mult]
           [J_set J_nempty J_plus J_mult] eq.
    cbn in eq.
    subst J_set.
    rewrite (proof_irrelevance J_nempty I_nempty).
    rewrite (proof_irrelevance J_plus I_plus).
    rewrite (proof_irrelevance J_mult I_mult).
    reflexivity.
Qed.

Theorem cideal_eq {U} : ∀ I J : CIdeal U, (∀ x, I x ↔ J x) → I = J.
Proof.
    intros I J eq.
    apply cideal_eq_set.
    apply predicate_ext.
    exact eq.
Qed.

Section CRingIdeal.

Context {U : CRing} (I : CIdeal U).

Lemma cideal_lmult : ∀ a b, I b → I (a * b).
Proof.
    intros a b.
    rewrite mult_comm.
    apply cideal_mult.
Qed.

Definition cideal_ideal : Ideal (cring_to_ring U) :=
    make_ideal I (cideal_nempty I) (cideal_plus I) cideal_lmult
    (cideal_mult I).

Lemma cideal_ideal_set : ∀ a, I a ↔ ideal_set cideal_ideal a.
Proof.
    reflexivity.
Qed.

Lemma cideal_neg : ∀ a, I a → I (-a).
Proof.
    intros a.
    do 2 rewrite cideal_ideal_set.
    apply ideal_neg.
Qed.

Lemma cideal_minus : ∀ a b, I (a - b) → I (b - a).
Proof.
    intros a b.
    do 2 rewrite cideal_ideal_set.
    apply ideal_minus.
Qed.

Lemma cideal_zero : I 0.
Proof.
    apply cideal_ideal_set.
    apply ideal_zero.
Qed.

Local Instance quotient_cring_mult_comm : MultComm (quotient_ring cideal_ideal).
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold mult.
    unfold quotient_ring; equiv_simpl.
    rewrite mult_comm.
    reflexivity.
Qed.

Definition quotient_cring : CRing := make_cring (quotient_ring cideal_ideal)
    (quotient_ring_plus cideal_ideal) (quotient_ring_zero cideal_ideal)
    (quotient_ring_neg cideal_ideal) (quotient_ring_mult cideal_ideal)
    _ _ _ _ _ _ (quotient_ring_one cideal_ideal) _ _.

Definition to_qcring : morphism U quotient_cring :=
    make_cring_homomorphism U quotient_cring (to_qring_type cideal_ideal)
    (to_qring_plus cideal_ideal) (to_qring_mult cideal_ideal)
    (to_qring_one cideal_ideal).

Theorem to_qcring_eq : ∀ x y, I (x - y) ↔ to_qcring x = to_qcring y.
Proof.
    intros x y.
    cbn; unfold to_qring_type; equiv_simpl.
    rewrite (equiv_eq (E := ideal_equiv cideal_ideal)); cbn.
    reflexivity.
Qed.

Theorem to_qcring_zero : ∀ x, I x ↔ 0 = to_qcring x.
Proof.
    intros x.
    assert (0 = to_qcring x ↔ to_qcring x = 0) as eq
        by (split; intro; symmetry; assumption).
    rewrite eq.
    unfold zero, to_qcring, to_qring_type; cbn.
    rewrite (equiv_eq (E := ideal_equiv cideal_ideal)); cbn.
    rewrite neg_zero, plus_rid.
    reflexivity.
Qed.

Local Infix "~" := (eq_equal (ideal_equiv cideal_ideal)).

Theorem qcring_unary_op {V} : ∀ (f : U → V) (wd : ∀ a b, a ~ b → f a = f b),
    ∀ x, unary_op wd (to_qcring x) = f x.
Proof.
    intros f wd x.
    apply unary_op_eq.
Qed.

Theorem qcring_binary_op {V} : ∀ (f : U → U → V)
    (wd : ∀ a b c d , a ~ b → c ~ d → f a c = f b d),
    ∀ x y, binary_op wd (to_qcring x) (to_qcring y) = f x y.
Proof.
    intros f wd x.
    apply binary_op_eq.
Qed.

Theorem qcring_ex : ∀ x : quotient_cring, ∃ a, to_qcring a = x.
Proof.
    intros x.
    equiv_get_value x.
    exists x.
    reflexivity.
Qed.

Theorem qcring_f_ex : ∀ {V} (f : morphism U V), (∀ x, I x → 0 = f x) →
    ∃ g : morphism quotient_cring V, ∀ x, f x = g (to_qcring x).
Proof.
    intros V f f_kern.
    pose proof (qring_f_ex cideal_ideal (⌈cring_to_ring⌉ f) f_kern) as [g g_eq].
    exists (make_cring_homomorphism quotient_cring V g
        (ring_homo_plus _ _ g) (ring_homo_mult _ _ g) (ring_homo_one _ _ g)).
    exact g_eq.
Qed.

Definition qcring_f {V} {f : morphism U V} (wd : ∀ x, I x → 0 = f x)
    := ex_val (qcring_f_ex f wd).
Definition qcring_f_eq {V} {f : morphism U V} {wd : ∀ x, I x → 0 = f x}
    := ex_proof (qcring_f_ex f wd) : ∀ x, f x = qcring_f wd (to_qcring x).

End CRingIdeal.

Section IdealGenerated.

Context {U : Ring}.
Variable S : U → Prop.

Definition ideal_generated_by_set x := ∃ l : ulist ((U * U) * set_type S),
    x = ulist_sum (ulist_image (λ p, fst (fst p) * [snd p|] * snd (fst p)) l).

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
    exists (al + bl).
    rewrite ulist_image_conc, ulist_sum_conc.
    reflexivity.
Qed.

Lemma ideal_generated_by_lmult : ∀ a b,
    ideal_generated_by_set b → ideal_generated_by_set (a * b).
Proof.
    intros a b [l l_eq]; subst b.
    exists (ulist_image (λ p, ((a * fst (fst p), snd (fst p)), snd p)) l).
    rewrite ulist_sum_lmult.
    do 2 rewrite ulist_image_comp.
    cbn.
    apply f_equal.
    apply f_equal2; [>|reflexivity].
    functional_intros x.
    do 2 rewrite mult_assoc.
    reflexivity.
Qed.

Lemma ideal_generated_by_rmult : ∀ a b,
    ideal_generated_by_set a → ideal_generated_by_set (a * b).
Proof.
    intros a b [l l_eq]; subst a.
    exists (ulist_image (λ p, ((fst (fst p), snd (fst p) * b), snd p)) l).
    rewrite ulist_sum_rmult.
    do 2 rewrite ulist_image_comp.
    cbn.
    apply f_equal.
    apply f_equal2; [>|reflexivity].
    functional_intros x.
    rewrite mult_assoc.
    reflexivity.
Qed.

Definition ideal_generated_by : Ideal U := make_ideal
    ideal_generated_by_set
    ideal_generated_by_nempty
    ideal_generated_by_plus
    ideal_generated_by_lmult
    ideal_generated_by_rmult.

End IdealGenerated.

Section CIdealGenerated.

Context {U : CRing}.
Variable S : U → Prop.

Definition cideal_generated_by_set x := ∃ l : ulist (U * set_type S),
    x = ulist_sum (ulist_image (λ p, [snd p|] * fst p) l).

Lemma cideal_generated_by_nempty : ∃ x, cideal_generated_by_set x.
Proof.
    exists 0.
    exists ulist_end.
    rewrite ulist_image_end, ulist_sum_end.
    reflexivity.
Qed.

Lemma cideal_generated_by_plus : ∀ a b,
    cideal_generated_by_set a → cideal_generated_by_set b →
    cideal_generated_by_set (a + b).
Proof.
    intros a b [al al_eq] [bl bl_eq]; subst a b.
    exists (al + bl).
    rewrite ulist_image_conc, ulist_sum_conc.
    reflexivity.
Qed.

Lemma cideal_generated_by_mult : ∀ a b,
    cideal_generated_by_set a → cideal_generated_by_set (a * b).
Proof.
    intros a b [l l_eq]; subst a.
    exists (ulist_image (λ p, (fst p * b, snd p)) l).
    rewrite ulist_sum_rmult.
    do 2 rewrite ulist_image_comp.
    cbn.
    apply f_equal.
    apply f_equal2; [>|reflexivity].
    functional_intros x.
    symmetry; apply mult_assoc.
Qed.

Definition cideal_generated_by : CIdeal U := make_cideal
    cideal_generated_by_set
    cideal_generated_by_nempty
    cideal_generated_by_plus
    cideal_generated_by_mult.

End CIdealGenerated.
