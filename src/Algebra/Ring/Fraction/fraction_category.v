Require Import init.

Require Import fraction_base.
Require Import fraction_plus.
Require Import fraction_mult.
Require Import fraction_order.

Require Export domain_category.
Require Export field_category.
Require Export ordered_domain_category.
Require Export ordered_field_category.
Require Export category_initterm.
Require Export category_comma.

Require Import nat.

Module FracUniversal.
Section FracUniversal.

Context {U F} (f : U → F) `{
    OrderedFieldClass U,
    OrderedFieldClass F,
    @HomomorphismPlus U F UP UP0 f,
    @HomomorphismMult U F UM UM0 f,
    @HomomorphismOne U F UE UE0 f,
    @HomomorphismLe U F UO UO0 f,
    Injective U F f
}.

Local Existing Instances frac_plus.
Local Existing Instances frac_zero.
Local Existing Instances frac_mult.
Local Existing Instances frac_one.
Local Existing Instances frac_div.
Local Existing Instances frac_order.
Local Existing Instances frac_plus_assoc.
Local Existing Instances frac_plus_comm.
Local Existing Instances frac_plus_lid.
Local Existing Instances frac_plus_linv.
Local Existing Instances frac_mult_comm.
Local Existing Instances frac_mult_linv.
Local Existing Instances to_frac_plus.
Local Existing Instances to_frac_inj.

Definition g (x : frac_base U) := f (fst x) / f [snd x|].

Lemma g_wd : ∀ a b, eq_equal (frac_equiv U) a b → g a = g b.
Proof.
    intros [a1 [a2 a2_nz]] [b1 [b2 b2_nz]] eq.
    equiv_simpl in eq.
    unfold frac_eq in eq; cbn in eq.
    unfold g; cbn.
    apply (inj_zero f) in a2_nz, b2_nz.
    rewrite <- mult_lrmove by exact b2_nz.
    rewrite <- mult_assoc, (mult_comm _ (f b2)), mult_assoc.
    rewrite <- mult_rrmove by exact a2_nz.
    do 2 rewrite <- (homo_mult (f := f)).
    rewrite eq.
    reflexivity.
Qed.

Definition h := unary_op g_wd.

Theorem h_eq : ∀ a, h (to_frac U a) = f a.
Proof.
    intros a.
    unfold h; equiv_simpl.
    unfold g; cbn.
    rewrite homo_one.
    rewrite div_one, mult_rid.
    reflexivity.
Qed.

Local Instance h_plus : HomomorphismPlus h.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold h, plus at 1; equiv_simpl.
    unfold g; cbn.
    destruct a as [a1 [a2 a2_nz]], b as [b1 [b2 b2_nz]]; cbn.
    apply (inj_zero f) in a2_nz, b2_nz.
    setoid_rewrite homo_plus.
    rewrite rdist.
    rewrite (mult_comm a2) at 1.
    do 4 rewrite (homo_mult (f := f)).
    do 2 rewrite div_mult by assumption.
    do 2 rewrite mult_assoc.
    rewrite mult_rrinv by exact b2_nz.
    rewrite mult_rrinv by exact a2_nz.
    reflexivity.
Qed.

Local Instance h_mult : HomomorphismMult h.
Proof.
    split.
    intros a b.
    equiv_get_value a b.
    unfold h, mult at 1; equiv_simpl.
    unfold g; cbn.
    destruct a as [a1 [a2 a2_nz]], b as [b1 [b2 b2_nz]]; cbn.
    apply (inj_zero f) in a2_nz, b2_nz.
    do 2 rewrite (homo_mult (f := f)).
    rewrite div_mult by assumption.
    apply mult_4.
Qed.

Local Instance h_one : HomomorphismOne h.
Proof.
    split.
    unfold h, one at 1; equiv_simpl.
    unfold g; cbn.
    setoid_rewrite homo_one.
    rewrite div_one.
    apply mult_lid.
Qed.

Local Instance h_le : HomomorphismLe h.
Proof.
    clear UD UMD UMDR FF OFF H0.
    split.
    intros a b.
    pose proof (frac_pos_ex U a) as [a1 [a2 [a2_pos a_eq]]].
    pose proof (frac_pos_ex U b) as [b1 [b2 [b2_pos b_eq]]].
    subst a b.
    rewrite (to_frac_div U a1 a2).
    rewrite (to_frac_div U b1 b2).
    destruct a2 as [a2 a2_nz], b2 as [b2 b2_nz].
    cbn in *.
    apply (inj_zero (to_frac U)) in a2_nz as a2_nz', b2_nz as b2_nz'.
    do 2 rewrite (homo_mult (f := h)).
    rewrite (homo_div (f := h)) by exact a2_nz'.
    rewrite (homo_div (f := h)) by exact b2_nz'.
    do 4 rewrite h_eq.
    unfold mult at 1 2, div at 1 2; equiv_simpl.
    rewrite (ifH_false (rand a2_pos)).
    rewrite (ifH_false (rand b2_pos)).
    cbn.
    unfold le at 1; equiv_simpl.
    unfold plus, neg, frac_pos; equiv_simpl.
    do 2 rewrite mult_rid.
    do 2 rewrite mult_lid.
    rewrite rdist.
    do 2 rewrite mult_lneg.
    rewrite le_plus_0_anb_b_a.
    intros leq.
    apply le_mult_rcancel_pos in leq.
    2: apply lt_mult; assumption.
    rewrite (homo_lt2 (f := f)) in a2_pos.
    rewrite (homo_lt2 (f := f)) in b2_pos.
    rewrite (homo_zero (f := f)) in a2_pos, b2_pos.
    rewrite <- le_mult_lrmove_pos by exact b2_pos.
    rewrite mult_comm, mult_assoc.
    rewrite <- le_mult_rrmove_pos by exact a2_pos.
    rewrite mult_comm.
    do 2 rewrite <- homo_mult.
    rewrite <- homo_le2.
    exact leq.
Qed.

Theorem h_uni : ∀ f' : frac_type U → F, HomomorphismPlus f' →
    HomomorphismMult f' → HomomorphismOne f' →
    (∀ x, f' (to_frac U x) = f x) →
    f' = h.
Proof.
    intros f' f'_plus f'_mult f'_one f'_in.
    functional_intros x.
    equiv_get_value x.
    destruct x as [a [b b_nz]].
    rewrite (to_frac_div U a [b|b_nz]); cbn.
    rewrite homo_mult.
    rewrite (homo_mult (f := h)).
    apply (inj_zero (to_frac U)) in b_nz.
    rewrite homo_div by exact b_nz.
    rewrite (homo_div (f := h)) by exact b_nz.
    do 2 rewrite f'_in.
    do 2 rewrite h_eq.
    reflexivity.
Qed.

End FracUniversal.
End FracUniversal.

Import FracUniversal.

Definition frac_field (U : IntegralDomain) : Field := make_field (frac_type U)
    (frac_not_trivial U) (frac_plus U) (frac_zero U) (frac_neg U) (frac_mult U)
    (frac_one U) (frac_div U) (frac_plus_assoc U) (frac_plus_comm U)
    (frac_plus_lid U) (frac_plus_linv U) (frac_mult_assoc U) (frac_mult_comm U)
    (frac_ldist U) (frac_mult_lid U) (frac_mult_linv U).

Definition to_frac (U : IntegralDomain)
    : morphism U (field_to_domain (frac_field U))
    := make_domain_homomorphism U (field_to_domain (frac_field U)) (to_frac U)
        (to_frac_plus U) (to_frac_mult U) (to_frac_one U) (to_frac_inj U).

Theorem frac_universal : ∀ U : IntegralDomain, initial (make_comma_l1
    (C := IntegralDomain) U field_to_domain (frac_field U) (to_frac U)).
Proof.
    intros U [s F f].
    cbn in *.
    apply singleton_set_type.
    exists (Single, make_field_homomorphism (frac_field U) F
        (h f) (h_plus f) (h_mult f) (h_one f)).
    split.
    -   apply domain_homo_eq; cbn.
        exact (h_eq f).
    -   intros [s2 g] g_in'.
        apply (f_equal domain_homo_f) in g_in'; cbn in g_in'.
        pose proof (func_eq _ _ g_in') as g_in.
        cbn in g_in.
        clear g_in'.
        apply prod_combine; [>apply singleton_type_eq|]; cbn.
        apply field_homo_eq; cbn.
        intros x.
        rewrite (h_uni f g).
        2, 3, 4: apply g.
        1: reflexivity.
        exact g_in.
Qed.

Definition frac := free_functor frac_universal.

Arguments to_frac : simpl never.
Arguments frac : simpl never.

Theorem frac_commute : ∀ {A B : IntegralDomain} (h : morphism A B),
    ∀ x, (⌈frac⌉ h) (to_frac A x) = to_frac B (h x).
Proof.
    intros A B h.
    pose proof (free_commute frac_universal h) as eq.
    apply (f_equal domain_homo_f) in eq.
    pose proof (func_eq _ _ eq) as eq2.
    exact eq2.
Qed.

Theorem to_frac_ex {U : IntegralDomain} :
    ∀ x : frac U, ∃ p q, x = to_frac U p / to_frac U q.
Proof.
    intros x.
    equiv_get_value x.
    destruct x as [p [q q_nz]].
    exists p, q.
    apply (to_frac_div U).
Qed.

Definition frac_extend {U : IntegralDomain} {F : Field}
    (f : morphism U (field_to_domain F)) := extend frac_universal f.

Lemma frac_extend_eq {U : IntegralDomain} :
    ∀ {F : Field} (f : morphism U (field_to_domain F)),
    ∀ x, frac_extend f (to_frac U x) = f x.
Proof.
    intros F f.
    apply func_eq.
    pose proof (extend_eq frac_universal f) as eq.
    apply (f_equal domain_homo_f) in eq.
    exact eq.
Qed.

Theorem frac_extend_uni {U : IntegralDomain} : ∀ {F : Field}
    (f : morphism U (field_to_domain F)) (g : morphism (frac U) F),
    (∀ x, g (to_frac U x) = f x) → frac_extend f = g.
Proof.
    intros F f g g_in.
    apply (extend_uni frac_universal f).
    apply domain_homo_eq.
    exact g_in.
Qed.


Definition ofrac_field (U : OrderedDomain) : OrderedField := make_ofield
    (frac_type U) (frac_not_trivial U) (frac_plus U) (frac_zero U) (frac_neg U)
    (frac_plus_assoc U) (frac_plus_comm U) (frac_plus_lid U) (frac_plus_linv U)
    (frac_mult U) (frac_one U) (frac_div U) (frac_mult_assoc U)
    (frac_mult_comm U) (frac_ldist U) (frac_mult_lid U) (frac_mult_linv U)
    (frac_order U) (frac_le_antisym U) (frac_le_trans U) (frac_le_connex U)
    (frac_le_lplus U) (frac_le_mult U).

Definition to_ofrac (U : OrderedDomain)
    : morphism U (ofield_to_odomain (ofrac_field U))
    := make_odomain_homomorphism U (ofield_to_odomain (ofrac_field U))
        (fraction_base.to_frac U) (to_frac_plus U) (to_frac_mult U)
        (to_frac_one U) (to_frac_le U) (to_frac_inj U).

Theorem ofrac_universal : ∀ U : OrderedDomain, initial (make_comma_l1
    (C := OrderedDomain) U ofield_to_odomain (ofrac_field U) (to_ofrac U)).
Proof.
    intros U [s F f].
    cbn in *.
    apply singleton_set_type.
    exists (Single, make_ofield_homomorphism (ofrac_field U) F
        (h f) (h_plus f) (h_mult f) (h_one f) (h_le f)).
    split.
    -   apply odomain_homo_eq; cbn.
        exact (h_eq f).
    -   intros [s2 g] g_in'.
        apply (f_equal odomain_homo_f) in g_in'; cbn in g_in'.
        pose proof (func_eq _ _ g_in') as g_in.
        cbn in g_in.
        clear g_in'.
        apply prod_combine; [>apply singleton_type_eq|]; cbn.
        apply ofield_homo_eq; cbn.
        intros x.
        rewrite (h_uni f g).
        2, 3, 4: apply g.
        1: reflexivity.
        exact g_in.
Qed.

Definition ofrac := free_functor ofrac_universal.

Arguments to_ofrac : simpl never.
Arguments ofrac : simpl never.

Theorem ofrac_commute : ∀ {A B : OrderedDomain} (h : morphism A B),
    ∀ x, (⌈ofrac⌉ h) (to_ofrac A x) = to_ofrac B (h x).
Proof.
    intros A B h.
    pose proof (free_commute ofrac_universal h) as eq.
    apply (f_equal odomain_homo_f) in eq.
    pose proof (func_eq _ _ eq) as eq2.
    exact eq2.
Qed.

Theorem to_ofrac_ex {U : OrderedDomain} :
    ∀ x : ofrac U, ∃ p q, 0 < q ∧ x = to_ofrac U p / to_ofrac U q.
Proof.
    exact (frac_pos_ex_div U).
Qed.

Definition ofrac_extend {U : OrderedDomain} {F : OrderedField}
    (f : morphism U (ofield_to_odomain F)) := extend ofrac_universal f.

Lemma ofrac_extend_eq {U : OrderedDomain} :
    ∀ {F : OrderedField} (f : morphism U (ofield_to_odomain F)),
    ∀ x, ofrac_extend f (to_ofrac U x) = f x.
Proof.
    intros F f.
    apply func_eq.
    pose proof (extend_eq ofrac_universal f) as eq.
    apply (f_equal odomain_homo_f) in eq.
    exact eq.
Qed.

Theorem ofrac_extend_uni {U : OrderedDomain} : ∀ {F : OrderedField}
    (f : morphism U (ofield_to_odomain F)) (g : morphism (ofrac U) F),
    (∀ x, g (to_ofrac U x) = f x) → ofrac_extend f = g.
Proof.
    intros F f g g_in.
    apply (extend_uni ofrac_universal f).
    apply odomain_homo_eq.
    exact g_in.
Qed.

Theorem ofrac_arch (U : OrderedDomain) `{@Archimedean U _ _ _}
    : Archimedean (ofrac U).
Proof.
    exact (frac_arch U).
Qed.

Definition ofrac_frac_extend {U : OrderedDomain} {F : Field}
    (f : morphism (odomain_to_domain U) (field_to_domain F)) := frac_extend f.

Theorem ofrac_frac_eq {U : OrderedDomain} {F : OrderedField} :
    ∀ f : morphism U (ofield_to_odomain F),
    ofrac_frac_extend (F := ofield_to_field F) (⌈odomain_to_domain⌉ f) =
    ⌈ofield_to_field⌉ (ofrac_extend f).
Proof.
    intros f.
    apply (frac_extend_uni).
    intros x.
    cbn.
    exact (ofrac_extend_eq f x).
Qed.
