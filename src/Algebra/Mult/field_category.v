Require Import init.

Require Export mult_field.
Require Export category_def.
Require Import monoid_category.
Require Import group_category.
Require Import ring_category.
Require Import domain_category.
Require Import basic_categories.

Require Import set.

Record FieldObj := make_field_base {
    field_U :> Type;
    field_not_trivial : NotTrivial field_U;
    field_plus : Plus field_U;
    field_zero : Zero field_U;
    field_neg : Neg field_U;
    field_mult : Mult field_U;
    field_one : One field_U;
    field_div : Div field_U;
    field_plus_assoc : @PlusAssoc field_U field_plus;
    field_plus_comm : @PlusComm field_U field_plus;
    field_plus_lid : @PlusLid field_U field_plus field_zero;
    field_plus_linv : @PlusLinv field_U field_plus field_zero field_neg;
    field_mult_assoc : @MultAssoc field_U field_mult;
    field_mult_comm : @MultComm field_U field_mult;
    field_ldist : @Ldist field_U field_plus field_mult;
    field_mult_lid : @MultLid field_U field_mult field_one;
    field_mult_linv : @MultLinv field_U field_zero field_mult field_one field_div;
}.

Global Existing Instances field_not_trivial field_plus field_zero field_neg
    field_mult field_one field_div field_plus_assoc field_plus_comm
    field_plus_lid field_plus_linv field_mult_assoc field_mult_comm field_ldist
    field_mult_lid field_mult_linv.

Record FieldHomomorphism (M N : FieldObj)
:= make_field_homomorphism_base {
    field_homo_f :> M → N;
    field_homo_plus : HomomorphismPlus field_homo_f;
    field_homo_mult : HomomorphismMult field_homo_f;
    field_homo_one : HomomorphismOne field_homo_f;
}.

Arguments field_homo_f {M N}.

Global Existing Instances field_homo_plus field_homo_mult field_homo_one.

Theorem field_homo_eq {M N : FieldObj} :
    ∀ f g : FieldHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus f_mult f_one] [g g_plus g_mult g_one] eq.
    cbn in eq.
    apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    rewrite (proof_irrelevance f_mult g_mult).
    rewrite (proof_irrelevance f_one g_one).
    reflexivity.
Qed.

Program Definition Field : Category := {|
    cat_U := FieldObj;
    morphism M N := FieldHomomorphism M N;
    cat_compose L M N f g := make_field_homomorphism_base L N
        (λ x, f (g x))
        (homo_plus_compose g f)
        (homo_mult_compose g f)
        (homo_one_compose g f);
    cat_id M := make_field_homomorphism_base M M
        identity
        {|homo_plus a b := Logic.eq_refl _|}
        {|homo_mult a b := Logic.eq_refl _|}
        {|homo_one := Logic.eq_refl : identity 1 = 1|};
|}.
Next Obligation.
    apply field_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply field_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply field_homo_eq; cbn.
    reflexivity.
Qed.

Definition make_field a b c d e f g h i j k l m n o p q
    := make_field_base a b c d e f g h i j k l m n o p q : Field.
Definition make_field_homomorphism (M N : Field) f f_plus f_mult f_one
    := make_field_homomorphism_base M N f f_plus f_mult f_one : morphism M N.

Program Definition field_to_type := {|
    functor_f A := A;
    functor_morphism A B f := f;
|} : Functor Field TYPE.

Definition field_to_domain_base (A : Field) := make_domain A
    (field_not_trivial A) (field_plus A) (field_zero A) (field_neg A) (field_mult A)
    (field_one A) (field_plus_assoc A) (field_plus_comm A) (field_plus_lid A)
    (field_plus_linv A) (field_mult_assoc A) (field_mult_comm A) (field_ldist A)
    (field_mult_lid A) mult_linv_lcancel : IntegralDomain.
Program Definition field_to_domain := {|
    functor_f := field_to_domain_base;
    functor_morphism A B f := make_domain_homomorphism
        (field_to_domain_base A) (field_to_domain_base B) f
        (field_homo_plus _ _ f) (field_homo_mult _ _ f)
        (field_homo_one _ _ f) (field_inj f);
|} : Functor Field IntegralDomain.
Next Obligation.
    apply domain_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply domain_homo_eq; cbn.
    reflexivity.
Qed.

Definition field_to_cring := domain_to_cring ∘ field_to_domain.
Definition field_to_ring := domain_to_ring ∘ field_to_domain.
Definition field_to_rng := domain_to_rng ∘ field_to_domain.
Definition field_to_cgroup := domain_to_cgroup ∘ field_to_domain.
Definition field_to_group := domain_to_group ∘ field_to_domain.
Definition field_to_cmonoid := domain_to_cmonoid ∘ field_to_domain.
Definition field_to_monoid := domain_to_monoid ∘ field_to_domain.
Definition field_to_mult_cmonoid := domain_to_mult_cmonoid ∘ field_to_domain.
Definition field_to_mult_monoid := domain_to_mult_monoid ∘ field_to_domain.

Section FieldMultGroup.

Context (A : Field).

Local Instance field_mult_plus : Plus (set_type (λ x : A, 0 ≠ x)) := {
    plus a b := [[a|] * [b|] | mult_nz [a|] [b|] [|a] [|b]]
}.
Local Instance field_mult_zero : Zero (set_type (λ x : A, 0 ≠ x)) := {
    zero := [1|not_trivial_one]
}.
Local Instance field_mult_neg : Neg (set_type (λ x : A, 0 ≠ x)) := {
    neg a := [/[a|] | div_nz [a|] [|a]]
}.
Local Instance field_mult_plus_assoc : PlusAssoc (set_type (λ x : A, 0 ≠ x)).
Proof.
    split.
    intros a b c.
    apply set_type_eq.
    apply mult_assoc.
Qed.
Local Instance field_mult_plus_comm : PlusComm (set_type (λ x : A, 0 ≠ x)).
Proof.
    split.
    intros a b.
    apply set_type_eq.
    apply mult_comm.
Qed.
Local Instance field_mult_plus_lid : PlusLid (set_type (λ x : A, 0 ≠ x)).
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply mult_lid.
Qed.
Local Instance field_mult_plus_linv : PlusLinv (set_type (λ x : A, 0 ≠ x)).
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply mult_linv.
    exact [|a].
Qed.

Definition field_to_mult_cgroup_base := make_cgroup _ field_mult_plus
    field_mult_zero field_mult_neg field_mult_plus_assoc field_mult_plus_comm
    field_mult_plus_lid field_mult_plus_linv : CGroup.

End FieldMultGroup.
Section FieldMultGroup.

Context (A B : Field) (f : FieldHomomorphism A B).
Let A' := field_to_mult_cgroup_base A.
Let B' := field_to_mult_cgroup_base B.

Let f' (x : A') := [f [x|] | inj_zero f [|x]] : B'.

Lemma field_to_mult_cgroup_f_plus : ∀ a b, f' (a + b) = f' a + f' b.
Proof.
    intros a b.
    apply set_type_eq.
    apply (homo_mult (f := f)).
Qed.

Definition field_to_mult_cgroup_f := make_cgroup_homomorphism A' B' f'
    {|homo_plus := field_to_mult_cgroup_f_plus|}.

End FieldMultGroup.

Program Definition field_to_mult_cgroup := {|
    functor_f := field_to_mult_cgroup_base;
    functor_morphism := field_to_mult_cgroup_f;
|} : Functor Field CGroup.
Next Obligation.
    apply cgroup_homo_eq; cbn.
    intros x.
    apply set_type_eq; reflexivity.
Qed.
Next Obligation.
    apply cgroup_homo_eq; cbn.
    intros x.
    apply set_type_eq; reflexivity.
Qed.

Definition field_to_mult_group := cgroup_to_group ∘ field_to_mult_cgroup.
