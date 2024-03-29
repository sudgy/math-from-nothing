Require Import init.

Require Export mult_ring.
Require Export category_def.
Require Import monoid_category.
Require Import group_category.
Require Import ring_category.
Require Import basic_categories.

Record IntegralDomainObj := make_domain_base {
    domain_U :> Type;
    domain_not_trivial : NotTrivial domain_U;
    domain_plus : Plus domain_U;
    domain_zero : Zero domain_U;
    domain_neg : Neg domain_U;
    domain_mult : Mult domain_U;
    domain_one : One domain_U;
    domain_plus_assoc : @PlusAssoc domain_U domain_plus;
    domain_plus_comm : @PlusComm domain_U domain_plus;
    domain_plus_lid : @PlusLid domain_U domain_plus domain_zero;
    domain_plus_linv : @PlusLinv domain_U domain_plus domain_zero domain_neg;
    domain_mult_assoc : @MultAssoc domain_U domain_mult;
    domain_mult_comm : @MultComm domain_U domain_mult;
    domain_ldist : @Ldist domain_U domain_plus domain_mult;
    domain_mult_lid : @MultLid domain_U domain_mult domain_one;
    domain_mult_lcancel : @MultLcancel domain_U domain_zero domain_mult;
}.

Global Existing Instances domain_not_trivial domain_plus domain_zero domain_neg
    domain_mult domain_one domain_plus_assoc domain_plus_comm domain_plus_lid
    domain_plus_linv domain_mult_assoc domain_mult_comm domain_ldist
    domain_mult_lid domain_mult_lcancel.

(** Note that I say that homomorphisms in integral domains must be injective!
The reason for this is that it makes the field of fractions easier to talk
about. *)
Record IntegralDomainHomomorphism (M N : IntegralDomainObj)
:= make_domain_homomorphism_base {
    domain_homo_f :> M → N;
    domain_homo_plus : HomomorphismPlus domain_homo_f;
    domain_homo_mult : HomomorphismMult domain_homo_f;
    domain_homo_one : HomomorphismOne domain_homo_f;
    domain_homo_inj : Injective domain_homo_f;
}.

Arguments domain_homo_f {M N}.

Global Existing Instances domain_homo_plus domain_homo_mult domain_homo_one
    domain_homo_inj.

Theorem domain_homo_eq {M N : IntegralDomainObj} :
    ∀ f g : IntegralDomainHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus f_mult f_one f_inj] [g g_plus g_mult g_one g_inj] eq.
    cbn in eq; apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    rewrite (proof_irrelevance f_mult g_mult).
    rewrite (proof_irrelevance f_one g_one).
    rewrite (proof_irrelevance f_inj g_inj).
    reflexivity.
Qed.

Local Existing Instance identity_bijective.
Program Definition IntegralDomain : Category := {|
    cat_U := IntegralDomainObj;
    morphism M N := IntegralDomainHomomorphism M N;
    cat_compose L M N f g := make_domain_homomorphism_base L N
        (λ x, f (g x))
        (homo_plus_compose g f)
        (homo_mult_compose g f)
        (homo_one_compose g f)
        (inj_comp g f);
    cat_id M := make_domain_homomorphism_base M M
        identity
        {|homo_plus a b := Logic.eq_refl _|}
        {|homo_mult a b := Logic.eq_refl _|}
        {|homo_one := Logic.eq_refl : identity 1 = 1|}
        bij_inj;
|}.
Local Remove Hints identity_bijective : typeclass_instances.
Next Obligation.
    apply domain_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply domain_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply domain_homo_eq; cbn.
    reflexivity.
Qed.

Definition make_domain a b c d e f g h i j k l m n o p
    := make_domain_base a b c d e f g h i j k l m n o p : IntegralDomain.
Definition make_domain_homomorphism (M N : IntegralDomain)
    f f_plus f_mult f_one f_inj
    := make_domain_homomorphism_base M N f f_plus f_mult f_one f_inj
    : morphism M N.

Program Definition domain_to_type := {|
    functor_f A := A;
    functor_morphism A B f := f;
|} : Functor IntegralDomain TYPE.

Definition domain_to_cring_base (A : IntegralDomain) := make_cring A
    (domain_plus A) (domain_zero A) (domain_neg A) (domain_mult A)
    (domain_plus_assoc A) (domain_plus_comm A) (domain_plus_lid A)
    (domain_plus_linv A) (domain_mult_assoc A) (domain_ldist A) (domain_one A)
    (domain_mult_lid A) (domain_mult_comm A) : CRing.
Program Definition domain_to_cring := {|
    functor_f := domain_to_cring_base;
    functor_morphism A B f := make_cring_homomorphism
        (domain_to_cring_base A) (domain_to_cring_base B) f
        (domain_homo_plus _ _ f) (domain_homo_mult _ _ f)
        (domain_homo_one _ _ f);
|} : Functor IntegralDomain CRing.

Definition domain_to_ring := cring_to_ring ∘ domain_to_cring.
Definition domain_to_rng := cring_to_rng ∘ domain_to_cring.
Definition domain_to_cgroup := cring_to_cgroup ∘ domain_to_cring.
Definition domain_to_group := cring_to_group ∘ domain_to_cring.
Definition domain_to_cmonoid := cring_to_cmonoid ∘ domain_to_cring.
Definition domain_to_monoid := cring_to_monoid ∘ domain_to_cring.
Definition domain_to_mult_cmonoid := cring_to_mult_cmonoid ∘ domain_to_cring.
Definition domain_to_mult_monoid := cring_to_mult_monoid ∘ domain_to_cring.
