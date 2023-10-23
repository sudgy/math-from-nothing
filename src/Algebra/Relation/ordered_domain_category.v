Require Import init.

Require Export mult_field.
Require Export category_def.
Require Import domain_category.
Require Import basic_categories.

Require Import set.

Record OrderedDomainObj := make_odomain_base {
    odomain_U :> Type;
    odomain_not_trivial : NotTrivial odomain_U;

    odomain_plus : Plus odomain_U;
    odomain_zero : Zero odomain_U;
    odomain_neg : Neg odomain_U;
    odomain_plus_assoc : @PlusAssoc odomain_U odomain_plus;
    odomain_plus_comm : @PlusComm odomain_U odomain_plus;
    odomain_plus_lid : @PlusLid odomain_U odomain_plus odomain_zero;
    odomain_plus_linv : @PlusLinv odomain_U odomain_plus odomain_zero odomain_neg;

    odomain_mult : Mult odomain_U;
    odomain_one : One odomain_U;
    odomain_mult_assoc : @MultAssoc odomain_U odomain_mult;
    odomain_mult_comm : @MultComm odomain_U odomain_mult;
    odomain_ldist : @Ldist odomain_U odomain_plus odomain_mult;
    odomain_mult_lid : @MultLid odomain_U odomain_mult odomain_one;
    odomain_mult_lcancel : @MultLcancel odomain_U odomain_zero odomain_mult;

    odomain_le : Order odomain_U;
    odomain_le_antisym : @Antisymmetric odomain_U le;
    odomain_le_trans : @Transitive odomain_U le;
    odomain_le_connex : @Connex odomain_U le;
    odomain_le_lplus : @OrderLplus odomain_U odomain_plus odomain_le;
    odomain_le_mult : @OrderMult odomain_U odomain_zero odomain_mult odomain_le;
}.

Global Existing Instances odomain_not_trivial odomain_plus odomain_zero odomain_neg
    odomain_plus_assoc odomain_plus_comm odomain_plus_lid odomain_plus_linv
    odomain_mult odomain_one odomain_mult_assoc odomain_mult_comm
    odomain_ldist odomain_mult_lid odomain_mult_lcancel odomain_le odomain_le_antisym
    odomain_le_trans odomain_le_connex odomain_le_lplus odomain_le_mult.

Record OrderedDomainHomomorphism (M N : OrderedDomainObj)
:= make_odomain_homomorphism_base {
    odomain_homo_f :> M → N;
    odomain_homo_plus : HomomorphismPlus odomain_homo_f;
    odomain_homo_mult : HomomorphismMult odomain_homo_f;
    odomain_homo_one : HomomorphismOne odomain_homo_f;
    odomain_homo_le : HomomorphismLe odomain_homo_f;
    odomain_homo_inj : Injective odomain_homo_f;
}.

Arguments odomain_homo_f {M N}.

Global Existing Instances odomain_homo_plus odomain_homo_mult odomain_homo_one
    odomain_homo_le odomain_homo_inj.

Theorem odomain_homo_eq {M N : OrderedDomainObj} :
    ∀ f g : OrderedDomainHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus f_mult f_one f_le f_inj] [g g_plus g_mult g_one g_le g_inj] eq.
    cbn in eq; apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    rewrite (proof_irrelevance f_mult g_mult).
    rewrite (proof_irrelevance f_one g_one).
    rewrite (proof_irrelevance f_le g_le).
    rewrite (proof_irrelevance f_inj g_inj).
    reflexivity.
Qed.

Local Existing Instance identity_bijective.
Program Definition OrderedDomain : Category := {|
    cat_U := OrderedDomainObj;
    morphism M N := OrderedDomainHomomorphism M N;
    cat_compose L M N f g := make_odomain_homomorphism_base L N
        (λ x, f (g x))
        (homo_plus_compose g f)
        (homo_mult_compose g f)
        (homo_one_compose g f)
        (homo_le_compose g f)
        (inj_comp g f);
    cat_id M := make_odomain_homomorphism_base M M
        identity
        {|homo_plus a b := Logic.eq_refl _|}
        {|homo_mult a b := Logic.eq_refl _|}
        {|homo_one := Logic.eq_refl : identity 1 = 1|}
        {|homo_le := λ a b, identity|}
        bij_inj;
|}.
Local Remove Hints identity_bijective : typeclass_instances.
Next Obligation.
    apply odomain_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply odomain_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply odomain_homo_eq; cbn.
    reflexivity.
Qed.

Definition make_odomain a b c d e f g h i j k l m n o p q r s t u v
    := make_odomain_base a b c d e f g h i j k l m n o p q r s t u v
    : OrderedDomain.
Definition make_odomain_homomorphism (M N : OrderedDomain)
    f f_plus f_mult f_one f_le f_inj
    := make_odomain_homomorphism_base M N f f_plus f_mult f_one f_le f_inj
    : morphism M N.

Program Definition odomain_to_type := {|
    functor_f A := A;
    functor_morphism A B f := f;
|} : Functor OrderedDomain TYPE.

Definition odomain_to_domain_base (A : OrderedDomain) := make_domain A
    (odomain_not_trivial A) (odomain_plus A) (odomain_zero A) (odomain_neg A)
    (odomain_mult A) (odomain_one A) (odomain_plus_assoc A)
    (odomain_plus_comm A) (odomain_plus_lid A) (odomain_plus_linv A)
    (odomain_mult_assoc A) (odomain_mult_comm A) (odomain_ldist A)
    (odomain_mult_lid A) (odomain_mult_lcancel A) : IntegralDomain.
Program Definition odomain_to_domain := {|
    functor_f := odomain_to_domain_base;
    functor_morphism A B f := make_domain_homomorphism
        (odomain_to_domain_base A) (odomain_to_domain_base B) f
        (odomain_homo_plus _ _ f) (odomain_homo_mult _ _ f)
        (odomain_homo_one _ _ f) (odomain_homo_inj _ _ f);
|} : Functor OrderedDomain IntegralDomain.
