Require Import init.

Require Export mult_field.
Require Export category_def.
Require Import field_category.
Require Import ordered_domain_category.
Require Import basic_categories.

Require Import set.

Record OrderedFieldObj := make_ofield_base {
    ofield_U :> Type;
    ofield_not_trivial : NotTrivial ofield_U;

    ofield_plus : Plus ofield_U;
    ofield_zero : Zero ofield_U;
    ofield_neg : Neg ofield_U;
    ofield_plus_assoc : @PlusAssoc ofield_U ofield_plus;
    ofield_plus_comm : @PlusComm ofield_U ofield_plus;
    ofield_plus_lid : @PlusLid ofield_U ofield_plus ofield_zero;
    ofield_plus_linv : @PlusLinv ofield_U ofield_plus ofield_zero ofield_neg;

    ofield_mult : Mult ofield_U;
    ofield_one : One ofield_U;
    ofield_div : Div ofield_U;
    ofield_mult_assoc : @MultAssoc ofield_U ofield_mult;
    ofield_mult_comm : @MultComm ofield_U ofield_mult;
    ofield_ldist : @Ldist ofield_U ofield_plus ofield_mult;
    ofield_mult_lid : @MultLid ofield_U ofield_mult ofield_one;
    ofield_mult_linv : @MultLinv ofield_U ofield_zero ofield_mult ofield_one ofield_div;

    ofield_le : Order ofield_U;
    ofield_le_antisym : @Antisymmetric ofield_U le;
    ofield_le_trans : @Transitive ofield_U le;
    ofield_le_connex : @Connex ofield_U le;
    ofield_le_lplus : @OrderLplus ofield_U ofield_plus ofield_le;
    ofield_le_mult : @OrderMult ofield_U ofield_zero ofield_mult ofield_le;
}.

Global Existing Instances ofield_not_trivial ofield_plus ofield_zero ofield_neg
    ofield_plus_assoc ofield_plus_comm ofield_plus_lid ofield_plus_linv
    ofield_mult ofield_one ofield_div ofield_mult_assoc ofield_mult_comm
    ofield_ldist ofield_mult_lid ofield_mult_linv ofield_le ofield_le_antisym
    ofield_le_trans ofield_le_connex ofield_le_lplus ofield_le_mult.

Record OrderedFieldHomomorphism (M N : OrderedFieldObj)
:= make_ofield_homomorphism_base {
    ofield_homo_f :> M → N;
    ofield_homo_plus : HomomorphismPlus ofield_homo_f;
    ofield_homo_mult : HomomorphismMult ofield_homo_f;
    ofield_homo_one : HomomorphismOne ofield_homo_f;
    ofield_homo_le : HomomorphismLe ofield_homo_f;
}.

Arguments ofield_homo_f {M N}.

Global Existing Instances ofield_homo_plus ofield_homo_mult ofield_homo_one
    ofield_homo_le.

Theorem ofield_homo_eq {M N : OrderedFieldObj} :
    ∀ f g : OrderedFieldHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus f_mult f_one f_le] [g g_plus g_mult g_one g_le] eq.
    cbn in eq; apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    rewrite (proof_irrelevance f_mult g_mult).
    rewrite (proof_irrelevance f_one g_one).
    rewrite (proof_irrelevance f_le g_le).
    reflexivity.
Qed.

Program Definition OrderedField : Category := {|
    cat_U := OrderedFieldObj;
    morphism M N := OrderedFieldHomomorphism M N;
    cat_compose L M N f g := make_ofield_homomorphism_base L N
        (λ x, f (g x))
        (homo_plus_compose g f)
        (homo_mult_compose g f)
        (homo_one_compose g f)
        (homo_le_compose g f);
    cat_id M := make_ofield_homomorphism_base M M
        identity
        {|homo_plus a b := Logic.eq_refl _|}
        {|homo_mult a b := Logic.eq_refl _|}
        {|homo_one := Logic.eq_refl : identity 1 = 1|}
        {|homo_le := λ a b, identity|};
|}.
Next Obligation.
    apply ofield_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply ofield_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply ofield_homo_eq; cbn.
    reflexivity.
Qed.

Definition make_ofield a b c d e f g h i j k l m n o p q r s t u v w
    := make_ofield_base a b c d e f g h i j k l m n o p q r s t u v w
    : OrderedField.
Definition make_ofield_homomorphism (M N : OrderedField)
    f f_plus f_mult f_one f_le
    := make_ofield_homomorphism_base M N f f_plus f_mult f_one f_le
    : morphism M N.

Program Definition ofield_to_type := {|
    functor_f A := A;
    functor_morphism A B f := f;
|} : Functor OrderedField TYPE.

Definition ofield_to_field_base (A : OrderedField) := make_field A
    (ofield_not_trivial A) (ofield_plus A) (ofield_zero A) (ofield_neg A)
    (ofield_mult A) (ofield_one A) (ofield_div A) (ofield_plus_assoc A)
    (ofield_plus_comm A) (ofield_plus_lid A) (ofield_plus_linv A)
    (ofield_mult_assoc A) (ofield_mult_comm A) (ofield_ldist A)
    (ofield_mult_lid A) (ofield_mult_linv A) : Field.
Program Definition ofield_to_field := {|
    functor_f := ofield_to_field_base;
    functor_morphism A B f := make_field_homomorphism
        (ofield_to_field_base A) (ofield_to_field_base B) f
        (ofield_homo_plus _ _ f) (ofield_homo_mult _ _ f)
        (ofield_homo_one _ _ f);
|} : Functor OrderedField Field.

Definition ofield_to_odomain_base (A : OrderedField) := make_odomain A
    (ofield_not_trivial A) (ofield_plus A) (ofield_zero A) (ofield_neg A)
    (ofield_plus_assoc A) (ofield_plus_comm A) (ofield_plus_lid A)
    (ofield_plus_linv A) (ofield_mult A) (ofield_one A) (ofield_mult_assoc A)
    (ofield_mult_comm A) (ofield_ldist A) (ofield_mult_lid A) mult_linv_lcancel
    (ofield_le A) (ofield_le_antisym A) (ofield_le_trans A) (ofield_le_connex A)
    (ofield_le_lplus A) (ofield_le_mult A) : OrderedDomain.
Program Definition ofield_to_odomain := {|
    functor_f := ofield_to_odomain_base;
    functor_morphism A B f := make_odomain_homomorphism
        (ofield_to_odomain_base A) (ofield_to_odomain_base B) f
        (ofield_homo_plus _ _ f) (ofield_homo_mult _ _ f)
        (ofield_homo_one _ _ f) (ofield_homo_le _ _ f) (field_inj f);
|} : Functor OrderedField OrderedDomain.
Next Obligation.
    apply odomain_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply odomain_homo_eq; cbn.
    reflexivity.
Qed.
