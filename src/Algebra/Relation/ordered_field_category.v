Require Import init.

Require Export mult_field.
Require Export category_def.
Require Import field_category.
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
    cbn in eq.
    apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    rewrite (proof_irrelevance f_mult g_mult).
    rewrite (proof_irrelevance f_one g_one).
    rewrite (proof_irrelevance f_le g_le).
    reflexivity.
Qed.

Lemma ofield_homo_id_one (M : OrderedFieldObj) : 1 = (1 : M).
Proof.
    reflexivity.
Qed.
Definition ofield_homo_id (M : OrderedFieldObj) :=
    make_ofield_homomorphism_base M M
    identity
    {|homo_plus a b := Logic.eq_refl _|}
    {|homo_mult a b := Logic.eq_refl _|}
    {|homo_one := ofield_homo_id_one M|}
    {|homo_le := λ a b, identity|}.

Lemma ofield_homo_compose_plus : ∀ {L M N : OrderedFieldObj}
    {f : OrderedFieldHomomorphism M N} {g : OrderedFieldHomomorphism L M},
    ∀ a b, f (g (a + b)) = f (g a) + f (g b).
Proof.
    intros L M N f g a b.
    setoid_rewrite homo_plus.
    apply homo_plus.
Qed.
Lemma ofield_homo_compose_mult : ∀ {L M N : OrderedFieldObj}
    {f : OrderedFieldHomomorphism M N} {g : OrderedFieldHomomorphism L M},
    ∀ a b, f (g (a * b)) = f (g a) * f (g b).
Proof.
    intros L M N f g a b.
    setoid_rewrite homo_mult.
    apply homo_mult.
Qed.
Lemma ofield_homo_compose_one : ∀ {L M N : OrderedFieldObj}
    {f : OrderedFieldHomomorphism M N} {g : OrderedFieldHomomorphism L M},
    f (g 1) = 1.
Proof.
    intros L M N f g.
    setoid_rewrite homo_one.
    apply homo_one.
Qed.
Lemma ofield_homo_compose_le : ∀ {L M N : OrderedFieldObj}
    {f : OrderedFieldHomomorphism M N} {g : OrderedFieldHomomorphism L M},
    ∀ a b, a ≤ b → f (g a) ≤ f (g b).
Proof.
    intros L M N f g a b leq.
    do 2 apply homo_le.
    exact leq.
Qed.
Definition ofield_homo_compose {L M N : OrderedFieldObj}
    (f : OrderedFieldHomomorphism M N) (g : OrderedFieldHomomorphism L M)
    : OrderedFieldHomomorphism L N := make_ofield_homomorphism_base L N
        (λ x, f (g x))
        {|homo_plus := ofield_homo_compose_plus|}
        {|homo_mult := ofield_homo_compose_mult|}
        {|homo_one := ofield_homo_compose_one|}
        {|homo_le := ofield_homo_compose_le|}.

Program Definition OrderedField : Category := {|
    cat_U := OrderedFieldObj;
    morphism M N := OrderedFieldHomomorphism M N;
    cat_compose L M N f g := ofield_homo_compose f g;
    cat_id M := ofield_homo_id M;
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
Definition make_ofield_homomorphism (M N : Field) f f_plus f_mult f_one
    := make_field_homomorphism_base M N f f_plus f_mult f_one : morphism M N.

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
Next Obligation.
    apply field_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply field_homo_eq; cbn.
    reflexivity.
Qed.
