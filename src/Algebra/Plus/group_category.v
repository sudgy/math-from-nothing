Require Import init.

Require Export plus_group.
Require Export category_def.
Require Import monoid_category.
Require Import basic_categories.

Record GroupObj := make_group_base {
    group_U :> Type;
    group_plus : Plus group_U;
    group_zero : Zero group_U;
    group_neg : Neg group_U;
    group_plus_assoc : @PlusAssoc group_U group_plus;
    group_plus_lid : @PlusLid group_U group_plus group_zero;
    group_plus_rid : @PlusRid group_U group_plus group_zero;
    group_plus_linv : @PlusLinv group_U group_plus group_zero group_neg;
    group_plus_rinv : @PlusRinv group_U group_plus group_zero group_neg;
}.

Global Existing Instances group_plus group_zero group_neg group_plus_assoc
    group_plus_lid group_plus_rid group_plus_linv group_plus_rinv.

Record GroupHomomorphism (M N : GroupObj) := make_group_homomorphism_base {
    group_homo_f :> M → N;
    group_homo_plus : HomomorphismPlus group_homo_f;
}.

Arguments group_homo_f {M N}.

Global Existing Instances group_homo_plus.

Theorem group_homo_eq {M N : GroupObj} :
    ∀ f g : GroupHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus] [g g_plus] eq.
    cbn in eq; apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    reflexivity.
Qed.

Program Definition Group : Category := {|
    cat_U := GroupObj;
    morphism M N := GroupHomomorphism M N;
    cat_compose L M N f g := make_group_homomorphism_base L N
        (λ x, f (g x))
        (homo_plus_compose g f);
    cat_id M := make_group_homomorphism_base M M
        identity
        {|homo_plus a b := Logic.eq_refl _|};
|}.
Next Obligation.
    apply group_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply group_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply group_homo_eq; cbn.
    reflexivity.
Qed.

Definition make_group a b c d e f g h i := make_group_base a b c d e f g h i
    : Group.
Definition make_group_homomorphism (M N : Group) f f_plus
    := make_group_homomorphism_base M N f f_plus : morphism M N.

Program Definition group_to_type := {|
    functor_f M := group_U M;
    functor_morphism A B f := group_homo_f f;
|} : Functor Group TYPE.

Definition group_to_monoid_base (M : Group) := make_monoid M (group_plus M)
    (group_zero M) (group_plus_assoc M) (group_plus_lid M) (group_plus_rid M).
Program Definition group_to_monoid := {|
    functor_f M := group_to_monoid_base M;
    functor_morphism A B f := make_monoid_homomorphism
        (group_to_monoid_base A) (group_to_monoid_base B)
        f (group_homo_plus _ _ f) (group_homo_zero f);
|} : Functor Group Monoid.
Next Obligation.
    apply monoid_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply monoid_homo_eq; cbn.
    reflexivity.
Qed.


Record CGroupObj := make_cgroup_base {
    cgroup_U :> Type;
    cgroup_plus : Plus cgroup_U;
    cgroup_zero : Zero cgroup_U;
    cgroup_neg : Neg cgroup_U;
    cgroup_plus_assoc : @PlusAssoc cgroup_U cgroup_plus;
    cgroup_plus_comm : @PlusComm cgroup_U cgroup_plus;
    cgroup_plus_lid : @PlusLid cgroup_U cgroup_plus cgroup_zero;
    cgroup_plus_linv : @PlusLinv cgroup_U cgroup_plus cgroup_zero cgroup_neg;
}.

Global Existing Instances cgroup_plus cgroup_zero cgroup_neg cgroup_plus_assoc
    cgroup_plus_comm cgroup_plus_lid cgroup_plus_linv.

Record CGroupHomomorphism (M N : CGroupObj) := make_cgroup_homomorphism_base {
    cgroup_homo_f :> M → N;
    cgroup_homo_plus : HomomorphismPlus cgroup_homo_f;
}.

Arguments cgroup_homo_f {M N}.

Global Existing Instances cgroup_homo_plus.

Theorem cgroup_homo_eq {M N : CGroupObj} :
    ∀ f g : CGroupHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus] [g g_plus] eq.
    cbn in eq; apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    reflexivity.
Qed.

Program Definition CGroup : Category := {|
    cat_U := CGroupObj;
    morphism M N := CGroupHomomorphism M N;
    cat_compose L M N f g := make_cgroup_homomorphism_base L N
        (λ x, f (g x))
        (homo_plus_compose g f);
    cat_id M := make_cgroup_homomorphism_base M M
        identity
        {|homo_plus a b := Logic.eq_refl _|};
|}.
Next Obligation.
    apply cgroup_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply cgroup_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply cgroup_homo_eq; cbn.
    reflexivity.
Qed.

Definition make_cgroup a b c d e f g h := make_cgroup_base a b c d e f g h
    : CGroup.
Definition make_cgroup_homomorphism (M N : CGroup) f f_plus
    := make_cgroup_homomorphism_base M N f f_plus : morphism M N.

Program Definition cgroup_to_type := {|
    functor_f M := cgroup_U M;
    functor_morphism A B f := cgroup_homo_f f;
|} : Functor CGroup TYPE.

Definition cgroup_to_cmonoid_base (M : CGroup) := make_cmonoid M (cgroup_plus M)
    (cgroup_zero M) (cgroup_plus_assoc M) (cgroup_plus_comm M)
    (cgroup_plus_lid M).

Program Definition cgroup_to_cmonoid := {|
    functor_f M := cgroup_to_cmonoid_base M;
    functor_morphism A B f := make_cmonoid_homomorphism
        (cgroup_to_cmonoid_base A) (cgroup_to_cmonoid_base B)
        f (cgroup_homo_plus _ _ f) (group_homo_zero f);
|} : Functor CGroup CMonoid.
Next Obligation.
    apply cmonoid_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply cmonoid_homo_eq; cbn.
    reflexivity.
Qed.

Definition cgroup_to_group_base (M : CGroup) := make_group M
    (cgroup_plus M) (cgroup_zero M) (cgroup_neg M) (cgroup_plus_assoc M)
    (cgroup_plus_lid M) plus_lid_rid (cgroup_plus_linv M) plus_linv_rinv
    : Group.
Program Definition cgroup_to_group := {|
    functor_f M := cgroup_to_group_base M;
    functor_morphism A B f := make_group_homomorphism
        (cgroup_to_group_base A) (cgroup_to_group_base B) f
        (cgroup_homo_plus _ _ f);
|} : Functor CGroup Group.

Definition cgroup_to_monoid := group_to_monoid ∘ cgroup_to_group.
