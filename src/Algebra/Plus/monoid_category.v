Require Import init.

Require Export plus_group.
Require Export category_def.
Require Import basic_categories.

Require Import list.
Require Import unordered_list.

Record MonoidObj := make_monoid_base {
    monoid_U :> Type;
    monoid_plus : Plus monoid_U;
    monoid_zero : Zero monoid_U;
    monoid_plus_assoc : @PlusAssoc monoid_U monoid_plus;
    monoid_plus_lid : @PlusLid monoid_U monoid_plus monoid_zero;
    monoid_plus_rid : @PlusRid monoid_U monoid_plus monoid_zero;
}.

Global Existing Instances monoid_plus monoid_zero monoid_plus_assoc
    monoid_plus_lid monoid_plus_rid.

Record MonoidHomomorphism (M N : MonoidObj) := make_monoid_homomorphism_base {
    monoid_homo_f :> M → N;
    monoid_homo_plus : HomomorphismPlus monoid_homo_f;
    monoid_homo_zero : HomomorphismZero monoid_homo_f;
}.

Arguments monoid_homo_f {M N}.

Global Existing Instances monoid_homo_plus monoid_homo_zero.

Theorem monoid_homo_eq {M N : MonoidObj} :
    ∀ f g : MonoidHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus f_zero] [g g_plus g_zero] eq.
    cbn in eq.
    apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    rewrite (proof_irrelevance f_zero g_zero).
    reflexivity.
Qed.

Lemma monoid_homo_id_zero (M : MonoidObj) : 0 = (0 : M).
Proof.
    reflexivity.
Qed.
Definition monoid_homo_id (M : MonoidObj) := make_monoid_homomorphism_base M M
    identity
    {|homo_plus a b := Logic.eq_refl _|}
    {|homo_zero := monoid_homo_id_zero M|}.

Lemma monoid_homo_compose_plus : ∀ {L M N : MonoidObj}
    {f : MonoidHomomorphism M N} {g : MonoidHomomorphism L M},
    ∀ a b, f (g (a + b)) = f (g a) + f (g b).
Proof.
    intros L M N f g a b.
    setoid_rewrite homo_plus.
    apply homo_plus.
Qed.
Lemma monoid_homo_compose_zero : ∀ {L M N : MonoidObj}
    {f : MonoidHomomorphism M N} {g : MonoidHomomorphism L M},
    f (g 0) = 0.
Proof.
    intros L M N f g.
    setoid_rewrite homo_zero.
    apply homo_zero.
Qed.
Definition monoid_homo_compose {L M N : MonoidObj}
    (f : MonoidHomomorphism M N) (g : MonoidHomomorphism L M)
    : MonoidHomomorphism L N := make_monoid_homomorphism_base L N
        (λ x, f (g x))
        {|homo_plus := monoid_homo_compose_plus|}
        {|homo_zero := monoid_homo_compose_zero|}.

Program Definition Monoid : Category := {|
    cat_U := MonoidObj;
    morphism M N := MonoidHomomorphism M N;
    cat_compose L M N f g := monoid_homo_compose f g;
    cat_id M := monoid_homo_id M;
|}.
Next Obligation.
    apply monoid_homo_eq.
    intros x.
    cbn.
    reflexivity.
Qed.
Next Obligation.
    apply monoid_homo_eq.
    intros x.
    cbn.
    reflexivity.
Qed.
Next Obligation.
    apply monoid_homo_eq.
    intros x.
    cbn.
    reflexivity.
Qed.

Definition make_monoid a b c d e f := make_monoid_base a b c d e f : Monoid.
Definition make_monoid_homomorphism (M N : Monoid) f f_plus f_zero
    := make_monoid_homomorphism_base M N f f_plus f_zero : morphism M N.

Program Definition monoid_to_type := {|
    functor_f M := monoid_U M;
    functor_morphism A B f := monoid_homo_f f;
|} : Functor Monoid TYPE.

Definition list_monoid U := make_monoid (list U) (list_plus U) (list_zero U)
    (list_plus_assoc U) (list_plus_lid U) (list_plus_rid U).

Program Definition free_monoid := {|
    functor_f U := list_monoid U;
    functor_morphism A B f := make_monoid_homomorphism
        (list_monoid A) (list_monoid B) (list_image f)
        {|homo_plus a b := list_image_conc a b f|}
        {|homo_zero := list_image_end f|};
|} : Functor TYPE Monoid.
Next Obligation.
    apply monoid_homo_eq; cbn.
    intros x.
    symmetry; apply list_image_comp.
Qed.
Next Obligation.
    apply monoid_homo_eq; cbn.
    induction x.
    -   apply list_image_end.
    -   rewrite list_image_add.
        rewrite IHx.
        reflexivity.
Qed.


Record CMonoidObj := make_cmonoid_base {
    cmonoid_U :> Type;
    cmonoid_plus : Plus cmonoid_U;
    cmonoid_zero : Zero cmonoid_U;
    cmonoid_plus_assoc : @PlusAssoc cmonoid_U cmonoid_plus;
    cmonoid_plus_comm : @PlusComm cmonoid_U cmonoid_plus;
    cmonoid_plus_lid : @PlusLid cmonoid_U cmonoid_plus cmonoid_zero;
}.

Global Existing Instances cmonoid_plus cmonoid_zero cmonoid_plus_assoc
    cmonoid_plus_comm cmonoid_plus_lid.

Record CMonoidHomomorphism (M N : CMonoidObj) := make_cmonoid_homomorphism_base {
    cmonoid_homo_f :> M → N;
    cmonoid_homo_plus : HomomorphismPlus cmonoid_homo_f;
    cmonoid_homo_zero : HomomorphismZero cmonoid_homo_f;
}.

Arguments cmonoid_homo_f {M N}.

Global Existing Instances cmonoid_homo_plus cmonoid_homo_zero.

Theorem cmonoid_homo_eq {M N : CMonoidObj} :
    ∀ f g : CMonoidHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus f_zero] [g g_plus g_zero] eq.
    cbn in eq.
    apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    rewrite (proof_irrelevance f_zero g_zero).
    reflexivity.
Qed.

Lemma cmonoid_homo_id_zero (M : CMonoidObj) : 0 = (0 : M).
Proof.
    reflexivity.
Qed.
Definition cmonoid_homo_id (M : CMonoidObj) := make_cmonoid_homomorphism_base M M
    identity
    {|homo_plus a b := Logic.eq_refl _|}
    {|homo_zero := cmonoid_homo_id_zero M|}.

Lemma cmonoid_homo_compose_plus : ∀ {L M N : CMonoidObj}
    {f : CMonoidHomomorphism M N} {g : CMonoidHomomorphism L M},
    ∀ a b, f (g (a + b)) = f (g a) + f (g b).
Proof.
    intros L M N f g a b.
    setoid_rewrite homo_plus.
    apply homo_plus.
Qed.
Lemma cmonoid_homo_compose_zero : ∀ {L M N : CMonoidObj}
    {f : CMonoidHomomorphism M N} {g : CMonoidHomomorphism L M},
    f (g 0) = 0.
Proof.
    intros L M N f g.
    setoid_rewrite homo_zero.
    apply homo_zero.
Qed.
Definition cmonoid_homo_compose {L M N : CMonoidObj}
    (f : CMonoidHomomorphism M N) (g : CMonoidHomomorphism L M)
    : CMonoidHomomorphism L N := make_cmonoid_homomorphism_base L N
        (λ x, f (g x))
        {|homo_plus := cmonoid_homo_compose_plus|}
        {|homo_zero := cmonoid_homo_compose_zero|}.

Program Definition CMonoid : Category := {|
    cat_U := CMonoidObj;
    morphism M N := CMonoidHomomorphism M N;
    cat_compose L M N f g := cmonoid_homo_compose f g;
    cat_id M := cmonoid_homo_id M;
|}.
Next Obligation.
    apply cmonoid_homo_eq.
    intros x.
    cbn.
    reflexivity.
Qed.
Next Obligation.
    apply cmonoid_homo_eq.
    intros x.
    cbn.
    reflexivity.
Qed.
Next Obligation.
    apply cmonoid_homo_eq.
    intros x.
    cbn.
    reflexivity.
Qed.

Definition make_cmonoid a b c d e f := make_cmonoid_base a b c d e f : CMonoid.
Definition make_cmonoid_homomorphism (M N : CMonoid) f f_plus f_zero
    := make_cmonoid_homomorphism_base M N f f_plus f_zero : morphism M N.

Program Definition cmonoid_to_type := {|
    functor_f M := cmonoid_U M;
    functor_morphism A B f := cmonoid_homo_f f;
|} : Functor CMonoid TYPE.

Definition ulist_cmonoid U := make_cmonoid (ulist U) (ulist_plus U)
    (ulist_zero U) (ulist_plus_assoc U) (ulist_plus_comm U) (ulist_plus_lid U).

Program Definition free_cmonoid := {|
    functor_f U := ulist_cmonoid U;
    functor_morphism A B f := make_cmonoid_homomorphism
        (ulist_cmonoid A) (ulist_cmonoid B) (ulist_image f)
        {|homo_plus a b := ulist_image_conc a b f|}
        {|homo_zero := ulist_image_end f|};
|} : Functor TYPE CMonoid.
Next Obligation.
    apply cmonoid_homo_eq; cbn.
    intros x.
    symmetry; apply ulist_image_comp.
Qed.
Next Obligation.
    apply cmonoid_homo_eq; cbn.
    induction x using ulist_induction.
    -   apply ulist_image_end.
    -   rewrite ulist_image_add.
        rewrite IHx.
        reflexivity.
Qed.

Definition cmonoid_to_monoid_base (M : CMonoid) := make_monoid M
    (cmonoid_plus M) (cmonoid_zero M) (cmonoid_plus_assoc M)
    (cmonoid_plus_lid M) plus_lid_rid : Monoid.
Program Definition cmonoid_to_monoid := {|
    functor_f M := cmonoid_to_monoid_base M;
    functor_morphism A B f := make_monoid_homomorphism
        (cmonoid_to_monoid_base A) (cmonoid_to_monoid_base B) f
        (cmonoid_homo_plus _ _ f) (cmonoid_homo_zero _ _ f);
|} : Functor CMonoid Monoid.
Next Obligation.
    apply monoid_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply monoid_homo_eq; cbn.
    reflexivity.
Qed.
