Require Import init.

Require Export mult_ring.
Require Export category_def.
Require Import monoid_category.
Require Import group_category.
Require Import basic_categories.

Record RngObj := make_rng_base {
    rng_U :> Type;
    rng_plus : Plus rng_U;
    rng_zero : Zero rng_U;
    rng_neg : Neg rng_U;
    rng_mult : Mult rng_U;
    rng_plus_assoc : @PlusAssoc rng_U rng_plus;
    rng_plus_comm : @PlusComm rng_U rng_plus;
    rng_plus_lid : @PlusLid rng_U rng_plus rng_zero;
    rng_plus_linv : @PlusLinv rng_U rng_plus rng_zero rng_neg;
    rng_mult_assoc : @MultAssoc rng_U rng_mult;
    rng_ldist : @Ldist rng_U rng_plus rng_mult;
    rng_rdist : @Rdist rng_U rng_plus rng_mult;
}.

Global Existing Instances rng_plus rng_zero rng_neg rng_mult rng_plus_assoc
    rng_plus_comm rng_plus_lid rng_plus_linv rng_mult_assoc rng_ldist rng_rdist.

Record RingObj := make_ring_base {
    ring_rng : RngObj;
    ring_one : One (rng_U ring_rng);
    ring_mult_lid : @MultLid (rng_U ring_rng) (rng_mult ring_rng) ring_one;
    ring_mult_rid : @MultRid (rng_U ring_rng) (rng_mult ring_rng) ring_one;
}.
Definition ring_U R := rng_U (ring_rng R).
Coercion ring_U : RingObj >-> Sortclass.
Definition ring_plus R := rng_plus (ring_rng R).
Definition ring_zero R := rng_zero (ring_rng R).
Definition ring_neg R := rng_neg (ring_rng R).
Definition ring_mult R := rng_mult (ring_rng R).
Definition ring_plus_assoc R := rng_plus_assoc (ring_rng R).
Definition ring_plus_comm R := rng_plus_comm (ring_rng R).
Definition ring_plus_lid R := rng_plus_lid (ring_rng R).
Definition ring_plus_linv R := rng_plus_linv (ring_rng R).
Definition ring_mult_assoc R := rng_mult_assoc (ring_rng R).
Definition ring_ldist R := rng_ldist (ring_rng R).
Definition ring_rdist R := rng_rdist (ring_rng R).

Global Existing Instances ring_plus ring_zero ring_neg ring_mult ring_plus_assoc
    ring_plus_comm ring_plus_lid ring_plus_linv ring_mult_assoc ring_ldist
    ring_rdist ring_one ring_mult_lid ring_mult_rid.

Record CRingObj := make_cring_base {
    cring_ring : RingObj;
    cring_mult_comm : @MultComm (ring_U cring_ring) (ring_mult cring_ring);
}.
Definition cring_U R := ring_U (cring_ring R).
Coercion cring_U : CRingObj >-> Sortclass.
Definition cring_plus R := ring_plus (cring_ring R).
Definition cring_zero R := ring_zero (cring_ring R).
Definition cring_neg R := ring_neg (cring_ring R).
Definition cring_mult R := ring_mult (cring_ring R).
Definition cring_plus_assoc R := ring_plus_assoc (cring_ring R).
Definition cring_plus_comm R := ring_plus_comm (cring_ring R).
Definition cring_plus_lid R := ring_plus_lid (cring_ring R).
Definition cring_plus_linv R := ring_plus_linv (cring_ring R).
Definition cring_mult_assoc R := ring_mult_assoc (cring_ring R).
Definition cring_ldist R := ring_ldist (cring_ring R).
Definition cring_one R := ring_one (cring_ring R).
Definition cring_mult_lid R := ring_mult_lid (cring_ring R).

Global Existing Instances cring_plus cring_zero cring_neg cring_mult
    cring_plus_assoc cring_plus_comm cring_plus_lid cring_plus_linv
    cring_mult_assoc cring_ldist cring_one cring_mult_lid cring_mult_comm.

Record RngHomomorphism (M N : RngObj) := make_rng_homomorphism_base {
    rng_homo_f :> M → N;
    rng_homo_plus : HomomorphismPlus rng_homo_f;
    rng_homo_mult : HomomorphismMult rng_homo_f;
}.

Arguments rng_homo_f {M N}.

Global Existing Instances rng_homo_plus rng_homo_mult.

Theorem rng_homo_eq {M N : RngObj} :
    ∀ f g : RngHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus f_mult] [g g_plus g_mult] eq.
    cbn in eq; apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    rewrite (proof_irrelevance f_mult g_mult).
    reflexivity.
Qed.

Program Definition Rng : Category := {|
    cat_U := RngObj;
    morphism M N := RngHomomorphism M N;
    cat_compose L M N f g := make_rng_homomorphism_base L N
        (λ x, f (g x))
        (homo_plus_compose g f)
        (homo_mult_compose g f);
    cat_id M := make_rng_homomorphism_base M M
        identity
        {|homo_plus a b := Logic.eq_refl _|}
        {|homo_mult a b := Logic.eq_refl _|};
|}.
Next Obligation.
    apply rng_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply rng_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply rng_homo_eq; cbn.
    reflexivity.
Qed.

Definition make_rng a b c d e f g h i j k l
    := make_rng_base a b c d e f g h i j k l : Rng.
Definition make_rng_homomorphism (M N : Rng) f f_plus f_mult
    := make_rng_homomorphism_base M N f f_plus f_mult : morphism M N.

Record RingHomomorphism (M N : RingObj) := make_ring_homomorphism_base {
    ring_homo_f :> M → N;
    ring_homo_plus : HomomorphismPlus ring_homo_f;
    ring_homo_mult : HomomorphismMult ring_homo_f;
    ring_homo_one : HomomorphismOne ring_homo_f;
}.

Arguments ring_homo_f {M N}.

Global Existing Instances ring_homo_plus ring_homo_mult ring_homo_one.

Theorem ring_homo_eq {M N : RingObj} :
    ∀ f g : RingHomomorphism M N, (∀ x, f x = g x) → f = g.
Proof.
    intros [f f_plus f_mult f_one] [g g_plus g_mult g_one] eq.
    cbn in eq; apply functional_ext in eq.
    subst g.
    rewrite (proof_irrelevance f_plus g_plus).
    rewrite (proof_irrelevance f_mult g_mult).
    rewrite (proof_irrelevance f_one g_one).
    reflexivity.
Qed.

Program Definition Ring : Category := {|
    cat_U := RingObj;
    morphism M N := RingHomomorphism M N;
    cat_compose L M N f g := make_ring_homomorphism_base L N
        (λ x, f (g x))
        (homo_plus_compose g f)
        (homo_mult_compose g f)
        (homo_one_compose g f);
    cat_id M := make_ring_homomorphism_base M M
        identity
        {|homo_plus a b := Logic.eq_refl _|}
        {|homo_mult a b := Logic.eq_refl _|}
        {|homo_one := Logic.eq_refl : identity 1 = 1|};
|}.
Next Obligation.
    apply ring_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply ring_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply ring_homo_eq; cbn.
    reflexivity.
Qed.

Definition make_ring a b c d e f g h i j k l m n o
    := make_ring_base (make_rng a b c d e f g h i j k l) m n o : Ring.
Definition make_ring_homomorphism (M N : Ring) f f_plus f_mult f_one
    := make_ring_homomorphism_base M N f f_plus f_mult f_one : morphism M N.

Record CRingHomomorphism (M N : CRingObj) := make_cring_homomorphism_base {
    cring_homo_f :> M → N;
    cring_homo_plus : HomomorphismPlus cring_homo_f;
    cring_homo_mult : HomomorphismMult cring_homo_f;
    cring_homo_one : HomomorphismOne cring_homo_f;
}.

Arguments cring_homo_f {M N}.

Global Existing Instances cring_homo_plus cring_homo_mult cring_homo_one.

Theorem cring_homo_eq {M N : CRingObj} :
    ∀ f g : CRingHomomorphism M N, (∀ x, f x = g x) → f = g.
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


Program Definition CRing : Category := {|
    cat_U := CRingObj;
    morphism M N := CRingHomomorphism M N;
    cat_compose L M N f g := make_cring_homomorphism_base L N
        (λ x, f (g x))
        (homo_plus_compose g f)
        (homo_mult_compose g f)
        (homo_one_compose g f);
    cat_id M := make_cring_homomorphism_base M M
        identity
        {|homo_plus a b := Logic.eq_refl _|}
        {|homo_mult a b := Logic.eq_refl _|}
        {|homo_one := Logic.eq_refl : identity 1 = 1|};
|}.
Next Obligation.
    apply cring_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply cring_homo_eq; cbn.
    reflexivity.
Qed.
Next Obligation.
    apply cring_homo_eq; cbn.
    reflexivity.
Qed.

Definition make_cring a b c d e f g h i j k (l : One a) (m : MultLid a) n
    := make_cring_base
        (make_ring a b c d e f g h i j k
        (ldist_rdist (UMC := n)) l m mult_lid_rid) n : CRing.
Definition make_cring_homomorphism (M N : CRing) f f_plus f_mult f_one
    := make_cring_homomorphism_base M N f f_plus f_mult f_one : morphism M N.

Program Definition rng_to_type := {|
    functor_f A := A;
    functor_morphism A B f := f;
|} : Functor Rng TYPE.

Program Definition ring_to_type := {|
    functor_f A := A;
    functor_morphism A B f := f;
|} : Functor Ring TYPE.

Program Definition cring_to_type := {|
    functor_f A := A;
    functor_morphism A B f := f;
|} : Functor CRing TYPE.

Definition rng_to_cgroup_base (A : Rng) := make_cgroup A (rng_plus A)
    (rng_zero A) (rng_neg A) (rng_plus_assoc A) (rng_plus_comm A)
    (rng_plus_lid A) (rng_plus_linv A).
Program Definition rng_to_cgroup := {|
    functor_f A := rng_to_cgroup_base A;
    functor_morphism A B f := make_cgroup_homomorphism
        (rng_to_cgroup_base A) (rng_to_cgroup_base B)
        f (rng_homo_plus _ _ f);
|} : Functor Rng CGroup.

Program Definition ring_to_rng := {|
    functor_f A := ring_rng A;
    functor_morphism A B f := make_rng_homomorphism
        (ring_rng A) (ring_rng B) f
        (ring_homo_plus _ _ f) (ring_homo_mult _ _ f);
|} : Functor Ring Rng.

Program Definition cring_to_ring := {|
    functor_f A := cring_ring A;
    functor_morphism A B f := make_ring_homomorphism
        (cring_ring A) (cring_ring B) f
        (cring_homo_plus _ _ f) (cring_homo_mult _ _ f) (cring_homo_one _ _ f);
|} : Functor CRing Ring.

Definition rng_to_group := cgroup_to_group ∘ rng_to_cgroup.
Definition rng_to_cmonoid := cgroup_to_cmonoid ∘ rng_to_cgroup.
Definition rng_to_monoid := cgroup_to_monoid ∘ rng_to_cgroup.

Definition ring_to_cgroup := rng_to_cgroup ∘ ring_to_rng.
Definition ring_to_group := rng_to_group ∘ ring_to_rng.
Definition ring_to_cmonoid := rng_to_cmonoid ∘ ring_to_rng.
Definition ring_to_monoid := rng_to_monoid ∘ ring_to_rng.

Definition cring_to_rng := ring_to_rng ∘ cring_to_ring.
Definition cring_to_cgroup := ring_to_cgroup ∘ cring_to_ring.
Definition cring_to_group := ring_to_group ∘ cring_to_ring.
Definition cring_to_cmonoid := ring_to_cmonoid ∘ cring_to_ring.
Definition cring_to_monoid := ring_to_monoid ∘ cring_to_ring.

Section RingToMultMonoid.

Context (A : Ring).
Local Instance ring_to_mult_plus : Plus A := {plus := mult}.
Local Instance ring_to_mult_zero : Zero A := {zero := 1}.
Local Instance ring_to_mult_assoc : PlusAssoc A := {plus_assoc := mult_assoc}.
Local Instance ring_to_mult_lid : PlusLid A := {plus_lid := mult_lid}.
Local Instance ring_to_mult_rid : PlusRid A := {plus_rid := mult_rid}.
Definition ring_to_mult_monoid_base := make_monoid A ring_to_mult_plus
    ring_to_mult_zero ring_to_mult_assoc ring_to_mult_lid ring_to_mult_rid.

End RingToMultMonoid.

Program Definition ring_to_mult_monoid := {|
    functor_f A := ring_to_mult_monoid_base A;
    functor_morphism A B f := make_monoid_homomorphism
        (ring_to_mult_monoid_base A) (ring_to_mult_monoid_base B) f
        {|homo_plus := homo_mult|} {|homo_zero := homo_one|}
|} : Functor Ring Monoid.
Next Obligation.
    apply monoid_homo_eq; cbn.
    reflexivity.
Qed.

Section CRingToMultCMonoid.

Context (A : CRing).
Local Instance cring_to_mult_plus : Plus A := {plus := mult}.
Local Instance cring_to_mult_zero : Zero A := {zero := 1}.
Local Instance cring_to_mult_assoc : PlusAssoc A := {plus_assoc := mult_assoc}.
Local Instance cring_to_mult_comm : PlusComm A := {plus_comm := mult_comm}.
Local Instance cring_to_mult_lid : PlusLid A := {plus_lid := mult_lid}.
Local Instance cring_to_mult_rid : PlusRid A := {plus_rid := mult_rid}.
Definition cring_to_mult_cmonoid_base := make_cmonoid A cring_to_mult_plus
    cring_to_mult_zero cring_to_mult_assoc cring_to_mult_comm cring_to_mult_lid.

End CRingToMultCMonoid.

Program Definition cring_to_mult_cmonoid := {|
    functor_f A := cring_to_mult_cmonoid_base A;
    functor_morphism A B f := make_cmonoid_homomorphism
        (cring_to_mult_cmonoid_base A) (cring_to_mult_cmonoid_base B) f
        {|homo_plus := homo_mult|} {|homo_zero := homo_one|}
|} : Functor CRing CMonoid.
Next Obligation.
    apply cmonoid_homo_eq; cbn.
    reflexivity.
Qed.

Definition cring_to_mult_monoid := cmonoid_to_monoid ∘ cring_to_mult_cmonoid.
