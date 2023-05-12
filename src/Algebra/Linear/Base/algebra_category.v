Require Import init.

Require Export module_category.
Require Import set.

(** These are unital associative algebras.  I'm just calling it "AlgebraObj"
because unital associative algebras are all I care about for the moment.  I can
change names later if I need to.
*)
Record AlgebraObj (F : CRingObj) := make_algebra {
    algebra_module : Module F;
    algebra_mult : Mult algebra_module;
    algebra_ldist : @Ldist algebra_module (module_plus algebra_module) algebra_mult;
    algebra_rdist : @Rdist algebra_module (module_plus algebra_module) algebra_mult;
    algebra_mult_assoc : @MultAssoc algebra_module algebra_mult;
    algebra_one : One algebra_module;
    algebra_mult_lid : @MultLid algebra_module algebra_mult algebra_one;
    algebra_mult_rid : @MultRid algebra_module algebra_mult algebra_one;
    algebra_scalar_lmult : @ScalarLMult (cring_U F) algebra_module algebra_mult (module_scalar algebra_module);
    algebra_scalar_rmult : @ScalarRMult (cring_U F) algebra_module algebra_mult (module_scalar algebra_module);
}.
Arguments algebra_module {F}.
Arguments algebra_mult {F}.
Arguments algebra_ldist {F}.
Arguments algebra_rdist {F}.
Arguments algebra_mult_assoc {F}.
Arguments algebra_one {F}.
Arguments algebra_mult_lid {F}.
Arguments algebra_mult_rid {F}.
Arguments algebra_scalar_lmult {F}.
Arguments algebra_scalar_rmult {F}.
Definition algebra_V {F} (A : AlgebraObj F) := module_V (algebra_module A).
Coercion algebra_V : AlgebraObj >-> Sortclass.
Definition algebra_plus {F} (A : AlgebraObj F) := module_plus (algebra_module A).
Definition algebra_zero {F} (A : AlgebraObj F) := module_zero (algebra_module A).
Definition algebra_neg {F} (A : AlgebraObj F) := module_neg (algebra_module A).
Definition algebra_plus_assoc {F} (A : AlgebraObj F) := module_plus_assoc (algebra_module A).
Definition algebra_plus_comm {F} (A : AlgebraObj F) := module_plus_comm (algebra_module A).
Definition algebra_plus_lid {F} (A : AlgebraObj F) := module_plus_lid (algebra_module A).
Definition algebra_plus_linv {F} (A : AlgebraObj F) := module_plus_linv (algebra_module A).
Definition algebra_scalar {F} (A : AlgebraObj F) := module_scalar (algebra_module A).
Definition algebra_scalar_id {F} (A : AlgebraObj F) := module_scalar_id (algebra_module A).
Definition algebra_scalar_ldist {F} (A : AlgebraObj F) := module_scalar_ldist (algebra_module A).
Definition algebra_scalar_rdist {F} (A : AlgebraObj F) := module_scalar_rdist (algebra_module A).
Definition algebra_scalar_comp {F} (A : AlgebraObj F) := module_scalar_comp (algebra_module A).

Global Existing Instances algebra_mult algebra_ldist algebra_rdist
    algebra_mult_assoc algebra_one algebra_mult_lid algebra_mult_rid
    algebra_scalar_lmult algebra_scalar_rmult algebra_plus algebra_zero
    algebra_neg algebra_plus_assoc algebra_plus_comm algebra_plus_lid
    algebra_plus_linv algebra_scalar algebra_scalar_id algebra_scalar_ldist
    algebra_scalar_rdist algebra_scalar_comp.

Record AlgebraObjHomomorphism {R : CRingObj} (A B : AlgebraObj R) := make_algebra_homomorphism {
    algebra_homo_f :> A → B;
    algebra_homo_plus : ∀ u v,
        algebra_homo_f (u + v) = algebra_homo_f u + algebra_homo_f v;
    algebra_homo_scalar : ∀ a v,
        algebra_homo_f (a · v) = a · algebra_homo_f v;
    algebra_homo_mult : ∀ u v,
        algebra_homo_f (u * v) = algebra_homo_f u * algebra_homo_f v;
    algebra_homo_one : algebra_homo_f 1 = 1
}.
Arguments algebra_homo_f {R A B}.

Definition algebra_to_module_homomorphism {R : CRingObj} {A B : AlgebraObj R}
    (f : AlgebraObjHomomorphism A B) :=
    make_module_homomorphism R (algebra_module A) (algebra_module B)
    f
    (algebra_homo_plus _ _ f)
    (algebra_homo_scalar _ _ f).

Theorem algebra_to_module_homo_eq {R : CRingObj} {A B : AlgebraObj R}
    (f : AlgebraObjHomomorphism A B) :
    ∀ x, f x =
    (algebra_to_module_homomorphism f) x.
Proof.
    reflexivity.
Qed.

Theorem algebra_homo_zero {R : CRingObj} {M N : AlgebraObj R} :
    ∀ f : AlgebraObjHomomorphism M N,
    f 0 = 0.
Proof.
    intros f.
    rewrite algebra_to_module_homo_eq.
    apply module_homo_zero.
Qed.

Theorem algebra_homo_neg {R : CRingObj} {M N : AlgebraObj R} :
    ∀ f : AlgebraObjHomomorphism M N,
    ∀ v, f (-v) = -f v.
Proof.
    intros f v.
    rewrite algebra_to_module_homo_eq.
    apply module_homo_neg.
Qed.

Theorem algebra_homomorphism_eq {R : CRingObj} {M N : AlgebraObj R} :
    ∀ f g : AlgebraObjHomomorphism M N,
    (∀ x, f x = g x) → f = g.
Proof.
    intros [f1 plus1 scalar1 mult1 one1] [f2 plus2 scalar2 mult2 one2] f_eq.
    cbn in *.
    assert (f1 = f2) as eq.
    {
        apply functional_ext.
        apply f_eq.
    }
    subst f2.
    rewrite (proof_irrelevance plus2 plus1).
    rewrite (proof_irrelevance scalar2 scalar1).
    rewrite (proof_irrelevance mult2 mult1).
    rewrite (proof_irrelevance one2 one1).
    reflexivity.
Qed.

Definition algebra_homo_id {R : CRingObj} (A : AlgebraObj R)
    : AlgebraObjHomomorphism A A := make_algebra_homomorphism R A A
        (λ x, x)
        (λ u v, Logic.eq_refl _)
        (λ a v, Logic.eq_refl _)
        (λ u v, Logic.eq_refl _)
        (Logic.eq_refl _).

Lemma algebra_homo_compose_plus : ∀ {R : CRingObj} {L M N : AlgebraObj R}
    {f : AlgebraObjHomomorphism M N} {g : AlgebraObjHomomorphism L M},
    ∀ a b, f (g (a + b)) = f (g a) + f (g b).
Proof.
    intros R L M N f g a b.
    rewrite algebra_homo_plus.
    apply algebra_homo_plus.
Qed.
Lemma algebra_homo_compose_scalar : ∀ {R : CRingObj} {L M N : AlgebraObj R}
    {f : AlgebraObjHomomorphism M N} {g : AlgebraObjHomomorphism L M},
    ∀ a v, f (g (a · v)) = a · f (g v).
Proof.
    intros R L M N f g a v.
    rewrite algebra_homo_scalar.
    apply algebra_homo_scalar.
Qed.
Lemma algebra_homo_compose_mult : ∀ {R : CRingObj} {L M N : AlgebraObj R}
    {f : AlgebraObjHomomorphism M N} {g : AlgebraObjHomomorphism L M},
    ∀ a b, f (g (a * b)) = f (g a) * f (g b).
Proof.
    intros R L M N f g a b.
    rewrite algebra_homo_mult.
    apply algebra_homo_mult.
Qed.
Lemma algebra_homo_compose_one : ∀ {R : CRingObj} {L M N : AlgebraObj R}
    {f : AlgebraObjHomomorphism M N} {g : AlgebraObjHomomorphism L M},
    f (g 1) = 1.
Proof.
    intros R L M N f g.
    rewrite algebra_homo_one.
    apply algebra_homo_one.
Qed.
Definition algebra_homo_compose {R : CRingObj} {L M N : AlgebraObj R}
    (f : AlgebraObjHomomorphism M N) (g : AlgebraObjHomomorphism L M)
    : AlgebraObjHomomorphism L N := make_algebra_homomorphism R L N
        (λ x, f (g x))
        algebra_homo_compose_plus algebra_homo_compose_scalar
        algebra_homo_compose_mult algebra_homo_compose_one.

(* begin show *)
Global Program Instance Algebra (R : CRingObj) : Category := {
    cat_U := AlgebraObj R;
    morphism M N := AlgebraObjHomomorphism M N;
    cat_compose {L M N} f g := algebra_homo_compose f g;
    cat_id M := algebra_homo_id M;
}.
(* end show *)
Next Obligation.
    apply algebra_homomorphism_eq.
    intros x.
    cbn.
    reflexivity.
Qed.
Next Obligation.
    apply algebra_homomorphism_eq.
    intros x.
    cbn.
    reflexivity.
Qed.
Next Obligation.
    apply algebra_homomorphism_eq.
    intros x.
    cbn.
    reflexivity.
Qed.

Theorem algebra_to_module_iso {R : CRingObj} {A B : Algebra R} :
    ∀ f : morphism A B, isomorphism f →
    isomorphism (C0 := Module R)(algebra_to_module_homomorphism f).
Proof.
    intros f [g [fg gf]].
    exists (algebra_to_module_homomorphism g).
    split.
    -   apply module_homomorphism_eq.
        intros x; cbn.
        inversion fg as [eq].
        apply (func_eq _ _ eq).
    -   apply module_homomorphism_eq.
        intros x; cbn.
        inversion gf as [eq].
        apply (func_eq _ _ eq).
Qed.
