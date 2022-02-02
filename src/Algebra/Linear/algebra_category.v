Require Import init.

Require Export module_category.
Require Import set.

(** These are unital associative algebras.  I'm just calling it "Algebra"
because unital associative algebras are all I care about for the moment.  I can
change names later if I need to.
*)
Record Algebra (F : CRing) := make_algebra {
    algebra_module : Module F;
    algebra_mult : Mult (module_V algebra_module);
    algebra_ldist : @Ldist (module_V algebra_module) (module_plus algebra_module) algebra_mult;
    algebra_rdist : @Rdist (module_V algebra_module) (module_plus algebra_module) algebra_mult;
    algebra_mult_assoc : @MultAssoc (module_V algebra_module) algebra_mult;
    algebra_one : One (module_V algebra_module);
    algebra_mult_lid : @MultLid (module_V algebra_module) algebra_mult algebra_one;
    algebra_mult_rid : @MultRid (module_V algebra_module) algebra_mult algebra_one;
    algebra_scalar_lmult : @ScalarLMult (cring_U F) (module_V algebra_module) algebra_mult (module_scalar algebra_module);
    algebra_scalar_rmult : @ScalarRMult (cring_U F) (module_V algebra_module) algebra_mult (module_scalar algebra_module);
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
Definition algebra_V {F} (A : Algebra F) := module_V (algebra_module A).
Definition algebra_plus {F} (A : Algebra F) := module_plus (algebra_module A).
Definition algebra_zero {F} (A : Algebra F) := module_zero (algebra_module A).
Definition algebra_neg {F} (A : Algebra F) := module_neg (algebra_module A).
Definition algebra_plus_assoc {F} (A : Algebra F) := module_plus_assoc (algebra_module A).
Definition algebra_plus_comm {F} (A : Algebra F) := module_plus_comm (algebra_module A).
Definition algebra_plus_lid {F} (A : Algebra F) := module_plus_lid (algebra_module A).
Definition algebra_plus_linv {F} (A : Algebra F) := module_plus_linv (algebra_module A).
Definition algebra_scalar {F} (A : Algebra F) := module_scalar (algebra_module A).
Definition algebra_scalar_id {F} (A : Algebra F) := module_scalar_id (algebra_module A).
Definition algebra_scalar_ldist {F} (A : Algebra F) := module_scalar_ldist (algebra_module A).
Definition algebra_scalar_rdist {F} (A : Algebra F) := module_scalar_rdist (algebra_module A).
Definition algebra_scalar_comp {F} (A : Algebra F) := module_scalar_comp (algebra_module A).

Record AlgebraHomomorphism {R : CRing} (A B : Algebra R) := make_algebra_homomorphism {
    algebra_homo_f : algebra_V A → algebra_V B;
    algebra_homo_plus : ∀ u v,
        algebra_homo_f (@plus _ (algebra_plus A) u v) =
        @plus _ (algebra_plus B) (algebra_homo_f u) (algebra_homo_f v);
    algebra_homo_scalar : ∀ a v,
        algebra_homo_f (@scalar_mult _ _ (algebra_scalar A) a v) =
        @scalar_mult _ _ (algebra_scalar B) a (algebra_homo_f v);
    algebra_homo_mult : ∀ u v,
        algebra_homo_f (@mult _ (algebra_mult A) u v) =
        @mult _ (algebra_mult B) (algebra_homo_f u) (algebra_homo_f v);
    algebra_homo_one :
        algebra_homo_f (@one _ (algebra_one A)) = @one _ (algebra_one B);
}.
Arguments algebra_homo_f {R A B}.

Definition algebra_to_module_homomorphism {R : CRing} {A B : Algebra R}
    (f : AlgebraHomomorphism A B) :=
    make_module_homomorphism R (algebra_module A) (algebra_module B)
    (algebra_homo_f f)
    (algebra_homo_plus _ _ f)
    (algebra_homo_scalar _ _ f).

Theorem algebra_to_module_homo_eq {R : CRing} {A B : Algebra R}
        (f : AlgebraHomomorphism A B) :
        ∀ x, algebra_homo_f f x =
        module_homo_f (algebra_to_module_homomorphism f) x.
    reflexivity.
Qed.

Theorem algebra_homo_zero {R : CRing} {M N : Algebra R} :
        ∀ f : AlgebraHomomorphism M N,
        algebra_homo_f f (@zero _ (algebra_zero M)) = (@zero _ (algebra_zero N)).
    intros f.
    rewrite algebra_to_module_homo_eq.
    apply module_homo_zero.
Qed.

Theorem algebra_homo_neg {R : CRing} {M N : Algebra R} :
        ∀ f : AlgebraHomomorphism M N,
        ∀ v, algebra_homo_f f (@neg _ (algebra_neg M) v)
        = (@neg _ (algebra_neg N) (algebra_homo_f f v)).
    intros f v.
    rewrite algebra_to_module_homo_eq.
    apply module_homo_neg.
Qed.

Theorem algebra_homomorphism_eq {R : CRing} {M N : Algebra R} :
        ∀ f g : AlgebraHomomorphism M N,
        (∀ x, algebra_homo_f f x = algebra_homo_f g x) → f = g.
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

Definition algebra_homo_id {R : CRing} (A : Algebra R)
    : AlgebraHomomorphism A A := make_algebra_homomorphism R A A
        (λ x, x)
        (λ u v, Logic.eq_refl _)
        (λ a v, Logic.eq_refl _)
        (λ u v, Logic.eq_refl _)
        (Logic.eq_refl _).

Lemma algebra_homo_compose_plus : ∀ {R : CRing} {L M N : Algebra R}
        {f : AlgebraHomomorphism M N} {g : AlgebraHomomorphism L M},
        ∀ a b, algebra_homo_f f (algebra_homo_f g (@plus _ (algebra_plus L) a b)) =
        @plus _ (algebra_plus N) (algebra_homo_f f (algebra_homo_f g a))
        (algebra_homo_f f (algebra_homo_f g b)).
    intros R L M N f g a b.
    rewrite algebra_homo_plus.
    apply algebra_homo_plus.
Qed.
Lemma algebra_homo_compose_scalar : ∀ {R : CRing} {L M N : Algebra R}
        {f : AlgebraHomomorphism M N} {g : AlgebraHomomorphism L M},
        ∀ a v, algebra_homo_f f (algebra_homo_f g
            (@scalar_mult _ _ (algebra_scalar L) a v)) =
        @scalar_mult _ _ (algebra_scalar N)
            a (algebra_homo_f f (algebra_homo_f g v)).
    intros R L M N f g a v.
    rewrite algebra_homo_scalar.
    apply algebra_homo_scalar.
Qed.
Lemma algebra_homo_compose_mult : ∀ {R : CRing} {L M N : Algebra R}
        {f : AlgebraHomomorphism M N} {g : AlgebraHomomorphism L M},
        ∀ a b, algebra_homo_f f (algebra_homo_f g (@mult _ (algebra_mult L) a b)) =
        @mult _ (algebra_mult N) (algebra_homo_f f (algebra_homo_f g a))
        (algebra_homo_f f (algebra_homo_f g b)).
    intros R L M N f g a b.
    rewrite algebra_homo_mult.
    apply algebra_homo_mult.
Qed.
Lemma algebra_homo_compose_one : ∀ {R : CRing} {L M N : Algebra R}
        {f : AlgebraHomomorphism M N} {g : AlgebraHomomorphism L M},
        algebra_homo_f f (algebra_homo_f g (@one _ (algebra_one L))) =
        @one _ (algebra_one N).
    intros R L M N f g.
    rewrite algebra_homo_one.
    apply algebra_homo_one.
Qed.
Definition algebra_homo_compose {R : CRing} {L M N : Algebra R}
    (f : AlgebraHomomorphism M N) (g : AlgebraHomomorphism L M)
    : AlgebraHomomorphism L N := make_algebra_homomorphism R L N
        (λ x, algebra_homo_f f (algebra_homo_f g x))
        algebra_homo_compose_plus algebra_homo_compose_scalar
        algebra_homo_compose_mult algebra_homo_compose_one.

(* begin show *)
Global Program Instance ALGEBRA (R : CRing) : Category := {
    cat_U := Algebra R;
    cat_morphism M N := AlgebraHomomorphism M N;
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

Theorem algebra_to_module_iso {R : CRing} {A B : Algebra R} :
        ∀ f : cat_morphism (ALGEBRA R) A B, isomorphism f →
        isomorphism (C0 := MODULE R)(algebra_to_module_homomorphism f).
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
