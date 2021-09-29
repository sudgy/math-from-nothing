Require Import init.

Require Export linear_base.
Require Export category_base.

(** I don't know if this is the best way to define this, but I'll try it for now
*)

(** This requires a commutative ring, not just any old ring.  If I ever need
one-sided modules, I'll just make a different category for those.
*)
(* Sorry if I forget any conditions, I'll add them if I find them *)
Record Cring := {
    cring_U : Type;
    cring_plus : Plus cring_U;
    cring_zero : Zero cring_U;
    cring_neg : Neg cring_U;
    cring_mult : Mult cring_U;
    cring_one : One cring_U;
    cring_plus_assoc : @PlusAssoc cring_U cring_plus;
    cring_plus_comm : @PlusComm cring_U cring_plus;
    cring_plus_lid : @PlusLid cring_U cring_plus cring_zero;
    cring_plus_linv : @PlusLinv cring_U cring_plus cring_zero cring_neg;
    cring_mult_assoc : @MultAssoc cring_U cring_mult;
    cring_mult_comm : @MultComm cring_U cring_mult;
    cring_mult_lid : @MultLid cring_U cring_mult cring_one;
}.
Record Module {R : Cring} := {
    module_V : Type;
    module_plus : Plus module_V;
    module_zero : Zero module_V;
    module_neg : Neg module_V;
    module_plus_assoc : @PlusAssoc module_V module_plus;
    module_plus_comm : @PlusComm module_V module_plus;
    module_plus_lid : @PlusLid module_V module_plus module_zero;
    module_plus_linv : @PlusLinv module_V module_plus module_zero module_neg;

    module_scalar : ScalarMult (cring_U R) module_V;
    module_scalar_id : @ScalarId (cring_U R) module_V (cring_one R) module_scalar;
    module_scalar_ldist : @ScalarLdist (cring_U R) module_V module_plus module_scalar;
    module_scalar_rdist : @ScalarRdist (cring_U R) module_V (cring_plus R) module_plus module_scalar;
    module_scalar_comp : @ScalarComp (cring_U R) module_V (cring_mult R) module_scalar;
}.
Arguments Module : clear implicits.

Record module_homomorphism {R : Cring} {M N : Module R} := {
    module_homo_f : module_V M → module_V N;
    module_homo_plus : ∀ u v,
        module_homo_f (plus (Plus:=module_plus M) u v) =
        plus (Plus:=module_plus N) (module_homo_f u) (module_homo_f v);
    module_homo_scalar : ∀ a v,
        module_homo_f (scalar_mult (ScalarMult:=module_scalar M) a v) =
        scalar_mult (ScalarMult:=module_scalar N) a (module_homo_f v);
}.
Arguments module_homomorphism {R} M N.

Theorem module_homomorphism_eq {R : Cring} {M N : Module R} :
        ∀ f g : module_homomorphism M N,
        (∀ x, module_homo_f f x = module_homo_f g x) → f = g.
    intros [f1 plus1 scalar1] [f2 plus2 scalar2] f_eq.
    cbn in *.
    assert (f1 = f2) as eq.
    {
        apply functional_ext.
        apply f_eq.
    }
    subst f2.
    rewrite (proof_irrelevance plus2 plus1).
    rewrite (proof_irrelevance scalar2 scalar1).
    reflexivity.
Qed.

Section ModuleCategory.

Context `{R : Cring} (L : Module R).

Let module_homo_id_f (x : module_V L) := x.

Lemma module_homo_id_plus : ∀ u v,
        module_homo_id_f (plus (Plus:=module_plus L) u v) =
        plus (Plus:=module_plus L)
            (module_homo_id_f u)
            (module_homo_id_f v).
    intros u v.
    reflexivity.
Qed.

Lemma module_homo_id_scalar : ∀ a v,
        module_homo_id_f (scalar_mult (ScalarMult:=module_scalar L) a v) =
        scalar_mult (ScalarMult:=module_scalar L) a (module_homo_id_f v).
    intros a v.
    reflexivity.
Qed.

Definition module_homo_id := {|
    module_homo_f := module_homo_id_f;
    module_homo_plus := module_homo_id_plus;
    module_homo_scalar := module_homo_id_scalar;
|}.

Context (M N : Module R).
Context (f : module_homomorphism M N) (g : module_homomorphism L M).

Let module_homo_compose_f := λ x, module_homo_f f (module_homo_f g x).

Lemma module_homo_compose_plus : ∀ u v,
        module_homo_compose_f (plus (Plus:=module_plus L) u v) =
        plus (Plus:=module_plus N)
            (module_homo_compose_f u)
            (module_homo_compose_f v).
    intros u v.
    unfold module_homo_compose_f.
    rewrite module_homo_plus.
    rewrite module_homo_plus.
    reflexivity.
Qed.

Lemma module_homo_compose_scalar : ∀ a v,
        module_homo_compose_f (scalar_mult (ScalarMult:=module_scalar L) a v) =
        scalar_mult (ScalarMult:=module_scalar N) a (module_homo_compose_f v).
    intros a v.
    unfold module_homo_compose_f.
    rewrite module_homo_scalar.
    rewrite module_homo_scalar.
    reflexivity.
Qed.

Definition module_homo_compose := {|
    module_homo_f := module_homo_compose_f;
    module_homo_plus := module_homo_compose_plus;
    module_homo_scalar := module_homo_compose_scalar;
|}.

End ModuleCategory.

Program Instance MODULE (R : Cring) : Category := {
    cat_U := Module R;
    cat_morphism M N := module_homomorphism M N;
    cat_compose {L M N} f g := module_homo_compose L M N f g;
    cat_id M := module_homo_id M;
}.
Next Obligation.
    apply module_homomorphism_eq.
    intros x.
    cbn.
    reflexivity.
Qed.
Next Obligation.
    apply module_homomorphism_eq.
    intros x.
    cbn.
    reflexivity.
Qed.
Next Obligation.
    apply module_homomorphism_eq.
    intros x.
    cbn.
    reflexivity.
Qed.
