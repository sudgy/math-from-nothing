Require Import init.

Require Export linear_base.
Require Export category_base.

(** I don't know if this is the best way to define this, but I'll try it for now
*)

(** This requires a commutative ring, not just any old ring.  If I ever need
one-sided modules, I'll just make a different category for those.
*)
(* Sorry if I forget any conditions, I'll add them if I find them *)
Class CRing := make_cring {
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
    cring_ldist : @Ldist cring_U cring_plus cring_mult;
}.
Class Module `(R : CRing) := make_module {
    module_V : Type;
    module_plus : Plus module_V;
    module_zero : Zero module_V;
    module_neg : Neg module_V;
    module_plus_assoc : @PlusAssoc module_V module_plus;
    module_plus_comm : @PlusComm module_V module_plus;
    module_plus_lid : @PlusLid module_V module_plus module_zero;
    module_plus_linv : @PlusLinv module_V module_plus module_zero module_neg;

    module_scalar : ScalarMult cring_U module_V;
    module_scalar_id : @ScalarId cring_U module_V cring_one module_scalar;
    module_scalar_ldist : @ScalarLdist cring_U module_V module_plus module_scalar;
    module_scalar_rdist : @ScalarRdist cring_U module_V cring_plus module_plus module_scalar;
    module_scalar_comp : @ScalarComp cring_U module_V cring_mult module_scalar;
}.
Arguments module_V {R} Module.
Arguments module_plus {R} Module.
Arguments module_zero {R} Module.
Arguments module_neg {R} Module.
Arguments module_plus_assoc {R} Module.
Arguments module_plus_comm {R} Module.
Arguments module_plus_lid {R} Module.
Arguments module_plus_linv {R} Module.
Arguments module_scalar {R} Module.
Arguments module_scalar_id {R} Module.
Arguments module_scalar_ldist {R} Module.
Arguments module_scalar_rdist {R} Module.
Arguments module_scalar_comp {R} Module.

Class ModuleHomomorphism `{R : CRing} `(M : @Module R, N : @Module R) := make_module_homomorphism {
    module_homo_f : module_V M → module_V N;
    module_homo_plus : ∀ u v,
        module_homo_f (plus (Plus:=module_plus M) u v) =
        plus (Plus:=module_plus N) (module_homo_f u) (module_homo_f v);
    module_homo_scalar : ∀ a v,
        module_homo_f (scalar_mult (ScalarMult:=module_scalar M) a v) =
        scalar_mult (ScalarMult:=module_scalar N) a (module_homo_f v);
}.
Arguments module_homo_f {R M N} ModuleHomomorphism.

Theorem module_homomorphism_eq {R : CRing} {M N : Module R} :
        ∀ f g : ModuleHomomorphism M N,
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

Program Instance module_homo_id `{R : CRing} (L : Module R)
    : ModuleHomomorphism L L :=
{
    module_homo_f x := x
}.

Program Instance module_homo_compose `{R : CRing}
    `{L : @Module R, M : @Module R, N : @Module R}
    (f : ModuleHomomorphism M N) (g : ModuleHomomorphism L M)
    : ModuleHomomorphism L N :=
{
    module_homo_f x := module_homo_f f (module_homo_f g x)
}.
Next Obligation.
    rewrite module_homo_plus.
    rewrite module_homo_plus.
    reflexivity.
Qed.
Next Obligation.
    rewrite module_homo_scalar.
    rewrite module_homo_scalar.
    reflexivity.
Qed.

Program Instance MODULE (R : CRing) : Category := {
    cat_U := Module R;
    cat_morphism M N := ModuleHomomorphism M N;
    cat_compose {L M N} f g := module_homo_compose f g;
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

Section ModuleCategoryObjects.

Context U `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UPA : @PlusAssoc U UP,
    UPC : @PlusComm U UP,
    UPZ : @PlusLid U UP UZ,
    UPN : @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    UMA : @MultAssoc U UM,
    UMC : @MultComm U UM,
    UMO : @MultLid U UM UO,
    UMD : @Ldist U UP UM
}.

Definition scalar_cring := make_cring U UP UZ UN UM UO UPA UPC UPZ UPN UMA UMC UMO UMD.

Local Instance USM : ScalarMult U U := {
    scalar_mult a b := a * b
}.
Local Program Instance USMO : ScalarId U U.
Next Obligation.
    apply mult_lid.
Qed.
Local Program Instance USML : ScalarLdist U U.
Next Obligation.
    apply ldist.
Qed.
Local Program Instance USMR : ScalarRdist U U.
Next Obligation.
    apply rdist.
Qed.
Local Program Instance USMC : ScalarComp U U.
Next Obligation.
    apply mult_assoc.
Qed.

Definition scalar_module := make_module scalar_cring U UP UZ UN UPA UPC UPZ UPN USM USMO USML USMR USMC.

Context V `{
    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    VPA : @PlusAssoc V VP,
    VPC : @PlusComm V VP,
    VPZ : @PlusLid V VP VZ,
    VPN : @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    SMO : @ScalarId U V UO SM,
    SML : @ScalarLdist U V VP SM,
    SMR : @ScalarRdist U V UP VP SM,
    SMC : @ScalarComp U V UM SM
}.

Definition vector_module := make_module scalar_cring V VP VZ VN VPA VPC VPZ VPN SM SMO SML SMR SMC.

End ModuleCategoryObjects.
