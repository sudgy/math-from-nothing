Require Import init.

Require Export linear_base.
Require Export category_base.
Require Export ring_category.
(** This requires a commutative ring, not just any old ring.  If I ever need
one-sided modules, I'll just make a different category for those.
*)
Record ModuleObj (R : CRingObj) := make_module {
    module_V :> Type;
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
Arguments module_V {R}.
Arguments module_plus {R}.
Arguments module_zero {R}.
Arguments module_neg {R}.
Arguments module_plus_assoc {R}.
Arguments module_plus_comm {R}.
Arguments module_plus_lid {R}.
Arguments module_plus_linv {R}.
Arguments module_scalar {R}.
Arguments module_scalar_id {R}.
Arguments module_scalar_ldist {R}.
Arguments module_scalar_rdist {R}.
Arguments module_scalar_comp {R}.

Global Existing Instances module_plus module_zero module_neg module_plus_assoc
    module_plus_comm module_plus_lid module_plus_linv module_scalar
    module_scalar_id module_scalar_ldist module_scalar_rdist module_scalar_comp.

Record ModuleObjHomomorphism {R : CRingObj} (M : ModuleObj R) (N : ModuleObj R) := make_module_homomorphism {
    module_homo_f :> M → N;
    module_homo_plus : ∀ u v,
        module_homo_f (u + v) = module_homo_f u + module_homo_f v;
    module_homo_scalar : ∀ a v,
        module_homo_f (a · v) = a · module_homo_f v;
}.
Arguments module_homo_f {R M N}.

Theorem module_homo_zero {R : CRingObj} {M N : ModuleObj R} :
    ∀ f : ModuleObjHomomorphism M N, f 0 = 0.
Proof.
    intros f.
    rewrite <- (scalar_lanni 0).
    rewrite module_homo_scalar.
    apply scalar_lanni.
Qed.

Theorem module_homo_neg {R : CRingObj} {M N : ModuleObj R} :
    ∀ f : ModuleObjHomomorphism M N,
    ∀ v, f (-v) = -f v.
Proof.
    intros f v.
    rewrite <- scalar_neg_one.
    rewrite (@module_homo_scalar _ _ _ f).
    apply scalar_neg_one.
Qed.

Theorem module_homomorphism_eq {R : CRingObj} {M N : ModuleObj R} :
    ∀ f g : ModuleObjHomomorphism M N,
    (∀ x, f x = g x) → f = g.
Proof.
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

Definition module_homo_id {R : CRingObj} (L : ModuleObj R)
    : ModuleObjHomomorphism L L := make_module_homomorphism R L L
        (λ x, x)
        (λ u v, Logic.eq_refl _)
        (λ a v, Logic.eq_refl _).

Lemma module_homo_compose_plus : ∀ {R : CRingObj} {L M N : ModuleObj R}
    {f : ModuleObjHomomorphism M N} {g : ModuleObjHomomorphism L M},
    ∀ a b, f (g (a + b)) = f (g a) + f (g b).
Proof.
    intros R L M N f g a b.
    rewrite module_homo_plus.
    apply module_homo_plus.
Qed.
Lemma module_homo_compose_scalar : ∀ {R : CRingObj} {L M N : ModuleObj R}
    {f : ModuleObjHomomorphism M N} {g : ModuleObjHomomorphism L M},
    ∀ a v, f (g (a · v)) = a · (f (g v)).
Proof.
    intros R L M N f g a v.
    rewrite module_homo_scalar.
    apply module_homo_scalar.
Qed.
Definition module_homo_compose {R : CRingObj} {L M N : ModuleObj R}
    (f : ModuleObjHomomorphism M N) (g : ModuleObjHomomorphism L M) 
    : ModuleObjHomomorphism L N := make_module_homomorphism R L N
        (λ x, f (g x))
        module_homo_compose_plus module_homo_compose_scalar.

Program Definition Module (R : CRingObj) : Category := {|
    cat_U := ModuleObj R;
    morphism M N := ModuleObjHomomorphism M N;
    cat_compose L M N f g := module_homo_compose f g;
    cat_id M := module_homo_id M;
|}.
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

Section ModuleObjCategoryObjects.

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

Definition scalar_cring := make_cring
    U UP UZ UN UM UPA UPC UPZ UPN UMA UMD UO UMO UMC.

Local Instance scalar_scalar_mult : ScalarMult U U := {
    scalar_mult a b := a * b
}.
Local Program Instance scalar_scalar_id : ScalarId U U.
Next Obligation.
    apply mult_lid.
Qed.
Local Program Instance scalar_scalar_ldist : ScalarLdist U U.
Next Obligation.
    apply ldist.
Qed.
Local Program Instance scalar_scalar_rdist : ScalarRdist U U.
Next Obligation.
    apply rdist.
Qed.
Local Program Instance scalar_scalar_comp : ScalarComp U U.
Next Obligation.
    apply mult_assoc.
Qed.

Definition scalar_module := make_module scalar_cring U UP UZ UN UPA UPC UPZ UPN scalar_scalar_mult scalar_scalar_id scalar_scalar_ldist scalar_scalar_rdist scalar_scalar_comp.

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

End ModuleObjCategoryObjects.

Definition cring_module (C : CRingObj) := make_module C (cring_U C) (cring_plus C)
    (cring_zero C) (cring_neg C) (cring_plus_assoc C) (cring_plus_comm C)
    (cring_plus_lid C) (cring_plus_linv C)
    (@scalar_scalar_mult (cring_U C) (cring_mult C))
    (@scalar_scalar_id (cring_U C) (cring_mult C) (cring_one C) (cring_mult_lid C))
    (@scalar_scalar_ldist (cring_U C) (cring_plus C) (cring_mult C) (cring_ldist C))
    (@scalar_scalar_rdist (cring_U C) (cring_plus C) (cring_mult C) (cring_mult_comm C) (cring_ldist C))
    (@scalar_scalar_comp (cring_U C) (cring_mult C) (cring_mult_assoc C))
.
