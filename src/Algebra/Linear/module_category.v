Require Import init.

Require Export linear_base.
Require Export category_base.

(** I don't know if this is the best way to define this, but I'll try it for now
*)

(** This requires a commutative ring, not just any old ring.  If I ever need
one-sided modules, I'll just make a different category for those.
*)
(* Sorry if I forget any conditions, I'll add them if I find them *)
Record CRing := make_cring {
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
Record Module (R : CRing) := make_module {
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

Record ModuleHomomorphism {R : CRing} (M : Module R) (N : Module R) := make_module_homomorphism {
    module_homo_f : module_V M → module_V N;
    module_homo_plus : ∀ u v,
        module_homo_f (plus (Plus:=module_plus M) u v) =
        plus (Plus:=module_plus N) (module_homo_f u) (module_homo_f v);
    module_homo_scalar : ∀ a v,
        module_homo_f (scalar_mult (ScalarMult:=module_scalar M) a v) =
        scalar_mult (ScalarMult:=module_scalar N) a (module_homo_f v);
}.
Arguments module_homo_f {R M N}.

Theorem module_homo_zero {R : CRing} {M N : Module R} :
        ∀ f : ModuleHomomorphism M N,
        module_homo_f f (@zero _ (module_zero M)) = (@zero _ (module_zero N)).
    intros f.
    pose (UP := cring_plus).
    pose (UZ := cring_zero).
    pose (UPZ := cring_plus_lid).
    pose (MP := module_plus M).
    pose (MZ := module_zero M).
    pose (MN := module_neg M).
    pose (MPC := module_plus_comm M).
    pose (MPA := module_plus_assoc M).
    pose (MPZ := module_plus_lid M).
    pose (MPN := module_plus_linv M).
    pose (MSM := module_scalar M).
    pose (MSMR := module_scalar_rdist M).
    pose (NP := module_plus N).
    pose (NZ := module_zero N).
    pose (NN := module_neg N).
    pose (NPC := module_plus_comm N).
    pose (NPA := module_plus_assoc N).
    pose (NPZ := module_plus_lid N).
    pose (NPN := module_plus_linv N).
    pose (NSM := module_scalar N).
    pose (NSMR := module_scalar_rdist N).
    rewrite <- (scalar_lanni 0).
    rewrite (@module_homo_scalar _ _ _ f).
    apply scalar_lanni.
Qed.

Theorem module_homo_neg {R : CRing} {M N : Module R} :
        ∀ f : ModuleHomomorphism M N,
        ∀ v, module_homo_f f (@neg _ (module_neg M) v)
        = (@neg _ (module_neg N) (module_homo_f f v)).
    intros f v.
    pose (UP := cring_plus).
    pose (UZ := cring_zero).
    pose (UN := cring_neg).
    pose (UPC := cring_plus_comm).
    pose (UPZ := cring_plus_lid).
    pose (UPN := cring_plus_linv).
    pose (UO := cring_one).
    pose (MP := module_plus M).
    pose (MZ := module_zero M).
    pose (MPC := module_plus_comm M).
    pose (MPA := module_plus_assoc M).
    pose (MPZ := module_plus_lid M).
    pose (MPN := module_plus_linv M).
    pose (MSM := module_scalar M).
    pose (MSMO := module_scalar_id M).
    pose (MSMR := module_scalar_rdist M).
    pose (NP := module_plus N).
    pose (NZ := module_zero N).
    pose (NPC := module_plus_comm N).
    pose (NPA := module_plus_assoc N).
    pose (NPZ := module_plus_lid N).
    pose (NPN := module_plus_linv N).
    pose (NSM := module_scalar N).
    pose (NSMO := module_scalar_id N).
    pose (NSMR := module_scalar_rdist N).
    rewrite <- scalar_neg_one.
    rewrite (@module_homo_scalar _ _ _ f).
    apply scalar_neg_one.
Qed.

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

Definition module_homo_id {R : CRing} (L : Module R)
    : ModuleHomomorphism L L := make_module_homomorphism R L L
        (λ x, x)
        (λ u v, Logic.eq_refl _)
        (λ a v, Logic.eq_refl _).

Lemma module_homo_compose_plus : ∀ {R : CRing} {L M N : Module R}
        {f : ModuleHomomorphism M N} {g : ModuleHomomorphism L M},
        ∀ a b, module_homo_f f (module_homo_f g (@plus _ (module_plus L) a b)) =
        @plus _ (module_plus N) (module_homo_f f (module_homo_f g a))
        (module_homo_f f (module_homo_f g b)).
    intros R L M N f g a b.
    rewrite module_homo_plus.
    apply module_homo_plus.
Qed.
Lemma module_homo_compose_scalar : ∀ {R : CRing} {L M N : Module R}
        {f : ModuleHomomorphism M N} {g : ModuleHomomorphism L M},
        ∀ a v, module_homo_f f (module_homo_f g
            (@scalar_mult _ _ (module_scalar L) a v)) =
        @scalar_mult _ _ (module_scalar N)
            a (module_homo_f f (module_homo_f g v)).
    intros R L M N f g a v.
    rewrite module_homo_scalar.
    apply module_homo_scalar.
Qed.
Definition module_homo_compose {R : CRing} {L M N : Module R}
    (f : ModuleHomomorphism M N) (g : ModuleHomomorphism L M) 
    : ModuleHomomorphism L N := make_module_homomorphism R L N
        (λ x, module_homo_f f (module_homo_f g x))
        module_homo_compose_plus module_homo_compose_scalar.

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

Instance scalar_scalar_mult : ScalarMult U U := {
    scalar_mult a b := a * b
}.
Program Instance scalar_scalar_id : ScalarId U U.
Next Obligation.
    apply mult_lid.
Qed.
Program Instance scalar_scalar_ldist : ScalarLdist U U.
Next Obligation.
    apply ldist.
Qed.
Program Instance scalar_scalar_rdist : ScalarRdist U U.
Next Obligation.
    apply rdist.
Qed.
Program Instance scalar_scalar_comp : ScalarComp U U.
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

End ModuleCategoryObjects.

Definition cring_module (C : CRing) := make_module C (cring_U C) (cring_plus C)
    (cring_zero C) (cring_neg C) (cring_plus_assoc C) (cring_plus_comm C)
    (cring_plus_lid C) (cring_plus_linv C)
    (@scalar_scalar_mult (cring_U C) (cring_mult C))
    (@scalar_scalar_id (cring_U C) (cring_mult C) (cring_one C) (cring_mult_lid C))
    (@scalar_scalar_ldist (cring_U C) (cring_plus C) (cring_mult C) (cring_ldist C))
    (@scalar_scalar_rdist (cring_U C) (cring_plus C) (cring_mult C) (cring_mult_comm C) (cring_ldist C))
    (@scalar_scalar_comp (cring_U C) (cring_mult C) (cring_mult_assoc C))
.
