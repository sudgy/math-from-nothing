Require Import init.

Require Export linear_base.
Require Import module_category.
Require Import algebra_category.

Section LinearTransformationSpace.

Variables V1 V2 : Type.

Context {U} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @MultAssoc U UM,
    @MultLid U UM UO,

    VP1 : Plus V1,
    VZ1 : Zero V1,
    VN1 : Neg V1,
    VPC1 : @PlusComm V1 VP1,
    VPA1 : @PlusAssoc V1 VP1,
    @PlusLid V1 VP1 VZ1,
    @PlusLinv V1 VP1 VZ1 VN1,

    SM1 : ScalarMult U V1,
    @ScalarId U V1 UO SM1,
    @ScalarLdist U V1 VP1 SM1,
    @ScalarRdist U V1 UP VP1 SM1,
    @ScalarComp U V1 UM SM1,

    VP2 : Plus V2,
    VZ2 : Zero V2,
    VN2 : Neg V2,
    VPC2 : @PlusComm V2 VP2,
    VPA2 : @PlusAssoc V2 VP2,
    @PlusLid V2 VP2 VZ2,
    @PlusLinv V2 VP2 VZ2 VN2,

    SM2 : ScalarMult U V2,
    @ScalarId U V2 UO SM2,
    @ScalarLdist U V2 VP2 SM2,
    @ScalarRdist U V2 UP VP2 SM2,
    @ScalarComp U V2 UM SM2
}.

Local Instance linear_func_plus : Plus (V1 → V2) := {
    plus f g := λ x, f x + g x
}.

Local Instance linear_func_zero : Zero (V1 → V2) := {
    zero := λ x, 0
}.

Local Instance linear_func_neg : Neg (V1 → V2) := {
    neg f := λ x, -f x
}.

Local Program Instance linear_func_plus_comm : PlusComm (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply plus_comm.
Qed.

Local Program Instance linear_func_plus_assoc : PlusAssoc (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply plus_assoc.
Qed.

Local Program Instance linear_func_plus_lid : PlusLid (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply plus_lid.
Qed.

Local Program Instance linear_func_plus_linv : PlusLinv (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply plus_linv.
Qed.

Local Instance linear_func_scalar : ScalarMult U (V1 → V2) := {
    scalar_mult a f := λ x, a · f x
}.

Local Program Instance linear_func_scalar_id : ScalarId U (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply scalar_id.
Qed.

Local Program Instance linear_func_scalar_ldist : ScalarLdist U (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply scalar_ldist.
Qed.

Local Program Instance linear_func_scalar_rdist : ScalarRdist U (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply scalar_rdist.
Qed.

Local Program Instance linear_func_scalar_comp : ScalarComp U (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply scalar_comp.
Qed.

End LinearTransformationSpace.

Section LinearTransformationModuleObj.

Context {F : CRingObj} (V1 V2 : ModuleObj F).

Let UP := cring_plus F.
Let UZ := cring_zero F.
Let UN := cring_neg F.
Let UPA := cring_plus_assoc F.
Let UPC := cring_plus_comm F.
Let UPZ := cring_plus_lid F.
Let UPN := cring_plus_linv F.
Let UM := cring_mult F.
Let UO := cring_one F.
Let UMA := cring_mult_assoc F.
Let UMC := cring_mult_comm F.
Let UMO := cring_mult_lid F.
Let UMD := cring_ldist F.
Let VP1 := module_plus V1.
Let VZ1 := module_zero V1.
Let VN1 := module_neg V1.
Let VPA1 := module_plus_assoc V1.
Let VPC1 := module_plus_comm V1.
Let VPZ1 := module_plus_lid V1.
Let VPN1 := module_plus_linv V1.
Let SM1 := module_scalar V1.
Let SMO1 := module_scalar_id V1.
Let SML1 := module_scalar_ldist V1.
Let SMR1 := module_scalar_rdist V1.
Let SMC1 := module_scalar_comp V1.
Let VP2 := module_plus V2.
Let VZ2 := module_zero V2.
Let VN2 := module_neg V2.
Let VPA2 := module_plus_assoc V2.
Let VPC2 := module_plus_comm V2.
Let VPZ2 := module_plus_lid V2.
Let VPN2 := module_plus_linv V2.
Let SM2 := module_scalar V2.
Let SMO2 := module_scalar_id V2.
Let SML2 := module_scalar_ldist V2.
Let SMR2 := module_scalar_rdist V2.
Let SMC2 := module_scalar_comp V2.
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD VP1 VZ1 VN1
    VPA1 VPC1 VPZ1 VPN1 SM1 SMO1 SML1 SMR1 SMC1 VP2 VZ2 VN2 VPA2 VPC2 VPZ2 VPN2
    SM2 SMO2 SML2 SMR2 SMC2.

Definition linear_trans_plus_base (f g : ModuleObjHomomorphism V1 V2) :=
    λ v, module_homo_f f v + module_homo_f g v.

Lemma linear_trans_plus_plus : ∀ f g, ∀ u v,
    linear_trans_plus_base f g (u + v) =
    linear_trans_plus_base f g u + linear_trans_plus_base f g v.
Proof.
    intros f g u v.
    unfold linear_trans_plus_base.
    rewrite (module_homo_plus _ _ f).
    rewrite (module_homo_plus _ _ g).
    do 2 rewrite <- plus_assoc.
    apply lplus.
    do 2 rewrite plus_assoc.
    apply rplus.
    apply plus_comm.
Qed.

Lemma linear_trans_plus_scalar : ∀ f g, ∀ a v,
    linear_trans_plus_base f g (a · v) = a · linear_trans_plus_base f g v.
Proof.
    intros f g a v.
    unfold linear_trans_plus_base.
    rewrite (module_homo_scalar _ _ f).
    rewrite (module_homo_scalar _ _ g).
    symmetry; apply scalar_ldist.
Qed.

Instance linear_trans_plus : Plus (ModuleObjHomomorphism V1 V2) := {
    plus f g := make_module_homomorphism F V1 V2
        (linear_trans_plus_base f g)
        (linear_trans_plus_plus f g)
        (linear_trans_plus_scalar f g)
}.

Definition linear_trans_zero_base := λ v : module_V V1, 0 : module_V V2.

Lemma linear_trans_zero_plus : ∀ u v,
    linear_trans_zero_base (u + v) =
    linear_trans_zero_base u + linear_trans_zero_base v.
Proof.
    intros u v.
    unfold linear_trans_zero_base.
    rewrite plus_rid.
    reflexivity.
Qed.

Lemma linear_trans_zero_scalar : ∀ a v,
    linear_trans_zero_base (a · v) = a · linear_trans_zero_base v.
Proof.
    intros a v.
    unfold linear_trans_zero_base.
    rewrite scalar_ranni.
    reflexivity.
Qed.

Instance linear_trans_zero : Zero (ModuleObjHomomorphism V1 V2) := {
    zero := make_module_homomorphism F V1 V2
        linear_trans_zero_base
        linear_trans_zero_plus
        linear_trans_zero_scalar
}.

Definition linear_trans_neg_base (f : ModuleObjHomomorphism V1 V2) :=
    λ v, -module_homo_f f v.

Lemma linear_trans_neg_plus : ∀ f, ∀ u v,
    linear_trans_neg_base f (u + v) =
    linear_trans_neg_base f u + linear_trans_neg_base f v.
Proof.
    intros f u v.
    unfold linear_trans_neg_base.
    rewrite (module_homo_plus _ _ f).
    apply neg_plus.
Qed.

Lemma linear_trans_neg_scalar : ∀ f, ∀ a v,
    linear_trans_neg_base f (a · v) = a · linear_trans_neg_base f v.
Proof.
    intros f a v.
    unfold linear_trans_neg_base.
    rewrite (module_homo_scalar _ _ f).
    symmetry; apply scalar_rneg.
Qed.

Instance linear_trans_neg : Neg (ModuleObjHomomorphism V1 V2) := {
    neg f := make_module_homomorphism F V1 V2
        (linear_trans_neg_base f)
        (linear_trans_neg_plus f)
        (linear_trans_neg_scalar f)
}.

Program Instance linear_trans_plus_assoc : PlusAssoc (ModuleObjHomomorphism V1 V2).
Next Obligation.
    apply module_homomorphism_eq.
    intros v.
    unfold plus; cbn.
    unfold linear_trans_plus_base; cbn.
    apply plus_assoc.
Qed.

Program Instance linear_trans_plus_comm : PlusComm (ModuleObjHomomorphism V1 V2).
Next Obligation.
    apply module_homomorphism_eq.
    intros v.
    unfold plus; cbn.
    unfold linear_trans_plus_base; cbn.
    apply plus_comm.
Qed.

Program Instance linear_trans_plus_lid : PlusLid (ModuleObjHomomorphism V1 V2).
Next Obligation.
    apply module_homomorphism_eq.
    intros v.
    unfold plus, zero; cbn.
    unfold linear_trans_plus_base, linear_trans_zero_base; cbn.
    apply plus_lid.
Qed.

Program Instance linear_trans_plus_linv : PlusLinv (ModuleObjHomomorphism V1 V2).
Next Obligation.
    apply module_homomorphism_eq.
    intros v.
    unfold plus, zero, neg; cbn.
    unfold linear_trans_plus_base, linear_trans_zero_base,
        linear_trans_neg_base; cbn.
    apply plus_linv.
Qed.

Definition linear_trans_scalar_base a (f : ModuleObjHomomorphism V1 V2) :=
    λ v, a · module_homo_f f v.

Lemma linear_trans_scalar_plus : ∀ a f, ∀ u v,
    linear_trans_scalar_base a f (u + v) =
    linear_trans_scalar_base a f u + linear_trans_scalar_base a f v.
Proof.
    intros a f u v.
    unfold linear_trans_scalar_base.
    rewrite (module_homo_plus _ _ f).
    apply scalar_ldist.
Qed.

Lemma linear_trans_scalar_scalar : ∀ a f, ∀ b v,
    linear_trans_scalar_base a f (b · v) =
    b · linear_trans_scalar_base a f v.
Proof.
    intros a f b v.
    unfold linear_trans_scalar_base.
    rewrite (module_homo_scalar _ _ f).
    do 2 rewrite scalar_comp.
    rewrite mult_comm.
    reflexivity.
Qed.

Instance linear_trans_scalar : ScalarMult (cring_U F) (ModuleObjHomomorphism V1 V2)
:= {
    scalar_mult a f := make_module_homomorphism F V1 V2
        (linear_trans_scalar_base a f)
        (linear_trans_scalar_plus a f)
        (linear_trans_scalar_scalar a f)
}.

Program Instance linear_trans_scalar_id
    : ScalarId (cring_U F) (ModuleObjHomomorphism V1 V2).
Next Obligation.
    apply module_homomorphism_eq.
    intros u.
    unfold scalar_mult; cbn.
    unfold linear_trans_scalar_base.
    apply scalar_id.
Qed.

Program Instance linear_trans_scalar_ldist
    : ScalarLdist (cring_U F) (ModuleObjHomomorphism V1 V2).
Next Obligation.
    apply module_homomorphism_eq.
    intros w.
    unfold scalar_mult, plus; cbn.
    unfold linear_trans_scalar_base, linear_trans_plus_base; cbn.
    apply scalar_ldist.
Qed.

Program Instance linear_trans_scalar_rdist
    : ScalarRdist (cring_U F) (ModuleObjHomomorphism V1 V2).
Next Obligation.
    apply module_homomorphism_eq.
    intros u.
    unfold scalar_mult, plus at 2; cbn.
    unfold linear_trans_scalar_base, linear_trans_plus_base; cbn.
    apply scalar_rdist.
Qed.

Program Instance linear_trans_scalar_comp
    : ScalarComp (cring_U F) (ModuleObjHomomorphism V1 V2).
Next Obligation.
    apply module_homomorphism_eq.
    intros u.
    unfold scalar_mult; cbn.
    unfold linear_trans_scalar_base; cbn.
    apply scalar_comp.
Qed.

Definition linear_trans_module := make_module
    F
    (ModuleObjHomomorphism V1 V2)
    linear_trans_plus
    linear_trans_zero
    linear_trans_neg
    linear_trans_plus_assoc
    linear_trans_plus_comm
    linear_trans_plus_lid
    linear_trans_plus_linv
    linear_trans_scalar
    linear_trans_scalar_id
    linear_trans_scalar_ldist
    linear_trans_scalar_rdist
    linear_trans_scalar_comp
.

End LinearTransformationModuleObj.

Section LinearTransformationAlgebraObj.

Context {F : CRingObj} (V : ModuleObj F).

Let VP := module_plus V.
Let VS := module_scalar V.

Existing Instances VP VS.

Let TP := linear_trans_plus V V.
Let TS := linear_trans_scalar V V.

Existing Instances TP TS.

Definition linear_trans_mult_base (f g : ModuleObjHomomorphism V V) :=
    λ v, module_homo_f f (module_homo_f g v).

Lemma linear_trans_mult_plus : ∀ f g, ∀ u v,
    linear_trans_mult_base f g (u + v) =
    linear_trans_mult_base f g u + linear_trans_mult_base f g v.
Proof.
    intros f g u v.
    unfold linear_trans_mult_base.
    rewrite (module_homo_plus _ _ g).
    apply module_homo_plus.
Qed.

Lemma linear_trans_mult_scalar : ∀ f g, ∀ a v,
    linear_trans_mult_base f g (a · v) = a · linear_trans_mult_base f g v.
Proof.
    intros f g a v.
    unfold linear_trans_mult_base.
    rewrite (module_homo_scalar _ _ g).
    apply module_homo_scalar.
Qed.

Instance linear_trans_mult : Mult (ModuleObjHomomorphism V V) := {
    mult f g := make_module_homomorphism F V V
        (linear_trans_mult_base f g)
        (linear_trans_mult_plus f g)
        (linear_trans_mult_scalar f g)
}.

Program Instance linear_trans_ldist : Ldist (ModuleObjHomomorphism V V).
Next Obligation.
    apply module_homomorphism_eq.
    intros v.
    unfold plus, mult; cbn.
    unfold linear_trans_mult_base, linear_trans_plus_base; cbn.
    apply module_homo_plus.
Qed.

Program Instance linear_trans_rdist : Rdist (ModuleObjHomomorphism V V).
Next Obligation.
    apply module_homomorphism_eq.
    intros v.
    unfold plus, mult; cbn.
    unfold linear_trans_mult_base, linear_trans_plus_base; cbn.
    reflexivity.
Qed.

Program Instance linear_trans_mult_assoc : MultAssoc (ModuleObjHomomorphism V V).
Next Obligation.
    apply module_homomorphism_eq.
    intros v.
    unfold mult; cbn.
    unfold linear_trans_mult_base; cbn.
    reflexivity.
Qed.

Instance linear_trans_one : One (ModuleObjHomomorphism V V) := {
    one := module_homo_id V
}.

Program Instance linear_trans_mult_lid : MultLid (ModuleObjHomomorphism V V).
Next Obligation.
    apply module_homomorphism_eq.
    intros v.
    unfold one, mult; cbn.
    reflexivity.
Qed.

Program Instance linear_trans_mult_rid : MultRid (ModuleObjHomomorphism V V).
Next Obligation.
    apply module_homomorphism_eq.
    intros v.
    unfold one, mult; cbn.
    reflexivity.
Qed.

Program Instance linear_trans_scalar_lmult
    : ScalarLMult (cring_U F) (ModuleObjHomomorphism V V).
Next Obligation.
    apply module_homomorphism_eq.
    intros w.
    unfold scalar_mult, mult; cbn.
    unfold linear_trans_scalar_base, linear_trans_mult_base; cbn.
    reflexivity.
Qed.

Program Instance linear_trans_scalar_rmult
    : ScalarRMult (cring_U F) (ModuleObjHomomorphism V V).
Next Obligation.
    apply module_homomorphism_eq.
    intros w.
    unfold scalar_mult, mult; cbn.
    unfold linear_trans_scalar_base, linear_trans_mult_base; cbn.
    apply module_homo_scalar.
Qed.


Definition linear_trans_algebra := make_algebra
    F
    (linear_trans_module V V)
    linear_trans_mult
    linear_trans_ldist
    linear_trans_rdist
    linear_trans_mult_assoc
    linear_trans_one
    linear_trans_mult_lid
    linear_trans_mult_rid
    linear_trans_scalar_lmult
    linear_trans_scalar_rmult
.

End LinearTransformationAlgebraObj.
