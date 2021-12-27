Require Import init.

Require Export linear_base.

Section LinearTransformationSpace.

Context {U V1 V2} `{
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

Local Instance linear_trans_plus : Plus (V1 → V2) := {
    plus f g := λ x, f x + g x
}.

Local Instance linear_trans_zero : Zero (V1 → V2) := {
    zero := λ x, 0
}.

Local Instance linear_trans_neg : Neg (V1 → V2) := {
    neg f := λ x, -f x
}.

Local Program Instance linear_trans_plus_comm : PlusComm (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply plus_comm.
Qed.

Local Program Instance linear_trans_plus_assoc : PlusAssoc (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply plus_assoc.
Qed.

Local Program Instance linear_trans_plus_lid : PlusLid (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply plus_lid.
Qed.

Local Program Instance linear_trans_plus_linv : PlusLinv (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply plus_linv.
Qed.

Local Instance linear_trans_scalar : ScalarMult U (V1 → V2) := {
    scalar_mult a f := λ x, a · f x
}.

Local Program Instance linear_trans_scalar_id : ScalarId U (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply scalar_id.
Qed.

Local Program Instance linear_trans_scalar_ldist : ScalarLdist U (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply scalar_ldist.
Qed.

Local Program Instance linear_trans_scalar_rdist : ScalarRdist U (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply scalar_rdist.
Qed.

Local Program Instance linear_trans_scalar_comp : ScalarComp U (V1 → V2).
Next Obligation.
    apply functional_ext.
    intros x.
    apply scalar_comp.
Qed.

End LinearTransformationSpace.
