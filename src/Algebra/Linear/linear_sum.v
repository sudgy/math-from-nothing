Require Import init.

Require Export linear_base.
Require Export module_category.

(* begin hide *)
Section DirectSum.

(* end hide *)
Context {F : CRing} (V1 V2 : Module F).

(* begin hide *)
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

(* end hide *)
Instance direct_sum_plus : Plus (module_V V1 * module_V V2) := {
    plus a b := (fst a + fst b, snd a + snd b)
}.

Instance direct_sum_zero : Zero (module_V V1 * module_V V2) := {
    zero := (0, 0)
}.

Instance direct_sum_neg : Neg (module_V V1 * module_V V2) := {
    neg a := (-fst a, -snd a)
}.

Program Instance direct_sum_plus_assoc : PlusAssoc (module_V V1 * module_V V2).
Next Obligation.
    unfold plus; cbn.
    do 2 rewrite plus_assoc.
    reflexivity.
Qed.

Program Instance direct_sum_plus_comm : PlusComm (module_V V1 * module_V V2).
Next Obligation.
    unfold plus; cbn.
    rewrite (plus_comm (fst b)).
    rewrite (plus_comm (snd b)).
    reflexivity.
Qed.

Program Instance direct_sum_plus_lid : PlusLid (module_V V1 * module_V V2).
Next Obligation.
    unfold plus, zero; cbn.
    do 2 rewrite plus_lid.
    destruct a; reflexivity.
Qed.

Program Instance direct_sum_plus_linv : PlusLinv (module_V V1 * module_V V2).
Next Obligation.
    unfold plus, neg, zero; cbn.
    do 2 rewrite plus_linv.
    reflexivity.
Qed.

Instance direct_sum_scalar : ScalarMult (cring_U F) (module_V V1 * module_V V2)
:= {
    scalar_mult a v := (a · fst v, a · snd v)
}.

Program Instance direct_sum_scalar_id
    : ScalarId (cring_U F) (module_V V1 * module_V V2).
Next Obligation.
    unfold scalar_mult; cbn.
    do 2 rewrite scalar_id.
    destruct v; reflexivity.
Qed.

Program Instance direct_sum_scalar_ldist
    : ScalarLdist (cring_U F) (module_V V1 * module_V V2).
Next Obligation.
    unfold scalar_mult, plus; cbn.
    do 2 rewrite scalar_ldist.
    reflexivity.
Qed.

Program Instance direct_sum_scalar_rdist
    : ScalarRdist (cring_U F) (module_V V1 * module_V V2).
Next Obligation.
    unfold scalar_mult, plus at 2; cbn.
    do 2 rewrite scalar_rdist.
    reflexivity.
Qed.

Program Instance direct_sum_scalar_comp
    : ScalarComp (cring_U F) (module_V V1 * module_V V2).
Next Obligation.
    unfold scalar_mult; cbn.
    do 2 rewrite scalar_comp.
    reflexivity.
Qed.

Definition direct_sum := make_module
    F
    (module_V V1 * module_V V2)
    direct_sum_plus
    direct_sum_zero
    direct_sum_neg
    direct_sum_plus_assoc
    direct_sum_plus_comm
    direct_sum_plus_lid
    direct_sum_plus_linv
    direct_sum_scalar
    direct_sum_scalar_id
    direct_sum_scalar_ldist
    direct_sum_scalar_rdist
    direct_sum_scalar_comp
.
(* begin hide *)

End DirectSum.
(* end hide *)
