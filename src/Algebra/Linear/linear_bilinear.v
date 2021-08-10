Require Import init.

Require Import linear_base.

(* TODO: Deal with multilinear functions in general *)
Definition bilinear {U V1 V2 V3} `{
    Plus V1, Plus V2, Plus V3,
    ScalarMult U V1,
    ScalarMult U V2,
    ScalarMult U V3
} (f : V1 → V2 → V3) :=
    (∀ a v1 v2, f (a · v1) v2 = a · (f v1 v2)) ∧
    (∀ a v1 v2, f v1 (a · v2) = a · (f v1 v2)) ∧
    (∀ v1 v2 v3, f (v1 + v2) v3 = f v1 v3 + f v2 v3) ∧
    (∀ v1 v2 v3, f v1 (v2 + v3) = f v1 v2 + f v1 v3).

Section Bilinear.

Context {U V1 V2 V3} `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    UO : One U,
    @PlusComm U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,

    V1P : Plus V1,
    V1Z : Zero V1,
    V1N : Neg V1,
    UV1 : ScalarMult U V1,
    @PlusComm V1 V1P,
    @PlusAssoc V1 V1P,
    @PlusLid V1 V1P V1Z,
    @PlusLinv V1 V1P V1Z V1N,
    @ScalarId U V1 UO UV1,
    @ScalarRdist U V1 UP V1P UV1,

    V2P : Plus V2,
    V2Z : Zero V2,
    V2N : Neg V2,
    UV2 : ScalarMult U V2,
    @PlusComm V2 V2P,
    @PlusAssoc V2 V2P,
    @PlusLid V2 V2P V2Z,
    @PlusLinv V2 V2P V2Z V2N,
    @ScalarId U V2 UO UV2,
    @ScalarRdist U V2 UP V2P UV2,

    V3P : Plus V3,
    V3Z : Zero V3,
    V3N : Neg V3,
    UV3 : ScalarMult U V3,
    @PlusComm V3 V3P,
    @PlusAssoc V3 V3P,
    @PlusLid V3 V3P V3Z,
    @PlusLinv V3 V3P V3Z V3N,
    @ScalarId U V3 UO UV3,
    @ScalarRdist U V3 UP V3P UV3
}.

Variables (f : V1 → V2 → V3) (f_bil : bilinear f).

Theorem bilinear_lscalar : ∀ a v1 v2, f (a · v1) v2 = a · (f v1 v2).
    apply f_bil.
Qed.
Theorem bilinear_rscalar : ∀ a v1 v2, f v1 (a · v2) = a · (f v1 v2).
    apply f_bil.
Qed.
Theorem bilinear_rdist : ∀ v1 v2 v3, f (v1 + v2) v3 = f v1 v3 + f v2 v3.
    apply f_bil.
Qed.
Theorem bilinear_ldist : ∀ v1 v2 v3, f v1 (v2 + v3) = f v1 v2 + f v1 v3.
    apply f_bil.
Qed.

Theorem bilinear_lanni : ∀ v, f 0 v = 0.
    intros v.
    rewrite <- (scalar_lanni 0).
    rewrite bilinear_lscalar.
    apply scalar_lanni.
Qed.

Theorem bilinear_ranni : ∀ v, f v 0 = 0.
    intros v.
    rewrite <- (scalar_lanni 0).
    rewrite bilinear_rscalar.
    apply scalar_lanni.
Qed.

Theorem bilinear_lneg : ∀ u v, f (-u) v = -(f u v).
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite bilinear_lscalar.
    rewrite scalar_neg_one.
    reflexivity.
Qed.

Theorem bilinear_rneg : ∀ u v, f u (-v) = -(f u v).
    intros u v.
    rewrite <- scalar_neg_one.
    rewrite bilinear_rscalar.
    rewrite scalar_neg_one.
    reflexivity.
Qed.

End Bilinear.
