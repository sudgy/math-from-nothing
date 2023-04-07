Require Import init.

Require Export mult_field.
Require Export unordered_list.

#[universes(template)]
Class ScalarMult U V := {
    scalar_mult : U → V → V
}.
Infix "·" := scalar_mult : algebra_scope.
Arguments scalar_mult : simpl never.

Class ScalarComp U V `{Mult U, ScalarMult U V} := {
    scalar_comp : ∀ a b v, a · (b · v) = (a * b) · v
}.

Class ScalarId U V `{One U, ScalarMult U V} := {
    scalar_id : ∀ v, 1 · v = v
}.

Class ScalarLdist U V `{Plus V, ScalarMult U V} := {
    scalar_ldist : ∀ a u v, a · (u + v) = a · u + a · v
}.
Class ScalarRdist U V `{Plus U, Plus V, ScalarMult U V} := {
    scalar_rdist : ∀ a b v, (a + b) · v = a · v + b · v
}.

Class ScalarLMult U V `{Mult V, ScalarMult U V} := {
    scalar_lmult : ∀ a u v, (a · u) * v = a · (u * v)
}.
Class ScalarRMult U V `{Mult V, ScalarMult U V} := {
    scalar_rmult : ∀ a u v, u * (a · v) = a · (u * v)
}.

Class ModuleClass U V `{
    MR : CRingClass U,
    MG : AbelianGroupClass V,
    SM : ScalarMult U V,
    SMC : @ScalarComp U V UM SM,
    SME : @ScalarId U V UE SM,
    SML : @ScalarLdist U V UP0 SM,
    SMR : @ScalarRdist U V UP UP0 SM
}.

Class VectorSpaceClass U V `{
    VF : FieldClass U,
    VG : AbelianGroupClass V,
    SM : ScalarMult U V,
    SMC : @ScalarComp U V UM SM,
    SME : @ScalarId U V UE SM,
    SML : @ScalarLdist U V UP0 SM,
    SMR : @ScalarRdist U V UP UP0 SM
}.

Class AlgebraClass U V `{
    AR : CRingClass U,
    AR : RingClass V,
    SM : ScalarMult U V,
    SMC : @ScalarComp U V UM SM,
    SME : @ScalarId U V UE SM,
    SML : @ScalarLdist U V UP0 SM,
    SMR : @ScalarRdist U V UP UP0 SM,
    SMLM : @ScalarLMult U V UM0 SM,
    SMRM : @ScalarRMult U V UM0 SM
}.

Class AlgebraFieldClass U V `{
    AF : FieldClass U,
    AR : RingClass V,
    SM : ScalarMult U V,
    SMC : @ScalarComp U V UM SM,
    SME : @ScalarId U V UE SM,
    SML : @ScalarLdist U V UP0 SM,
    SMR : @ScalarRdist U V UP UP0 SM,
    SMLM : @ScalarLMult U V UM0 SM,
    SMRM : @ScalarRMult U V UM0 SM
}.

(* begin hide *)
Section LinearBase.

Context {U V} `{AlgebraFieldClass U V}.

(* end hide *)
Theorem lscalar : ∀ {u v} a, u = v → a · u = a · v.
Proof.
    intros u v a eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem rscalar : ∀ {a b} v, a = b → a · v = b · v.
Proof.
    intros u v a eq.
    rewrite eq.
    reflexivity.
Qed.
Theorem lrscalar : ∀ {a b u v}, a = b → u = v → a · u = b · v.
Proof.
    intros a b u v eq1 eq2.
    apply lscalar with b in eq2.
    apply rscalar with u in eq1.
    rewrite eq1, <- eq2.
    reflexivity.
Qed.

Theorem scalar_lanni : ∀ v, 0 · v = 0.
Proof.
    intros v.
    assert (0 · v = 0 · v) as eq by reflexivity.
    rewrite <- (plus_lid 0) in eq at 1.
    rewrite scalar_rdist in eq.
    apply plus_0_a_ab_b in eq.
    symmetry; exact eq.
Qed.

Theorem scalar_ranni : ∀ a, a · 0 = 0.
Proof.
    intros a.
    assert (a · 0 = a · 0) as eq by reflexivity.
    rewrite <- (plus_lid 0) in eq at 1.
    rewrite scalar_ldist in eq.
    apply plus_0_a_ab_b in eq.
    symmetry; exact eq.
Qed.

Theorem scalar_lneg : ∀ a b, -a · b = -(a · b).
Proof.
    intros a b.
    apply plus_lcancel with (a · b).
    rewrite <- scalar_rdist.
    do 2 rewrite plus_rinv.
    apply scalar_lanni.
Qed.

Theorem scalar_rneg : ∀ a b, a · -b = -(a · b).
Proof.
    intros a b.
    apply plus_lcancel with (a · b).
    rewrite <- scalar_ldist.
    do 2 rewrite plus_rinv.
    apply scalar_ranni.
Qed.

Theorem scalar_neg_one : ∀ a, (-(1)) · a = -a.
Proof.
    intros a.
    rewrite scalar_lneg.
    rewrite scalar_id.
    reflexivity.
Qed.

Theorem scalar_lcancel : ∀ {a b} c, 0 ≠ c → c · a = c · b → a = b.
Proof.
    intros a b c c_nz eq.
    apply lscalar with (/c) in eq.
    do 2 rewrite scalar_comp in eq.
    rewrite mult_linv in eq by exact c_nz.
    do 2 rewrite scalar_id in eq.
    exact eq.
Qed.

Theorem scalar_rcancel : ∀ {a b} c, 0 ≠ c → a · c = b · c → a = b.
Proof.
    intros a b c c_nz eq.
    rewrite <- plus_0_anb_a_b in eq.
    rewrite <- scalar_lneg in eq.
    rewrite <- scalar_rdist in eq.
    classic_contradiction contr.
    rewrite <- (scalar_ranni (a - b)) in eq.
    apply scalar_lcancel in eq; [>contradiction|].
    intros contr2.
    rewrite plus_0_anb_a_b in contr2.
    contradiction.
Qed.

Theorem list_sum_scalar : ∀ a l,
    list_sum (list_image (scalar_mult a) l) = a · list_sum l.
Proof.
    intros a l.
    induction l as [|v l].
    {
        rewrite list_image_end.
        rewrite list_sum_end.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite list_image_add.
    do 2 rewrite list_sum_add.
    rewrite IHl.
    rewrite scalar_ldist.
    reflexivity.
Qed.

Theorem ulist_sum_scalar : ∀ a l,
    ulist_sum (ulist_image (scalar_mult a) l) = a · ulist_sum l.
Proof.
    intros a l.
    induction l as [|v l] using ulist_induction.
    {
        rewrite ulist_image_end.
        rewrite ulist_sum_end.
        rewrite scalar_ranni.
        reflexivity.
    }
    rewrite ulist_image_add.
    do 2 rewrite ulist_sum_add.
    rewrite IHl.
    rewrite scalar_ldist.
    reflexivity.
Qed.

(* begin hide *)
End LinearBase.
(* end hide *)
