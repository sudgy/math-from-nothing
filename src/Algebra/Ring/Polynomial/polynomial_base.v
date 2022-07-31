Require Import init.

Require Import linear_free.
Require Import linear_grade.
Require Import module_category.
Require Import algebra_category.
Require Import nat.
Require Import set.
Require Import unordered_list.
Require Import mult_pow.
Require Import linear_grade_sum.

Section Polynomial.

Context (F : CRingObj).
Let U := cring_U F.
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
Existing Instances UP UZ UN UPA UPC UPZ UPN UM UO UMA UMC UMO UMD.
Context `{
    UML : @MultLcancel U UZ UM,
    UMR : @MultRcancel U UZ UM,
    UD : Div U,
    UMDL : @MultLinv U UZ UM UO UD,
    UMDR : @MultRinv U UZ UM UO UD,
    @NotTrivial U
}.

Definition polynomial_module := free_linear F nat.
Definition polynomial := module_V polynomial_module : Type.
Definition polynomial_plus := module_plus polynomial_module : Plus polynomial.
Definition polynomial_zero := module_zero polynomial_module : Zero polynomial.
Definition polynomial_neg := module_neg polynomial_module : Neg polynomial.
Definition polynomial_plus_comm := module_plus_comm polynomial_module : PlusComm polynomial.
Definition polynomial_plus_assoc := module_plus_assoc polynomial_module : PlusAssoc polynomial.
Definition polynomial_plus_lid := module_plus_lid polynomial_module : PlusLid polynomial.
Definition polynomial_plus_linv := module_plus_linv polynomial_module : PlusLinv polynomial.
Definition polynomial_scalar := module_scalar polynomial_module : ScalarMult U polynomial.
Definition polynomial_scalar_id := module_scalar_id polynomial_module : ScalarId U polynomial.
Definition polynomial_scalar_ldist := module_scalar_ldist polynomial_module : ScalarLdist U polynomial.
Definition polynomial_scalar_rdist := module_scalar_rdist polynomial_module : ScalarRdist U polynomial.
Definition polynomial_scalar_comp := module_scalar_comp polynomial_module : ScalarComp U polynomial.
Definition polynomial_grade := free_grade F nat : GradedSpace U polynomial.
Local Existing Instances polynomial_plus polynomial_zero polynomial_neg
    polynomial_plus_comm polynomial_plus_assoc polynomial_plus_lid
    polynomial_plus_linv polynomial_scalar polynomial_scalar_id
    polynomial_scalar_ldist polynomial_scalar_rdist polynomial_scalar_comp
    polynomial_grade.

Definition polynomial_xn (n : nat) := to_free F nat n.

Theorem polynomial_xn_ex : ∀ (n : nat) (f : polynomial),
        of_grade n f → ∃ α, f = α · polynomial_xn n.
    intros n f fn.
    apply to_free_ex in fn as [α eq]; subst f.
    exists α.
    unfold polynomial_xn.
    reflexivity.
Qed.

Local Instance polynomial_mult : Mult polynomial := {
    mult := free_bilinear F nat (λ m n, polynomial_xn (m + n));
}.

Theorem polynomial_xn_mult : ∀ m n,
    polynomial_xn m * polynomial_xn n = polynomial_xn (m + n).
Proof.
    intros m n.
    unfold mult; cbn.
    rewrite (free_bilinear_free F nat).
    reflexivity.
Qed.

Local Program Instance polynomial_ldist : Ldist polynomial.
Next Obligation.
    apply (free_bilinear_ldist F nat).
Qed.
Local Program Instance polynomial_mult_assoc : MultAssoc polynomial.
Next Obligation.
    unfold mult; cbn.

    rewrite (grade_decomposition_eq a).
    remember (grade_decomposition a) as l; clear Heql.
    induction l as [|v l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite (free_bilinear_lanni F nat).
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    do 3 rewrite (free_bilinear_rdist F nat).
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    destruct v as [v [i vi]]; cbn.
    apply polynomial_xn_ex in vi as [α v_eq]; subst v.
    do 3 rewrite (free_bilinear_lscalar F nat).
    apply f_equal; clear α.

    rewrite (grade_decomposition_eq b).
    remember (grade_decomposition b) as l; clear Heql.
    induction l as [|v l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite (free_bilinear_lanni F nat).
        do 2 rewrite (free_bilinear_ranni F nat).
        rewrite (free_bilinear_lanni F nat).
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite (free_bilinear_rdist F nat).
    do 2 rewrite (free_bilinear_ldist F nat).
    rewrite (free_bilinear_rdist F nat).
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    destruct v as [v [j vj]]; cbn.
    apply polynomial_xn_ex in vj as [α v_eq]; subst v.
    rewrite (free_bilinear_lscalar F nat).
    do 2 rewrite (free_bilinear_rscalar F nat).
    rewrite (free_bilinear_lscalar F nat).
    apply f_equal; clear α.

    rewrite (grade_decomposition_eq c).
    remember (grade_decomposition c) as l; clear Heql.
    induction l as [|v l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 3 rewrite (free_bilinear_ranni F nat).
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    do 3 rewrite (free_bilinear_ldist F nat).
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    destruct v as [v [k vk]]; cbn.
    apply polynomial_xn_ex in vk as [α v_eq]; subst v.
    do 3 rewrite (free_bilinear_rscalar F nat).
    apply f_equal; clear α.

    do 4 rewrite (free_bilinear_free F nat).
    rewrite plus_assoc.
    reflexivity.
Qed.
Local Program Instance polynomial_mult_comm : MultComm polynomial.
Next Obligation.
    unfold mult; cbn.

    rewrite (grade_decomposition_eq a).
    remember (grade_decomposition a) as l; clear Heql.
    induction l as [|v l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite (free_bilinear_lanni F nat).
        rewrite (free_bilinear_ranni F nat).
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite (free_bilinear_ldist F nat).
    rewrite (free_bilinear_rdist F nat).
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    destruct v as [v [i vi]]; cbn.
    apply polynomial_xn_ex in vi as [α v_eq]; subst v.
    rewrite (free_bilinear_lscalar F nat).
    rewrite (free_bilinear_rscalar F nat).
    apply f_equal; clear α.

    rewrite (grade_decomposition_eq b).
    remember (grade_decomposition b) as l; clear Heql.
    induction l as [|v l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite (free_bilinear_lanni F nat).
        rewrite (free_bilinear_ranni F nat).
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite (free_bilinear_ldist F nat).
    rewrite (free_bilinear_rdist F nat).
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    destruct v as [v [j vj]]; cbn.
    apply polynomial_xn_ex in vj as [α v_eq]; subst v.
    rewrite (free_bilinear_lscalar F nat).
    rewrite (free_bilinear_rscalar F nat).
    apply f_equal; clear α.
    do 2 rewrite (free_bilinear_free F nat).
    rewrite plus_comm.
    reflexivity.
Qed.
Local Instance polynomial_one : One polynomial := {
    one := polynomial_xn 0
}.
Local Program Instance polynomial_mult_lid : MultLid polynomial.
Next Obligation.
    rewrite mult_comm.
    unfold mult, one; cbn.
    rewrite (grade_decomposition_eq a).
    remember (grade_decomposition a) as l; clear Heql.
    induction l as [|v l] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        apply (free_bilinear_lanni F nat).
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite (free_bilinear_rdist F nat).
    rewrite IHl; clear IHl.
    apply rplus; clear l.
    destruct v as [v [i vi]]; cbn.
    apply polynomial_xn_ex in vi as [α v_eq]; subst v.
    rewrite (free_bilinear_lscalar F nat).
    apply f_equal.
    rewrite (free_bilinear_free F nat).
    rewrite plus_rid.
    reflexivity.
Qed.
Local Program Instance polynomial_scalar_lmult : ScalarLMult U polynomial.
Next Obligation.
    apply (free_bilinear_lscalar F nat).
Qed.
Local Program Instance polynomial_scalar_rmult : ScalarRMult U polynomial.
Next Obligation.
    apply (free_bilinear_rscalar F nat).
Qed.

Definition to_polynomial (a : U) := a · 1.
Definition polynomial_x := polynomial_xn 1.

Theorem to_polynomial_eq : ∀ a b, to_polynomial a = to_polynomial b → a = b.
Proof.
    intros a b eq.
    unfold to_polynomial in eq.
    apply scalar_rcancel in eq.
    1: exact eq.
    intros contr.
    unfold one in contr; cbn in contr.
    unfold polynomial_xn, to_free in contr.
    rewrite <- (single_to_grade_sum_zero nat _ 0) in contr.
    apply single_to_grade_sum_eq in contr.
    apply not_trivial_one.
    exact contr.
Qed.

Theorem to_polynomial_plus : ∀ a b,
    to_polynomial (a + b) = to_polynomial a + to_polynomial b.
Proof.
    intros a b.
    unfold to_polynomial.
    apply scalar_rdist.
Qed.

Theorem to_polynomial_neg : ∀ a, to_polynomial (-a) = -to_polynomial a.
Proof.
    intros a.
    unfold to_polynomial.
    apply scalar_lneg.
Qed.

Theorem to_polynomial_mult : ∀ a b,
    to_polynomial (a * b) = to_polynomial a * to_polynomial b.
Proof.
    intros a b.
    unfold to_polynomial.
    rewrite scalar_lmult, scalar_rmult.
    rewrite scalar_comp.
    unfold mult at 3; cbn.
    rewrite (free_bilinear_free F nat).
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem to_polynomial_zero : to_polynomial 0 = 0.
Proof.
    unfold to_polynomial; cbn.
    apply scalar_lanni.
Qed.

Theorem to_polynomial_one : to_polynomial 1 = 1.
Proof.
    unfold to_polynomial; cbn.
    rewrite scalar_id.
    unfold one; cbn.
    reflexivity.
Qed.

Theorem to_polynomial_scalar : ∀ a f, to_polynomial a * f = a · f.
Proof.
    intros a f.
    unfold to_polynomial.
    rewrite scalar_lmult.
    rewrite mult_lid.
    reflexivity.
Qed.

Theorem to_polynomial_comm : ∀ a f, to_polynomial a * f = f * to_polynomial a.
Proof.
    intros a f.
    unfold to_polynomial.
    rewrite scalar_lmult, scalar_rmult.
    rewrite mult_lid, mult_rid.
    reflexivity.
Qed.

Theorem polynomial_xn_grade : ∀ n : nat, of_grade n (polynomial_xn n).
Proof.
    intros n.
    unfold polynomial_xn.
    unfold to_free.
    unfold of_grade; cbn.
    unfold grade_sum_subspace_set.
    exists 1.
    reflexivity.
Qed.

Theorem to_polynomial_grade : ∀ a, of_grade 0 (to_polynomial a).
    intros a.
    unfold to_polynomial.
    apply of_grade_scalar.
    unfold one; cbn.
    apply polynomial_xn_grade.
Qed.

Let USM := module_scalar (cring_module F).
Let USML := module_scalar_ldist (cring_module F).
Let USMR := module_scalar_rdist (cring_module F).
Let USMC := module_scalar_comp (cring_module F).
Let USMO := module_scalar_id (cring_module F).

Local Existing Instances USM USML USMR USMC USMO.

Definition polynomial_eval (f : polynomial) (x : U)
    := free_extend F nat (pow_nat x) f : U.

Theorem polynomial_eval_constant :
    ∀ a x : U, polynomial_eval (to_polynomial a) x = a.
Proof.
    intros a x.
    unfold polynomial_eval, to_polynomial.
    rewrite (free_extend_scalar F nat).
    rewrite (free_extend_free F nat).
    unfold zero; cbn.
    unfold scalar_mult; cbn.
    apply mult_rid.
Qed.

Theorem polynomial_eval_zero : ∀ x, polynomial_eval 0 x = 0.
    intros x.
    rewrite <- to_polynomial_zero.
    apply polynomial_eval_constant.
Qed.

Theorem polynomial_eval_xn : ∀ x n,
    polynomial_eval (polynomial_xn n) x = (x^n)%nat.
Proof.
    intros x n.
    unfold polynomial_eval, polynomial_xn.
    rewrite (free_extend_free F nat).
    reflexivity.
Qed.

Theorem polynomial_eval_x : ∀ x : U, polynomial_eval polynomial_x x = x.
Proof.
    intros x.
    unfold polynomial_x.
    rewrite polynomial_eval_xn.
    apply pow_1_nat.
Qed.

Theorem polynomial_eval_plus : ∀ f g x,
    polynomial_eval (f + g) x = polynomial_eval f x + polynomial_eval g x.
Proof.
    intros f g x.
    unfold polynomial_eval.
    apply (free_extend_plus F nat).
Qed.

Theorem polynomial_eval_neg : ∀ f x,
    polynomial_eval (-f) x = -polynomial_eval f x.
Proof.
    intros f x.
    unfold polynomial_eval.
    apply (free_extend_neg F nat).
Qed.

Theorem polynomial_eval_scalar : ∀ f a x,
    polynomial_eval (a · f) x = a * polynomial_eval f x.
Proof.
    intros f a x.
    unfold polynomial_eval.
    rewrite (free_extend_scalar F nat).
    unfold scalar_mult; cbn.
    reflexivity.
Qed.

Theorem polynomial_eval_mult : ∀ f g x,
    polynomial_eval (f * g) x = polynomial_eval f x * polynomial_eval g x.
Proof.
    intros f g x.
    induction f as [|f f' m fm f'm IHf] using grade_induction.
    {
        rewrite mult_lanni.
        rewrite <- to_polynomial_zero.
        rewrite (polynomial_eval_constant 0 x).
        rewrite mult_lanni.
        reflexivity.
    }
    rewrite rdist.
    do 2 rewrite polynomial_eval_plus.
    rewrite IHf.
    rewrite rdist.
    apply rplus.
    clear f' f'm IHf.
    induction g as [|g g' n gn g'n IHg] using grade_induction.
    {
        rewrite mult_ranni.
        rewrite <- to_polynomial_zero.
        rewrite (polynomial_eval_constant 0 x).
        rewrite mult_ranni.
        reflexivity.
    }
    rewrite ldist.
    do 2 rewrite polynomial_eval_plus.
    rewrite IHg.
    rewrite ldist.
    apply rplus.
    clear g' g'n IHg.
    apply polynomial_xn_ex in fm as [a f_eq].
    apply polynomial_xn_ex in gn as [b g_eq].
    subst f g.
    rewrite scalar_lmult, scalar_rmult.
    do 4 rewrite polynomial_eval_scalar.
    rewrite <- mult_assoc.
    do 2 rewrite (mult_assoc _ b).
    rewrite (mult_comm (_ _ _) b).
    do 2 rewrite mult_assoc.
    rewrite <- (mult_assoc (a * b)).
    apply f_equal.
    unfold mult at 1; cbn.
    rewrite (free_bilinear_free F nat).
    unfold polynomial_eval.
    do 3 rewrite (free_extend_free F nat).
    rewrite pow_mult_nat.
    reflexivity.
Qed.

Definition polynomial_rng := make_rng polynomial polynomial_plus polynomial_zero
    polynomial_neg polynomial_mult polynomial_plus_assoc polynomial_plus_comm
    polynomial_plus_lid
    polynomial_plus_linv
    polynomial_mult_assoc
    polynomial_ldist.
Definition polynomial_ring := make_ring polynomial_rng polynomial_one
    polynomial_mult_lid.
Definition polynomial_cring := make_cring polynomial_ring polynomial_mult_comm.
Definition polynomial_algebra := make_algebra F polynomial_module
    polynomial_mult polynomial_ldist ldist_rdist polynomial_mult_assoc
    polynomial_one polynomial_mult_lid mult_lid_rid polynomial_scalar_lmult
    polynomial_scalar_rmult.

End Polynomial.

Arguments polynomial_eval {F}.
Arguments polynomial : simpl never.
Arguments polynomial_plus : simpl never.
Arguments polynomial_zero : simpl never.
Arguments polynomial_neg : simpl never.
Arguments polynomial_plus_comm : simpl never.
Arguments polynomial_plus_assoc : simpl never.
Arguments polynomial_plus_lid : simpl never.
Arguments polynomial_plus_linv : simpl never.
Arguments polynomial_scalar : simpl never.
Arguments polynomial_scalar_id : simpl never.
Arguments polynomial_scalar_ldist : simpl never.
Arguments polynomial_scalar_rdist : simpl never.
Arguments polynomial_scalar_comp : simpl never.
Arguments polynomial_grade : simpl never.
Arguments polynomial_mult : simpl never.
Arguments polynomial_ldist : simpl never.
Arguments polynomial_mult_assoc : simpl never.
Arguments polynomial_mult_comm : simpl never.
Arguments polynomial_one : simpl never.
Arguments polynomial_mult_lid : simpl never.
Arguments polynomial_scalar_lmult : simpl never.
Arguments polynomial_scalar_rmult : simpl never.
