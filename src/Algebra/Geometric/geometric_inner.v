Require Import init.

Require Import linear_extend.

Require Export geometric_base.

Section GeometricInner.

Context {F : CRingObj} {V : ModuleObj F}.
Context (B : set_type (bilinear_form (V := V))).

Let GG := geo_grade B.

Existing Instances GG.

Local Notation φ := (vector_to_geo B).
Local Notation σ := (scalar_to_geo B).
Local Notation geo := (geometric_algebra B).

Local Open Scope geo_scope.
Local Open Scope nat_scope.

Definition geo_inner_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := grade_project (a * b) (i ⊖ j).

Definition geo_lcontr_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := match j ¯ i with
       | opt_val n => grade_project (a * b) n
       | opt_nil _ => 0
       end.

Definition geo_rcontr_base i j a b (ai : of_grade i a) (bj : of_grade j b)
    := match i ¯ j with
       | opt_val n => grade_project (a * b) n
       | opt_nil _ => 0
       end.

Lemma geo_inner_ldist_base : bilinear_extend_ldist_base geo_inner_base.
Proof.
    intros u v w i j ui vj wj.
    unfold geo_inner_base.
    rewrite ldist.
    apply grade_project_plus.
Qed.

Lemma geo_inner_rdist_base : bilinear_extend_rdist_base geo_inner_base.
Proof.
    intros u v w i j ui vi wj.
    unfold geo_inner_base.
    rewrite rdist.
    apply grade_project_plus.
Qed.

Lemma geo_inner_lscalar_base : bilinear_extend_lscalar_base geo_inner_base.
Proof.
    intros a u v i j ui vj.
    unfold geo_inner_base.
    rewrite scalar_lmult.
    apply grade_project_scalar.
Qed.

Lemma geo_inner_rscalar_base : bilinear_extend_rscalar_base geo_inner_base.
Proof.
    intros a u v i j ui vj.
    unfold geo_inner_base.
    rewrite scalar_rmult.
    apply grade_project_scalar.
Qed.

Lemma geo_lcontr_ldist_base : bilinear_extend_ldist_base geo_lcontr_base.
Proof.
    intros u v w i j ui vj wj.
    unfold geo_lcontr_base.
    rewrite ldist.
    destruct (j ¯ i).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma geo_lcontr_rdist_base : bilinear_extend_rdist_base geo_lcontr_base.
Proof.
    intros u v w i j ui vi wj.
    unfold geo_lcontr_base.
    rewrite rdist.
    destruct (j ¯ i).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma geo_lcontr_lscalar_base : bilinear_extend_lscalar_base geo_lcontr_base.
Proof.
    intros a u v i j ui vj.
    unfold geo_lcontr_base.
    rewrite scalar_lmult.
    destruct (j ¯ i).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Lemma geo_lcontr_rscalar_base : bilinear_extend_rscalar_base geo_lcontr_base.
Proof.
    intros a u v i j ui vj.
    unfold geo_lcontr_base.
    rewrite scalar_rmult.
    destruct (j ¯ i).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Lemma geo_rcontr_ldist_base : bilinear_extend_ldist_base geo_rcontr_base.
Proof.
    intros u v w i j ui vj wj.
    unfold geo_rcontr_base.
    rewrite ldist.
    destruct (i ¯ j).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma geo_rcontr_rdist_base : bilinear_extend_rdist_base geo_rcontr_base.
Proof.
    intros u v w i j ui vi wj.
    unfold geo_rcontr_base.
    rewrite rdist.
    destruct (i ¯ j).
    -   apply grade_project_plus.
    -   symmetry; apply plus_rid.
Qed.

Lemma geo_rcontr_lscalar_base : bilinear_extend_lscalar_base geo_rcontr_base.
Proof.
    intros a u v i j ui vj.
    unfold geo_rcontr_base.
    rewrite scalar_lmult.
    destruct (i ¯ j).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Lemma geo_rcontr_rscalar_base : bilinear_extend_rscalar_base geo_rcontr_base.
Proof.
    intros a u v i j ui vj.
    unfold geo_rcontr_base.
    rewrite scalar_rmult.
    destruct (i ¯ j).
    -   apply grade_project_scalar.
    -   symmetry; apply scalar_ranni.
Qed.

Definition geo_inner := bilinear_extend geo_inner_base : geo → geo → geo.
Definition geo_lcontr := bilinear_extend geo_lcontr_base : geo → geo → geo.
Definition geo_rcontr := bilinear_extend geo_rcontr_base : geo → geo → geo.

(* begin show *)
Local Infix "•" := geo_inner (at level 34, left associativity).
Local Infix "⌋" := geo_lcontr (at level 34, left associativity).
Local Infix "⌊" := geo_rcontr (at level 34, left associativity).
(* end show *)

Theorem inner_ldist : ∀ a b c, a • (b + c) = a • b + a • c.
Proof.
    apply bilinear_extend_ldist.
    -   exact geo_inner_ldist_base.
    -   exact geo_inner_rscalar_base.
Qed.

Theorem inner_rdist : ∀ a b c, (a + b) • c = a • c + b • c.
Proof.
    apply bilinear_extend_rdist.
    -   exact geo_inner_rdist_base.
    -   exact geo_inner_lscalar_base.
Qed.

Theorem inner_lscalar : ∀ a u v, (a · u) • v = a · (u • v).
Proof.
    apply bilinear_extend_lscalar.
    -   apply geo_inner_rdist_base.
    -   apply geo_inner_lscalar_base.
Qed.

Theorem inner_rscalar : ∀ a u v, u • (a · v) = a · (u • v).
Proof.
    apply bilinear_extend_rscalar.
    -   apply geo_inner_ldist_base.
    -   apply geo_inner_rscalar_base.
Qed.

Theorem inner_lanni : ∀ a, 0 • a = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite inner_lscalar.
    apply scalar_lanni.
Qed.

Theorem inner_ranni : ∀ a, a • 0 = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite inner_rscalar.
    apply scalar_lanni.
Qed.

Theorem lcontr_ldist : ∀ a b c, a ⌋ (b + c) = a ⌋ b + a ⌋ c.
Proof.
    apply bilinear_extend_ldist.
    -   exact geo_lcontr_ldist_base.
    -   exact geo_lcontr_rscalar_base.
Qed.

Theorem lcontr_rdist : ∀ a b c, (a + b) ⌋ c = a ⌋ c + b ⌋ c.
Proof.
    apply bilinear_extend_rdist.
    -   exact geo_lcontr_rdist_base.
    -   exact geo_lcontr_lscalar_base.
Qed.

Theorem lcontr_lscalar : ∀ a u v, (a · u) ⌋ v = a · (u ⌋ v).
Proof.
    apply bilinear_extend_lscalar.
    -   apply geo_lcontr_rdist_base.
    -   apply geo_lcontr_lscalar_base.
Qed.

Theorem lcontr_rscalar : ∀ a u v, u ⌋ (a · v) = a · (u ⌋ v).
Proof.
    apply bilinear_extend_rscalar.
    -   apply geo_lcontr_ldist_base.
    -   apply geo_lcontr_rscalar_base.
Qed.

Theorem lcontr_lanni : ∀ a, 0 ⌋ a = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite lcontr_lscalar.
    apply scalar_lanni.
Qed.

Theorem lcontr_ranni : ∀ a, a ⌋ 0 = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite lcontr_rscalar.
    apply scalar_lanni.
Qed.

Theorem rcontr_ldist : ∀ a b c, a ⌊ (b + c) = a ⌊ b + a ⌊ c.
Proof.
    apply bilinear_extend_ldist.
    -   exact geo_rcontr_ldist_base.
    -   exact geo_rcontr_rscalar_base.
Qed.

Theorem rcontr_rdist : ∀ a b c, (a + b) ⌊ c = a ⌊ c + b ⌊ c.
Proof.
    apply bilinear_extend_rdist.
    -   exact geo_rcontr_rdist_base.
    -   exact geo_rcontr_lscalar_base.
Qed.

Theorem rcontr_lscalar : ∀ a u v, (a · u) ⌊ v = a · (u ⌊ v).
Proof.
    apply bilinear_extend_lscalar.
    -   apply geo_rcontr_rdist_base.
    -   apply geo_rcontr_lscalar_base.
Qed.

Theorem rcontr_rscalar : ∀ a u v, u ⌊ (a · v) = a · (u ⌊ v).
Proof.
    apply bilinear_extend_rscalar.
    -   apply geo_rcontr_ldist_base.
    -   apply geo_rcontr_rscalar_base.
Qed.

Theorem rcontr_lanni : ∀ a, 0 ⌊ a = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite rcontr_lscalar.
    apply scalar_lanni.
Qed.

Theorem rcontr_ranni : ∀ a, a ⌊ 0 = 0.
Proof.
    intros a.
    rewrite <- (scalar_lanni 0) at 1.
    rewrite rcontr_rscalar.
    apply scalar_lanni.
Qed.

Lemma inner_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
    u • v = geo_inner_base i j u v ui vj.
Proof.
    intros i j u v ui vj.
    unfold geo_inner.
    apply bilinear_extend_homo.
    -   exact geo_inner_ldist_base.
    -   exact geo_inner_rdist_base.
    -   exact geo_inner_lscalar_base.
    -   exact geo_inner_rscalar_base.
Qed.

Lemma lcontr_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
    u ⌋ v = geo_lcontr_base i j u v ui vj.
Proof.
    intros i j u v ui vj.
    unfold geo_lcontr.
    apply bilinear_extend_homo.
    -   exact geo_lcontr_ldist_base.
    -   exact geo_lcontr_rdist_base.
    -   exact geo_lcontr_lscalar_base.
    -   exact geo_lcontr_rscalar_base.
Qed.

Lemma rcontr_homo : ∀ i j u v (ui : of_grade i u) (vj : of_grade j v),
    u ⌊ v = geo_rcontr_base i j u v ui vj.
Proof.
    intros i j u v ui vj.
    unfold geo_rcontr.
    apply bilinear_extend_homo.
    -   exact geo_rcontr_ldist_base.
    -   exact geo_rcontr_rdist_base.
    -   exact geo_rcontr_lscalar_base.
    -   exact geo_rcontr_rscalar_base.
Qed.

Theorem lrcontr_reverse : ∀ a b, (a ⌋ b)† = b† ⌊ a†.
Proof.
    intros a b.
    induction a as [|a a' m am a'm IHa] using (grade_induction (VG := GG)).
    {
        rewrite lcontr_lanni.
        do 2 rewrite geo_reverse_zero.
        rewrite rcontr_ranni.
        reflexivity.
    }
    rewrite lcontr_rdist.
    do 2 rewrite geo_reverse_plus.
    rewrite rcontr_ldist.
    rewrite IHa.
    apply rplus; clear a' a'm IHa.
    induction b as [|b b' n bn b'n IHb] using (grade_induction (VG := GG)).
    {
        rewrite lcontr_ranni.
        do 2 rewrite geo_reverse_zero.
        rewrite rcontr_lanni.
        reflexivity.
    }
    rewrite lcontr_ldist.
    do 2 rewrite geo_reverse_plus.
    rewrite rcontr_rdist.
    rewrite IHb.
    apply rplus; clear b' b'n IHb.
    pose proof (of_grade_reverse _ _ _ am) as am'.
    pose proof (of_grade_reverse _ _ _ bn) as bn'.
    rewrite (lcontr_homo _ _ _ _ am bn).
    rewrite (rcontr_homo _ _ _ _ bn' am').
    unfold geo_lcontr_base, geo_rcontr_base.
    destruct (n ¯ m) as [z|].
    -   rewrite geo_reverse_project.
        rewrite geo_reverse_mult.
        reflexivity.
    -   apply geo_reverse_zero.
Qed.

Theorem rlcontr_reverse : ∀ a b, (a ⌊ b)† = b† ⌋ a†.
Proof.
    intros a b.
    rewrite <- (geo_reverse_reverse B (b † ⌋ a †)).
    rewrite lrcontr_reverse.
    do 2 rewrite geo_reverse_reverse.
    reflexivity.
Qed.

Theorem inner_reverse : ∀ a b, (a • b)† = b† • a†.
Proof.
    intros a b.
    induction a as [|a a' m am a'm IHa] using (grade_induction (VG := GG)).
    {
        rewrite inner_lanni.
        do 2 rewrite geo_reverse_zero.
        rewrite inner_ranni.
        reflexivity.
    }
    rewrite inner_rdist.
    do 2 rewrite geo_reverse_plus.
    rewrite inner_ldist.
    rewrite IHa.
    apply rplus; clear a' a'm IHa.
    induction b as [|b b' n bn b'n IHb] using (grade_induction (VG := GG)).
    {
        rewrite inner_ranni.
        do 2 rewrite geo_reverse_zero.
        rewrite inner_lanni.
        reflexivity.
    }
    rewrite inner_ldist.
    do 2 rewrite geo_reverse_plus.
    rewrite inner_rdist.
    rewrite IHb.
    apply rplus; clear b' b'n IHb.
    pose proof (of_grade_reverse _ _ _ am) as am'.
    pose proof (of_grade_reverse _ _ _ bn) as bn'.
    rewrite (inner_homo _ _ _ _ am bn).
    rewrite (inner_homo _ _ _ _ bn' am').
    unfold geo_inner_base, geo_inner_base.
    rewrite geo_reverse_project.
    rewrite geo_reverse_mult.
    rewrite nat_abs_minus_comm.
    reflexivity.
Qed.

Theorem lcontr_inner : ∀ a b (m n : nat), m ≤ n → of_grade m a → of_grade n b →
    a ⌋ b = a • b.
Proof.
    intros a b m n leq an bn.
    rewrite (lcontr_homo _ _ _ _ an bn).
    rewrite (inner_homo _ _ _ _ an bn).
    unfold geo_lcontr_base, geo_inner_base.
    apply nat_le_ex in leq as [c eq]; subst n.
    rewrite nat_minus_plus.
    rewrite nat_abs_minus_comm.
    rewrite nat_abs_minus_plus.
    reflexivity.
Qed.

Theorem rcontr_inner : ∀ a b (m n : nat), n ≤ m → of_grade m a → of_grade n b →
    a ⌊ b = a • b.
Proof.
    intros a b m n leq an bn.
    rewrite (rcontr_homo _ _ _ _ an bn).
    rewrite (inner_homo _ _ _ _ an bn).
    unfold geo_rcontr_base, geo_inner_base.
    apply nat_le_ex in leq as [c eq]; subst m.
    rewrite nat_minus_plus.
    rewrite nat_abs_minus_plus.
    reflexivity.
Qed.

Theorem inner_involute : ∀ a b, (a • b)∗ = a∗ • b∗.
Proof.
    intros a b.
    induction a as [|a a' m am a'm IHa] using (grade_induction (VG := GG)).
    {
        rewrite inner_lanni.
        do 2 rewrite geo_involute_zero.
        rewrite inner_lanni.
        reflexivity.
    }
    rewrite inner_rdist.
    do 2 rewrite geo_involute_plus.
    rewrite inner_rdist.
    rewrite IHa.
    apply rplus; clear a' a'm IHa.
    induction b as [|b b' n bn b'n IHb] using (grade_induction (VG := GG)).
    {
        rewrite inner_ranni.
        do 2 rewrite geo_involute_zero.
        rewrite inner_ranni.
        reflexivity.
    }
    rewrite inner_ldist.
    do 2 rewrite geo_involute_plus.
    rewrite inner_ldist.
    rewrite IHb.
    apply rplus; clear b' b'n IHb.
    pose proof (of_grade_involute _ _ _ am) as am'.
    pose proof (of_grade_involute _ _ _ bn) as bn'.
    rewrite (inner_homo _ _ _ _ am bn).
    rewrite (inner_homo _ _ _ _ am' bn').
    unfold geo_inner_base, geo_inner_base.
    rewrite geo_involute_project.
    rewrite geo_involute_mult.
    reflexivity.
Qed.

Theorem lcontr_involute : ∀ a b, (a ⌋ b)∗ = a∗ ⌋ b∗.
Proof.
    intros a b.
    induction a as [|a a' m am a'm IHa] using (grade_induction (VG := GG)).
    {
        rewrite lcontr_lanni.
        do 2 rewrite geo_involute_zero.
        rewrite lcontr_lanni.
        reflexivity.
    }
    rewrite lcontr_rdist.
    do 2 rewrite geo_involute_plus.
    rewrite lcontr_rdist.
    rewrite IHa.
    apply rplus; clear a' a'm IHa.
    induction b as [|b b' n bn b'n IHb] using (grade_induction (VG := GG)).
    {
        rewrite lcontr_ranni.
        do 2 rewrite geo_involute_zero.
        rewrite lcontr_ranni.
        reflexivity.
    }
    rewrite lcontr_ldist.
    do 2 rewrite geo_involute_plus.
    rewrite lcontr_ldist.
    rewrite IHb.
    apply rplus; clear b' b'n IHb.
    pose proof (of_grade_involute _ _ _ am) as am'.
    pose proof (of_grade_involute _ _ _ bn) as bn'.
    rewrite (lcontr_homo _ _ _ _ am bn).
    rewrite (lcontr_homo _ _ _ _ am' bn').
    unfold geo_lcontr_base, geo_lcontr_base.
    destruct (n ¯ m) as [z|].
    -   rewrite geo_involute_project.
        rewrite geo_involute_mult.
        reflexivity.
    -   apply geo_involute_zero.
Qed.

Theorem rcontr_involute : ∀ a b, (a ⌊ b)∗ = a∗ ⌊ b∗.
Proof.
    intros a b.
    rewrite <- (geo_reverse_reverse B ((a ⌊ b)∗)).
    rewrite <- geo_reverse_involute.
    rewrite rlcontr_reverse.
    rewrite lcontr_involute.
    do 2 rewrite geo_reverse_involute.
    rewrite <- rlcontr_reverse.
    apply geo_reverse_reverse.
Qed.

(* begin hide *)
End GeometricInner.

(* end hide *)
Infix "•" := (geo_inner _) (at level 34, left associativity) : geo_scope.
Infix "⌋" := (geo_lcontr _) (at level 34, left associativity) : geo_scope.
Infix "⌊" := (geo_rcontr _) (at level 34, left associativity) : geo_scope.
