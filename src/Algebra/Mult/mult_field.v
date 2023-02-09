Require Import init.

Require Export mult_ring.

#[universes(template)]
Class Div U := {
    div : U → U
}.

Notation "/ a" := (div a) : algebra_scope.
Notation "a / b" := (a * /b) : algebra_scope.

Class MultLinv U `{Zero U, Mult U, One U, Div U} := {
    mult_linv : ∀ a, 0 ≠ a → /a * a = 1
}.
Class MultRinv U `{Zero U, Mult U, One U, Div U} := {
    mult_rinv : ∀ a, 0 ≠ a → a / a = 1
}.

Class FieldBase U `{
    FM : AllMult U,
    UD : Div U,
    UMD : @MultLinv U UZ UM UE UD,
    UMDR : @MultRinv U UZ UM UE UD
}.

Class Field U `{
    FF : FieldBase U,
    NotTrivial U
}.

Class HomomorphismDiv {U V} `{Zero U, Div U, Div V} (f : U → V) := {
    homo_div : ∀ a, 0 ≠ a → f (/a) = /f a
}.

(* begin hide *)
Arguments div : simpl never.

Section FieldImply1.

Context {U} `{Field U}.

Global Instance mult_linv_rinv : MultRinv U.
Proof.
    split.
    intros a a_nz.
    rewrite mult_comm.
    apply mult_linv.
    exact a_nz.
Qed.

End FieldImply1.

Section FieldImply2.

Context {U} `{Field U}.

Global Instance mult_linv_lcancel : MultLcancel U.
Proof.
    split.
    intros a b c c_nz eq.
    apply lmult with (/c) in eq.
    do 2 rewrite mult_assoc in eq.
    rewrite mult_linv in eq by exact c_nz.
    do 2 rewrite mult_lid in eq.
    exact eq.
Qed.

Global Instance mult_rinv_rcancel : MultRcancel U.
Proof.
    split.
    intros a b c c_nz eq.
    apply rmult with (/c) in eq.
    do 2 rewrite <- mult_assoc in eq.
    rewrite mult_rinv in eq by exact c_nz.
    do 2 rewrite mult_rid in eq.
    exact eq.
Qed.

End FieldImply2.

Section Field.

Context {U} `{Field U}.

(* end hide *)
Theorem div_nz : ∀ a, 0 ≠ a → 0 ≠ /a.
Proof.
    intros a a_nz eq.
    apply rmult with a in eq.
    rewrite mult_lanni in eq.
    rewrite mult_linv in eq by exact a_nz.
    exact (not_trivial_one eq).
Qed.

Theorem div_div : ∀ a, 0 ≠ a → /(/a) = a.
Proof.
    intros a a_nz.
    pose proof (div_nz a a_nz) as a'_nz.
    apply mult_lcancel with (/a); [>exact a'_nz|].
    rewrite mult_linv by exact a_nz.
    rewrite mult_rinv by exact a'_nz.
    reflexivity.
Qed.

Theorem mult_rrinv : ∀ a b, 0 ≠ b → a * b / b = a.
Proof.
    intros a b b_nz.
    rewrite <- mult_assoc.
    rewrite mult_rinv by exact b_nz.
    apply mult_rid.
Qed.
Theorem mult_rlinv : ∀ a b, 0 ≠ b → a / b * b = a.
Proof.
    intros a b b_nz.
    rewrite <- mult_assoc.
    rewrite mult_linv by exact b_nz.
    apply mult_rid.
Qed.
Theorem mult_lrinv : ∀ a b, 0 ≠ b → b * (/b * a) = a.
Proof.
    intros a b b_nz.
    rewrite mult_assoc.
    rewrite mult_rinv by exact b_nz.
    apply mult_lid.
Qed.
Theorem mult_llinv : ∀ a b, 0 ≠ b → /b * (b * a) = a.
Proof.
    intros a b b_nz.
    rewrite mult_assoc.
    rewrite mult_linv by exact b_nz.
    apply mult_lid.
Qed.

Theorem mult_llmove : ∀ a b c, 0 ≠ a → a * b = c ↔ b = /a * c.
Proof.
    intros a b c a_nz.
    split; intros eq.
    -   apply lmult with (/a) in eq.
        rewrite mult_llinv in eq by exact a_nz.
        exact eq.
    -   apply lmult with a in eq.
        rewrite mult_lrinv in eq by exact a_nz.
        exact eq.
Qed.
Theorem mult_lrmove : ∀ a b c, 0 ≠ b → a * b = c ↔ a = c / b.
Proof.
    intros a b c b_nz.
    split; intros eq.
    -   apply rmult with (/b) in eq.
        rewrite mult_rrinv in eq by exact b_nz.
        exact eq.
    -   apply rmult with b in eq.
        rewrite mult_rlinv in eq by exact b_nz.
        exact eq.
Qed.
Theorem mult_rlmove : ∀ a b c, 0 ≠ b → a = b * c ↔ /b * a = c.
Proof.
    intros a b c b_nz.
    split; intros eq.
    -   apply lmult with (/b) in eq.
        rewrite mult_llinv in eq by exact b_nz.
        exact eq.
    -   apply lmult with b in eq.
        rewrite mult_lrinv in eq by exact b_nz.
        exact eq.
Qed.
Theorem mult_rrmove : ∀ a b c, 0 ≠ c → a = b * c ↔ a / c = b.
Proof.
    intros a b c c_nz.
    split; intros eq.
    -   apply rmult with (/c) in eq.
        rewrite mult_rrinv in eq by exact c_nz.
        exact eq.
    -   apply rmult with c in eq.
        rewrite mult_rlinv in eq by exact c_nz.
        exact eq.
Qed.

Theorem mult_1_ab_da_b : ∀ a b, 0 ≠ a → 1 = a * b ↔ /a = b.
Proof.
    intros a b a_nz.
    rewrite mult_rlmove by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem mult_1_ab_db_a : ∀ a b, 0 ≠ b → 1 = a * b ↔ /b = a.
Proof.
    intros a b b_nz.
    rewrite mult_rrmove by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem mult_1_ab_a_db : ∀ a b, 0 ≠ b → 1 = a * b ↔ a = /b.
Proof.
    intros a b b_nz.
    rewrite mult_rrmove by exact b_nz.
    rewrite mult_lid.
    apply eq_iff.
Qed.
Theorem mult_1_ab_b_da : ∀ a b, 0 ≠ a → 1 = a * b ↔ b = /a.
Proof.
    intros a b a_nz.
    rewrite mult_rlmove by exact a_nz.
    rewrite mult_rid.
    apply eq_iff.
Qed.

Theorem mult_1_a_ab_b : ∀ a b, 0 ≠ b → 1 = a ↔ a * b = b.
Proof.
    intros a b b_nz.
    rewrite mult_lrmove by exact b_nz.
    rewrite mult_rinv by exact b_nz.
    apply eq_iff.
Qed.
Theorem mult_1_a_ba_b : ∀ a b, 0 ≠ b → 1 = a ↔ b * a = b.
Proof.
    intros a b b_nz.
    rewrite mult_llmove by exact b_nz.
    rewrite mult_linv by exact b_nz.
    apply eq_iff.
Qed.
Theorem mult_1_a_b_ab : ∀ a b, 0 ≠ b → 1 = a ↔ b = a * b.
Proof.
    intros a b b_nz.
    rewrite mult_rrmove by exact b_nz.
    rewrite mult_rinv by exact b_nz.
    reflexivity.
Qed.
Theorem mult_1_a_b_ba : ∀ a b, 0 ≠ b → 1 = a ↔ b = b * a.
Proof.
    intros a b b_nz.
    rewrite mult_rlmove by exact b_nz.
    rewrite mult_linv by exact b_nz.
    reflexivity.
Qed.

Theorem mult_1_dab_a_b : ∀ a b, 0 ≠ a → 1 = /a * b ↔ a = b.
Proof.
    intros a b a_nz.
    rewrite mult_1_ab_da_b by (apply div_nz; exact a_nz).
    rewrite div_div by exact a_nz.
    reflexivity.
Qed.
Theorem mult_1_adb_a_b : ∀ a b, 0 ≠ b → 1 = a / b ↔ a = b.
Proof.
    intros a b b_nz.
    rewrite mult_1_ab_a_db by (apply div_nz; exact b_nz).
    rewrite div_div by exact b_nz.
    reflexivity.
Qed.
Theorem mult_1_dab_b_a : ∀ a b, 0 ≠ a → 1 = /a * b ↔ b = a.
Proof.
    intros a b a_nz.
    rewrite mult_1_ab_b_da by (apply div_nz; exact a_nz).
    rewrite div_div by exact a_nz.
    reflexivity.
Qed.
Theorem mult_1_adb_b_a : ∀ a b, 0 ≠ b → 1 = a / b ↔ b = a.
Proof.
    intros a b b_nz.
    rewrite mult_1_ab_db_a by (apply div_nz; exact b_nz).
    rewrite div_div by exact b_nz.
    reflexivity.
Qed.

Theorem neg_div : ∀ a, 0 ≠ a → /(-a) = -/a.
Proof.
    intros a a_nz.
    pose proof (land (neg_nz _) a_nz) as na_nz.
    apply mult_rcancel with (-a); [>exact na_nz|].
    rewrite mult_linv by exact na_nz.
    rewrite mult_lneg, mult_rneg, neg_neg.
    rewrite mult_linv by exact a_nz.
    reflexivity.
Qed.

Theorem div_mult : ∀ a b, 0 ≠ a → 0 ≠ b → /(a * b) = /a * /b.
Proof.
    intros a b a_nz b_nz.
    apply mult_lcancel with a; [>exact a_nz|].
    rewrite mult_lrinv by exact a_nz.
    apply mult_lcancel with b; [>exact b_nz|].
    rewrite mult_rinv by exact b_nz.
    rewrite mult_assoc, (mult_comm b).
    rewrite mult_rinv; [>reflexivity|].
    apply mult_nz; assumption.
Qed.

Theorem div_one : /1 = 1.
Proof.
    rewrite <- (mult_lid (/1)).
    classic_case (0 = 1) as [triv|ntriv].
    -   rewrite <- triv.
        apply mult_lanni.
    -   rewrite mult_rinv by exact ntriv.
        reflexivity.
Qed.

(* begin hide *)
End Field.

Section MultHomo.

Context {U V} `{Field U, Field V}.
(* end hide *)
Context (f : U → V) `{
    @Injective U V f,
    @HomomorphismPlus U V UP UP0 f,
    @HomomorphismZero U V UZ UZ0 f,
    @HomomorphismNeg U V UN UN0 f,
    @HomomorphismMult U V UM UM0 f,
    @HomomorphismOne U V UE UE0 f,
    @HomomorphismDiv U V UZ UD UD0 f
}.

Global Instance field_inj : Injective f.
Proof.
    apply (homo_zero_inj _).
    intros a eq.
    classic_contradiction a_nz.
    apply (lmult (f (/a))) in eq.
    rewrite mult_ranni in eq.
    rewrite <- homo_mult in eq.
    rewrite mult_linv in eq by exact a_nz.
    rewrite homo_one in eq.
    contradiction (not_trivial_one eq).
Qed.
Local Remove Hints field_inj : typeclass_instances.

Global Instance field_homo_div : HomomorphismDiv f.
Proof.
    split.
    intros a a_nz.
    pose proof (inj_zero _ a_nz) as fa_nz.
    apply (mult_lcancel (f a) fa_nz).
    rewrite <- homo_mult.
    do 2 rewrite mult_rinv by assumption.
    apply homo_one.
Qed.
Local Remove Hints field_homo_div : typeclass_instances.

(* begin hide *)
End MultHomo.
(* end hide *)
Tactic Notation "mult_cancel_left" constr(x) :=
    mult_bring_left x;
    apply lmult.
Tactic Notation "mult_cancel_left" constr(x) "in" ident(H) :=
    mult_bring_left x in H;
    apply mult_lcancel in H.
Tactic Notation "mult_cancel_right" constr(x) :=
    mult_bring_right x;
    apply rmult.
Tactic Notation "mult_cancel_right" constr(x) "in" ident(H) :=
    mult_bring_right x in H;
    apply mult_rcancel in H.
