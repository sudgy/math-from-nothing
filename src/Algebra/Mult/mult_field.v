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

(* begin hide *)
Arguments div : simpl never.

Section FieldImply1.

Context {U} `{
    z : Zero U,
    m : Mult U,
    o : One U,
    d : Div U,
    @MultComm U m,
    @MultLinv U z m o d
}.

Lemma mult_linv_rinv : ∀ a, 0 ≠ a → a / a = 1.
    intros a a_nz.
    rewrite mult_comm.
    apply mult_linv.
    exact a_nz.
Qed.
Global Instance mult_linv_rinv_class : MultRinv U := {
    mult_rinv := mult_linv_rinv
}.

End FieldImply1.

Section FieldImply2.

Context {U} `{
    z : Zero U,
    m : Mult U,
    o : One U,
    d : Div U,
    @MultComm U m,
    @MultAssoc U m,
    @MultLid U m o,
    @MultRid U m o,
    @MultLinv U z m o d,
    @MultRinv U z m o d
}.

Lemma mult_linv_lcancel : ∀ a b c, 0 ≠ c → c * a = c * b → a = b.
    intros a b c c_nz eq.
    apply lmult with (/c) in eq.
    do 2 rewrite mult_assoc in eq.
    rewrite mult_linv in eq; try exact c_nz.
    do 2 rewrite mult_lid in eq.
    exact eq.
Qed.
Global Instance mult_linv_lcancel_class : MultLcancel U := {
    mult_lcancel := mult_linv_lcancel
}.

Lemma mult_rinv_rcancel : ∀ a b c, 0 ≠ c → a * c = b * c → a = b.
    intros a b c c_nz eq.
    apply rmult with (/c) in eq.
    do 2 rewrite <- mult_assoc in eq.
    rewrite mult_rinv in eq; try exact c_nz.
    do 2 rewrite mult_rid in eq.
    exact eq.
Qed.
Global Instance mult_rinv_rcancel_class : MultRcancel U := {
    mult_rcancel := mult_rinv_rcancel
}.

End FieldImply2.

Section Field.

Context {U} `{
    p : Plus U,
    z : Zero U,
    n : Neg U,
    m : Mult U,
    o : One U,
    d : Div U,
    @PlusComm U p,
    @PlusAssoc U p,
    @PlusLid U p z,
    @PlusRid U p z,
    @PlusLinv U p z n,
    @PlusRinv U p z n,
    @MultComm U m,
    @MultAssoc U m,
    @Ldist U p m,
    @Rdist U p m,
    @MultLid U m o,
    @MultRid U m o,
    @MultLinv U z m o d,
    @MultRinv U z m o d,
    @NotTrivial U z o
}.
(* end hide *)
Theorem div_nz : ∀ a, 0 ≠ a → 0 ≠ /a.
    intros a a_nz eq.
    apply rmult with a in eq.
    rewrite mult_lanni in eq.
    rewrite mult_linv in eq by exact a_nz.
    exact (not_trivial eq).
Qed.

Theorem div_div : ∀ a, 0 ≠ a → /(/a) = a.
    intros a a_nz.
    apply mult_lcancel with (/a).
    1: apply div_nz; exact a_nz.
    rewrite mult_linv by exact a_nz.
    rewrite mult_rinv; try reflexivity.
    apply div_nz.
    exact a_nz.
Qed.

Theorem neg_div : ∀ a, 0 ≠ a → /(-a) = -/a.
    intros a a_nz.
    pose proof (neg_nz _ a_nz) as na_nz.
    apply mult_rcancel with (-a); try exact na_nz.
    rewrite mult_linv by exact na_nz.
    rewrite mult_lneg, mult_rneg, neg_neg.
    rewrite mult_linv by exact a_nz.
    reflexivity.
Qed.

Theorem div_mult : ∀ a b, 0 ≠ a → 0 ≠ b → /(a * b) = /a * /b.
    intros a b a_nz b_nz.
    apply mult_lcancel with a; try exact a_nz.
    rewrite mult_assoc.
    rewrite mult_rinv by exact a_nz.
    rewrite mult_lid.
    apply mult_lcancel with b; try exact b_nz.
    rewrite mult_rinv by exact b_nz.
    rewrite mult_assoc, (mult_comm b).
    rewrite mult_rinv; try reflexivity.
    intro contr.
    apply rmult with (/b) in contr.
    rewrite mult_lanni in contr.
    rewrite <- mult_assoc in contr.
    rewrite mult_rinv in contr by exact b_nz.
    rewrite mult_rid in contr.
    contradiction.
Qed.

Theorem mult_0 : ∀ {a b}, 0 = a * b → {0 = a} + {0 = b}.
    intros a b eq.
    classic_case (0 = a) as [a_z|a_nz].
    -   left; exact a_z.
    -   right.
        apply lmult with (/a) in eq.
        rewrite mult_ranni, mult_assoc in eq.
        rewrite mult_linv, mult_lid in eq by exact a_nz.
        exact eq.
Qed.

Theorem mult_rrinv : ∀ a b, 0 ≠ b → a * b / b = a.
    intros a b b_nz.
    rewrite <- mult_assoc.
    rewrite mult_rinv by exact b_nz.
    apply mult_rid.
Qed.
Theorem mult_rlinv : ∀ a b, 0 ≠ b → a / b * b = a.
    intros a b b_nz.
    rewrite <- mult_assoc.
    rewrite mult_linv by exact b_nz.
    apply mult_rid.
Qed.
Theorem mult_lrinv : ∀ a b, 0 ≠ b → b * (/b * a) = a.
    intros a b b_nz.
    rewrite mult_assoc.
    rewrite mult_rinv by exact b_nz.
    apply mult_lid.
Qed.
Theorem mult_llinv : ∀ a b, 0 ≠ b → /b * (b * a) = a.
    intros a b b_nz.
    rewrite mult_assoc.
    rewrite mult_linv by exact b_nz.
    apply mult_lid.
Qed.

Theorem mult_llmove : ∀ a b c, 0 ≠ a → a * b = c ↔ b = /a * c.
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
    intros a b a_nz.
    rewrite mult_rlmove by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem mult_1_ab_db_a : ∀ a b, 0 ≠ b → 1 = a * b ↔ /b = a.
    intros a b b_nz.
    rewrite mult_rrmove by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem mult_1_ab_a_db : ∀ a b, 0 ≠ b → 1 = a * b ↔ a = /b.
    intros a b b_nz.
    rewrite mult_rrmove by exact b_nz.
    rewrite mult_lid.
    split; intro eq; symmetry; exact eq.
Qed.
Theorem mult_1_ab_b_da : ∀ a b, 0 ≠ a → 1 = a * b ↔ b = /a.
    intros a b a_nz.
    rewrite mult_rlmove by exact a_nz.
    rewrite mult_rid.
    split; intro eq; symmetry; exact eq.
Qed.

Theorem mult_1_a_ab_b : ∀ a b, 0 ≠ b → 1 = a ↔ a * b = b.
    intros a b b_nz.
    rewrite mult_lrmove by exact b_nz.
    rewrite mult_rinv by exact b_nz.
    split; intro eq; symmetry; exact eq.
Qed.
Theorem mult_1_a_ba_b : ∀ a b, 0 ≠ b → 1 = a ↔ b * a = b.
    intros a b b_nz.
    rewrite mult_llmove by exact b_nz.
    rewrite mult_linv by exact b_nz.
    split; intro eq; symmetry; exact eq.
Qed.
Theorem mult_1_a_b_ab : ∀ a b, 0 ≠ b → 1 = a ↔ b = a * b.
    intros a b b_nz.
    rewrite mult_rrmove by exact b_nz.
    rewrite mult_rinv by exact b_nz.
    reflexivity.
Qed.
Theorem mult_1_a_b_ba : ∀ a b, 0 ≠ b → 1 = a ↔ b = b * a.
    intros a b b_nz.
    rewrite mult_rlmove by exact b_nz.
    rewrite mult_linv by exact b_nz.
    reflexivity.
Qed.

Theorem mult_1_dab_a_b : ∀ a b, 0 ≠ a → 1 = /a * b ↔ a = b.
    intros a b a_nz.
    rewrite mult_1_ab_da_b by (apply div_nz; exact a_nz).
    rewrite div_div by exact a_nz.
    reflexivity.
Qed.
Theorem mult_1_adb_a_b : ∀ a b, 0 ≠ b → 1 = a / b ↔ a = b.
    intros a b b_nz.
    rewrite mult_1_ab_a_db by (apply div_nz; exact b_nz).
    rewrite div_div by exact b_nz.
    reflexivity.
Qed.
Theorem mult_1_dab_b_a : ∀ a b, 0 ≠ a → 1 = /a * b ↔ b = a.
    intros a b a_nz.
    rewrite mult_1_ab_b_da by (apply div_nz; exact a_nz).
    rewrite div_div by exact a_nz.
    reflexivity.
Qed.
Theorem mult_1_adb_b_a : ∀ a b, 0 ≠ b → 1 = a / b ↔ b = a.
    intros a b b_nz.
    rewrite mult_1_ab_db_a by (apply div_nz; exact b_nz).
    rewrite div_div by exact b_nz.
    reflexivity.
Qed.

(* begin hide *)
End Field.
(* end hide *)
