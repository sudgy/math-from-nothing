Require Import init.

Require Export relation.
Require Export plus_group.
Require Export mult.
Require Export order_plus.

Class OrderMult U `{Zero U, Mult U, Order U} := {
    le_mult : ∀ a b, zero <= a → zero <= b → zero <= a * b
}.
Class OrderLmult U `{Zero U, Mult U, Order U} := {
    le_lmult_pos : ∀ {a b} c, zero <= c → a <= b → c * a <= c * b
}.
Class OrderRmult U `{Zero U, Mult U, Order U} := {
    le_rmult_pos : ∀ {a b} c, zero <= c → a <= b → a * c <= b * c
}.
Class OrderMultLcancel U `{Zero U, Mult U, Order U} := {
    le_mult_lcancel_pos : ∀ {a b} c, zero < c → c * a <= c * b → a <= b
}.
Class OrderMultRcancel U `{Zero U, Mult U, Order U} := {
    le_mult_rcancel_pos : ∀ {a b} c, zero < c → a * c <= b * c → a <= b
}.

Class OrderedField U `{
    OFF : Field U,
    OFO : TotalOrder U,
    UOP : @OrderLplus U UP UO,
    UOPR : @OrderRplus U UP UO,
    UOPC : @OrderPlusLcancel U UP UO,
    UOPCR : @OrderPlusRcancel U UP UO,
    UOM : @OrderMult U UZ UM UO,
    UOML : @OrderLmult U UZ UM UO,
    UOMR : @OrderRmult U UZ UM UO,
    UOMLC : @OrderMultLcancel U UZ UM UO,
    UOMRC : @OrderMultRcancel U UZ UM UO
}.

(* begin hide *)
Section OrderMultImply.

Context {U} `{OrderedField U}.

Lemma le_lmult_rmult_ : ∀ a b c, zero <= c → a <= b → a * c <= b * c.
    intros a b c c_pos eq.
    do 2 rewrite (mult_comm _ c).
    apply le_lmult_pos; assumption.
Qed.

Lemma le_mult_lcancel_rcancel_ : ∀ a b c, zero < c → a * c <= b * c → a <= b.
    intros a b c c_pos eq.
    do 2 rewrite (mult_comm _ c) in eq.
    apply le_mult_lcancel_pos in eq; assumption.
Qed.

Lemma le_mult_lmult : ∀ a b c, 0 <= c → a <= b → c * a <= c * b.
    intros a b c c_pos leq.
    apply le_lplus with (-a) in leq.
    rewrite plus_linv in leq.
    pose proof (le_mult _ _ c_pos leq) as eq.
    rewrite ldist in eq.
    rewrite mult_rneg in eq.
    apply le_lplus with (c * a) in eq.
    rewrite plus_assoc in eq.
    rewrite plus_rinv in eq.
    rewrite plus_lid, plus_rid in eq.
    exact eq.
Qed.
(* end hide *)
Theorem div_pos : ∀ a, 0 < a → 0 < div a.
    intros a a_pos.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    apply le_lmult_pos with a in contr.
    2: apply a_pos.
    apply le_lmult_pos with a in contr.
    2: apply a_pos.
    rewrite mult_rinv in contr by apply a_pos.
    rewrite mult_rid in contr.
    do 2 rewrite mult_ranni in contr.
    pose proof (lt_le_trans a_pos contr) as contr2.
    destruct contr2; contradiction.
Qed.

(* begin hide *)
Lemma le_lmult_lcancel : ∀ a b c, zero < c → c * a <= c * b → a <= b.
    intros a b c c_pos eq.
    apply le_lmult_pos with (div c) in eq.
    2: apply div_pos; apply c_pos.
    do 2 rewrite mult_assoc in eq.
    rewrite mult_linv in eq by apply c_pos.
    do 2 rewrite mult_lid in eq.
    exact eq.
Qed.

Global Instance le_lmult_rmult : OrderRmult U := {
    le_rmult_pos := le_lmult_rmult_
}.

Global Instance le_mult_lcancel_rcancel : OrderMultRcancel U := {
    le_mult_rcancel_pos := le_mult_lcancel_rcancel_
}.

Global Instance le_mult_lmult_class : OrderLmult U := {
    le_lmult_pos := le_mult_lmult
}.

Global Instance le_lmult_lcancel_class : OrderMultLcancel U := {
    le_mult_lcancel_pos := le_lmult_lcancel
}.

End OrderMultImply.

Section OrderMult.

Context {U} `{OrderedField U}.

(* end hide *)
Theorem lt_lmult_pos : ∀ {a b} c, zero < c → a < b → c * a < c * b.
    intros a b c c_gt ab.
    split.
    -   apply le_lmult_pos.
        +   apply c_gt.
        +   apply ab.
    -   intro contr.
        apply mult_lcancel in contr.
        +   destruct ab; contradiction.
        +   apply c_gt.
Qed.

Theorem lt_rmult_pos : ∀ {a b} c, zero < c → a < b → a * c < b * c.
    intros a b c c_gt ab.
    split.
    -   apply le_rmult_pos.
        +   apply c_gt.
        +   apply ab.
    -   intro contr.
        apply mult_rcancel in contr.
        +   destruct ab; contradiction.
        +   apply c_gt.
Qed.

Theorem lt_mult_lcancel_pos : ∀ {a b} c, zero < c → c * a < c * b → a < b.
    intros a b c c_nz eq.
    split.
    -   apply le_mult_lcancel_pos with c.
        +   exact c_nz.
        +   apply eq.
    -   intro contr.
        rewrite contr in eq.
        destruct eq; contradiction.
Qed.

Theorem lt_mult_rcancel_pos : ∀ {a b} c, zero < c → a * c < b * c → a < b.
    intros a b c c_nz eq.
    split.
    -   apply le_mult_rcancel_pos with c.
        +   exact c_nz.
        +   apply eq.
    -   intro contr.
        rewrite contr in eq.
        destruct eq; contradiction.
Qed.

Theorem le_lmult_neg : ∀ {a b} c, c <= zero → a <= b → c * b <= c * a.
    intros a b c c_neg eq.
    apply le_neg in c_neg.
    rewrite neg_zero in c_neg.
    apply (le_lmult_pos _ c_neg) in eq.
    apply le_neg in eq.
    do 2 rewrite mult_lneg in eq.
    do 2 rewrite neg_neg in eq.
    exact eq.
Qed.

Theorem le_rmult_neg : ∀ {a b} c, c <= zero → a <= b → b * c <= a * c.
    intros a b c c_neg eq.
    apply le_neg in c_neg.
    rewrite neg_zero in c_neg.
    apply (le_rmult_pos _ c_neg) in eq.
    apply le_neg in eq.
    do 2 rewrite mult_rneg in eq.
    do 2 rewrite neg_neg in eq.
    exact eq.
Qed.

Theorem lt_mult : ∀ a b, zero < a → zero < b → zero < a * b.
    intros a b a_pos b_pos.
    apply lt_rmult_pos with b in a_pos; try exact b_pos.
    rewrite mult_lanni in a_pos.
    exact a_pos.
Qed.

Theorem lt_lmult_neg : ∀ {a b} c, c < zero → a < b → c * b < c * a.
    intros a b c c_neg eq.
    apply lt_neg in c_neg.
    rewrite neg_zero in c_neg.
    apply (lt_lmult_pos _ c_neg) in eq.
    apply lt_neg in eq.
    do 2 rewrite mult_lneg in eq.
    do 2 rewrite neg_neg in eq.
    exact eq.
Qed.

Theorem lt_rmult_neg : ∀ {a b} c, c < zero → a < b → b * c < a * c.
    intros a b c c_neg eq.
    apply lt_neg in c_neg.
    rewrite neg_zero in c_neg.
    apply (lt_rmult_pos _ c_neg) in eq.
    apply lt_neg in eq.
    do 2 rewrite mult_rneg in eq.
    do 2 rewrite neg_neg in eq.
    exact eq.
Qed.

Theorem div_neg : ∀ a, a < 0 → /a < 0.
    intros a a_neg.
    pose proof (neg_pos2 _ a_neg) as a_pos.
    apply div_pos in a_pos.
    rewrite neg_div in a_pos by (rewrite neq_sym; apply a_neg).
    apply pos_neg2 in a_pos.
    rewrite neg_neg in a_pos.
    exact a_pos.
Qed.

Theorem le_mult_lcancel_neg : ∀ {a b} c, c < 0 → c * a <= c * b → b <= a.
    intros a b c c_neg eq.
    apply le_lmult_neg with (/c) in eq.
    2: apply div_neg; exact c_neg.
    do 2 rewrite mult_llinv in eq by (rewrite neq_sym; apply c_neg).
    exact eq.
Qed.
Theorem le_mult_rcancel_neg : ∀ {a b} c, c < 0 → a * c <= b * c → b <= a.
    intros a b c c_neg eq.
    apply le_rmult_neg with (/c) in eq.
    2: apply div_neg; exact c_neg.
    do 2 rewrite mult_rrinv in eq by (rewrite neq_sym; apply c_neg).
    exact eq.
Qed.
Theorem lt_mult_lcancel_neg : ∀ {a b} c, c < 0 → c * a < c * b → b < a.
    intros a b c c_neg eq.
    apply lt_lmult_neg with (/c) in eq.
    2: apply div_neg; exact c_neg.
    do 2 rewrite mult_llinv in eq by (rewrite neq_sym; apply c_neg).
    exact eq.
Qed.
Theorem lt_mult_rcancel_neg : ∀ {a b} c, c < 0 → a * c < b * c → b < a.
    intros a b c c_neg eq.
    apply lt_rmult_neg with (/c) in eq.
    2: apply div_neg; exact c_neg.
    do 2 rewrite mult_rrinv in eq by (rewrite neq_sym; apply c_neg).
    exact eq.
Qed.

Theorem one_pos : 0 < 1.
    split; [>|exact not_trivial_one].
    classic_contradiction contr.
    rewrite nle_lt in contr.
    pose proof (land (lt_neg _ _) contr) as eq.
    rewrite neg_zero in eq.
    pose proof (lt_mult _ _ eq eq) as eq2.
    rewrite mult_rneg, mult_lneg in eq2.
    rewrite neg_neg in eq2.
    rewrite mult_lid in eq2.
    pose proof (trans contr eq2) as [C0 C1]; contradiction.
Qed.

Theorem plus_one_pos : ∀ x, x < x + 1.
    intros x.
    rewrite <- (plus_rid x) at 1.
    apply lt_lplus.
    exact one_pos.
Qed.

Theorem two_pos : 0 < 2.
    pose proof (lt_lrplus one_pos one_pos) as eq.
    rewrite plus_lid in eq.
    exact eq.
Qed.

Theorem three_pos : 0 < 3.
    pose proof (lt_lrplus one_pos two_pos) as eq.
    rewrite plus_lid in eq.
    exact eq.
Qed.

Theorem four_pos : 0 < 4.
    pose proof (lt_lrplus two_pos two_pos) as eq.
    rewrite plus_lid, two_plus_two in eq.
    exact eq.
Qed.

Theorem inv_ge_one : ∀ a, 1 <= a → div a <= 1.
    intros a a_ge.
    pose proof (lt_le_trans one_pos a_ge) as a_pos.
    apply le_mult_rcancel_pos with a; try exact a_pos.
    rewrite mult_linv by apply a_pos.
    rewrite mult_lid.
    exact a_ge.
Qed.

Theorem inv_le_one : ∀ a, 0 < a → a <= 1 → 1 <= div a.
    intros a a_pos a_leq.
    apply le_mult_rcancel_pos with a; try exact a_pos.
    rewrite mult_linv by apply a_pos.
    rewrite mult_lid.
    exact a_leq.
Qed.

Theorem inv_gt_one : ∀ a, 1 < a → div a < 1.
    intros a a_gt.
    pose proof (trans one_pos a_gt) as a_pos.
    apply lt_mult_rcancel_pos with a; try exact a_pos.
    rewrite mult_linv by apply a_pos.
    rewrite mult_lid.
    exact a_gt.
Qed.

Theorem inv_lt_one : ∀ a, 0 < a → a < 1 → 1 < div a.
    intros a a_pos a_ltq.
    apply lt_mult_rcancel_pos with a; try exact a_pos.
    rewrite mult_linv by apply a_pos.
    rewrite mult_lid.
    exact a_ltq.
Qed.

Theorem square_one_one_pos : ∀ a, 0 < a → a * a = 1 → a = 1.
    intros a a_pos eq.
    apply rmult with (div a) in eq.
    rewrite <- mult_assoc in eq.
    rewrite mult_rinv in eq by apply a_pos.
    rewrite mult_rid, mult_lid in eq.
    destruct (connex 1 a) as [leq|leq].
    +   pose proof (inv_ge_one _ leq) as leq2.
        rewrite <- eq in leq2.
        exact (antisym leq2 leq).
    +   pose proof (inv_le_one _ a_pos leq) as leq2.
        rewrite <- eq in leq2.
        exact (antisym leq leq2).
Qed.
Theorem square_one_one : ∀ a, a * a = 1 → a = 1 ∨ a = -(1).
    intros a eq.
    classic_case (0 = a) as [a_z|a_nz].
    {
        subst.
        rewrite mult_ranni in eq.
        contradiction (not_trivial_one eq).
    }
    destruct (trichotomy 0 a) as [[a_pos|a_z]|a_neg]; try contradiction.
    -   left.
        apply square_one_one_pos; assumption.
    -   right.
        rewrite <- (neg_neg a).
        rewrite <- neg_eq.
        apply square_one_one_pos.
        +   apply lt_neg in a_neg.
            rewrite neg_zero in a_neg.
            exact a_neg.
        +   rewrite mult_lneg, mult_rneg, neg_neg.
            exact eq.
Qed.

Theorem plus_half : ∀ a, a * div 2 + a * div 2 = a.
    intros a.
    rewrite <- ldist.
    rewrite <- (mult_lid (div 2)).
    rewrite <- rdist.
    rewrite mult_rinv by apply two_pos.
    apply mult_rid.
Qed.

Theorem le_div_pos : ∀ a b, 0 < a → a <= b → div b <= div a.
    intros a b a_pos ab.
    pose proof (lt_le_trans a_pos ab) as b_pos.
    apply le_rmult_pos with (div a) in ab.
    2: apply div_pos; exact a_pos.
    rewrite mult_rinv in ab by apply a_pos.
    apply le_lmult_pos with (div b) in ab.
    2: apply div_pos; exact b_pos.
    rewrite mult_assoc in ab.
    rewrite mult_linv in ab by apply b_pos.
    rewrite mult_lid, mult_rid in ab.
    exact ab.
Qed.

Theorem le_div_neg : ∀ a b, b < 0 → a <= b → div b <= div a.
    intros a b b_neg ab.
    pose proof (le_lt_trans ab b_neg) as a_neg.
    assert (0 ≠ a) as a_nz by (intro contr;subst;destruct a_neg; contradiction).
    assert (0 ≠ b) as b_nz by (intro contr;subst;destruct b_neg; contradiction).
    apply le_neg in ab.
    apply lt_neg in a_neg, b_neg.
    rewrite neg_zero in a_neg, b_neg.
    apply le_div_pos in ab; try assumption.
    rewrite neg_div in ab by exact a_nz.
    rewrite neg_div in ab by exact b_nz.
    apply le_neg in ab.
    exact ab.
Qed.

Theorem lt_div_pos : ∀ a b, 0 < a → a < b → div b < div a.
    intros a b a_pos [ab neq].
    pose proof (lt_le_trans a_pos ab) as b_pos.
    split.
    -   apply le_div_pos; assumption.
    -   intros contr.
        apply (f_equal div) in contr.
        rewrite div_div in contr by apply b_pos.
        rewrite div_div in contr by apply a_pos.
        symmetry in contr; contradiction.
Qed.

Theorem lt_div_neg : ∀ a b, b < 0 → a < b → div b < div a.
    intros a b b_neg [ab neq].
    pose proof (le_lt_trans ab b_neg) as a_neg.
    assert (0 ≠ a) as a_nz by (intro contr;subst;destruct a_neg; contradiction).
    assert (0 ≠ b) as b_nz by (intro contr;subst;destruct b_neg; contradiction).
    split.
    -   apply le_div_neg; assumption.
    -   intros contr.
        apply (f_equal div) in contr.
        rewrite div_div in contr by exact b_nz.
        rewrite div_div in contr by exact a_nz.
        symmetry in contr; contradiction.
Qed.

Theorem half_pos : ∀ a, 0 < a → 0 < a * div 2.
    intros a a_pos.
    apply lt_mult_rcancel_pos with 2.
    1: exact two_pos.
    rewrite mult_lanni.
    rewrite <- mult_assoc, mult_linv, mult_rid by apply two_pos.
    exact a_pos.
Qed.
Theorem half_neg : ∀ a, a < 0 → a * div 2 < 0.
    intros a a_neg.
    apply lt_mult_rcancel_pos with 2.
    1: exact two_pos.
    rewrite mult_lanni.
    rewrite <- mult_assoc, mult_linv, mult_rid by apply two_pos.
    exact a_neg.
Qed.

Theorem double_pos : ∀ a, 0 < a → 0 < 2 * a.
    intros a a_pos.
    rewrite rdist, mult_lid.
    rewrite <- (plus_rid 0).
    apply lt_lrplus; exact a_pos.
Qed.
Theorem double_neg : ∀ a, a < 0 → 2 * a < 0.
    intros a a_neg.
    rewrite rdist, mult_lid.
    rewrite <- (plus_rid 0).
    apply lt_lrplus; exact a_neg.
Qed.

(* begin hide *)
Lemma ordered_field_dense : ∀ a b, a < b → ∃ c, a < c ∧ c < b.
    intros a b ab.
    exists ((a + b) * div 2).
    split.
    -   apply lt_mult_rcancel_pos with 2.
        1: exact two_pos.
        rewrite <- mult_assoc, mult_linv, mult_rid by apply two_pos.
        rewrite ldist.
        rewrite mult_rid.
        apply lt_lplus.
        exact ab.
    -   apply lt_mult_rcancel_pos with 2.
        1: exact two_pos.
        rewrite <- mult_assoc, mult_linv, mult_rid by apply two_pos.
        rewrite ldist.
        rewrite mult_rid.
        apply lt_rplus.
        exact ab.
Qed.
Global Instance ordered_field_dense_class : Dense lt := {
    dense := ordered_field_dense
}.
(* end hide *)
Theorem le_mult_llmove_pos : ∀ a b c, 0 < a → a * b <= c ↔ b <= /a * c.
    intros a b c a_pos.
    split; intros eq.
    -   apply le_lmult_pos with (/a) in eq.
        2: apply div_pos; apply a_pos.
        rewrite mult_llinv in eq by apply a_pos.
        exact eq.
    -   apply le_lmult_pos with a in eq.
        2: apply a_pos.
        rewrite mult_lrinv in eq by apply a_pos.
        exact eq.
Qed.
Theorem le_mult_lrmove_pos : ∀ a b c, 0 < b → a * b <= c ↔ a <= c / b.
    intros a b c b_pos.
    split; intros eq.
    -   apply le_rmult_pos with (/b) in eq.
        2: apply div_pos; apply b_pos.
        rewrite mult_rrinv in eq by apply b_pos.
        exact eq.
    -   apply le_rmult_pos with b in eq.
        2: apply b_pos.
        rewrite mult_rlinv in eq by apply b_pos.
        exact eq.
Qed.
Theorem le_mult_rlmove_pos : ∀ a b c, 0 < b → a <= b * c ↔ /b * a <= c.
    intros a b c b_pos.
    split; intros eq.
    -   apply le_lmult_pos with (/b) in eq.
        2: apply div_pos; apply b_pos.
        rewrite mult_llinv in eq by apply b_pos.
        exact eq.
    -   apply le_lmult_pos with b in eq.
        2: apply b_pos.
        rewrite mult_lrinv in eq by apply b_pos.
        exact eq.
Qed.
Theorem le_mult_rrmove_pos : ∀ a b c, 0 < c → a <= b * c ↔ a / c <= b.
    intros a b c c_pos.
    split; intros eq.
    -   apply le_rmult_pos with (/c) in eq.
        2: apply div_pos; apply c_pos.
        rewrite mult_rrinv in eq by apply c_pos.
        exact eq.
    -   apply le_rmult_pos with c in eq.
        2: apply c_pos.
        rewrite mult_rlinv in eq by apply c_pos.
        exact eq.
Qed.

Theorem le_mult_1_ab_da_b_pos : ∀ a b, 0 < a → 1 <= a * b ↔ /a <= b.
    intros a b a_nz.
    rewrite le_mult_rlmove_pos by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem le_mult_1_ab_db_a_pos : ∀ a b, 0 < b → 1 <= a * b ↔ /b <= a.
    intros a b b_nz.
    rewrite le_mult_rrmove_pos by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem le_mult_ab_1_a_db_pos : ∀ a b, 0 < b → a * b <= 1 ↔ a <= /b.
    intros a b b_nz.
    rewrite le_mult_lrmove_pos by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem le_mult_ab_1_b_da_pos : ∀ a b, 0 < a → a * b <= 1 ↔ b <= /a.
    intros a b a_nz.
    rewrite le_mult_llmove_pos by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem le_mult_a_1_ab_b_pos : ∀ a b, 0 < b → a <= 1 ↔ a * b <= b.
    intros a b b_nz.
    rewrite le_mult_lrmove_pos by exact b_nz.
    rewrite mult_rinv by apply b_nz.
    reflexivity.
Qed.
Theorem le_mult_a_1_ba_b_pos : ∀ a b, 0 < b → a <= 1 ↔ b * a <= b.
    intros a b b_nz.
    rewrite le_mult_llmove_pos by exact b_nz.
    rewrite mult_linv by apply b_nz.
    reflexivity.
Qed.
Theorem le_mult_1_a_b_ab_pos : ∀ a b, 0 < b → 1 <= a ↔ b <= a * b.
    intros a b b_nz.
    rewrite le_mult_rrmove_pos by exact b_nz.
    rewrite mult_rinv by apply b_nz.
    reflexivity.
Qed.
Theorem le_mult_1_a_b_ba_pos : ∀ a b, 0 < b → 1 <= a ↔ b <= b * a.
    intros a b b_nz.
    rewrite le_mult_rlmove_pos by exact b_nz.
    rewrite mult_linv by apply b_nz.
    reflexivity.
Qed.

Theorem le_mult_1_dab_a_b_pos : ∀ a b, 0 < a → 1 <= /a * b ↔ a <= b.
    intros a b a_nz.
    rewrite le_mult_1_ab_da_b_pos by (apply div_pos; exact a_nz).
    rewrite div_div by apply a_nz.
    reflexivity.
Qed.
Theorem le_mult_adb_1_a_b_pos : ∀ a b, 0 < b → a / b <= 1 ↔ a <= b.
    intros a b b_nz.
    rewrite le_mult_ab_1_a_db_pos by (apply div_pos; exact b_nz).
    rewrite div_div by apply b_nz.
    reflexivity.
Qed.
Theorem le_mult_1_dab_b_a_pos : ∀ a b, 0 < a → /a * b <= 1 ↔ b <= a.
    intros a b a_nz.
    rewrite le_mult_ab_1_b_da_pos by (apply div_pos; exact a_nz).
    rewrite div_div by apply a_nz.
    reflexivity.
Qed.
Theorem le_mult_1_adb_b_a_pos : ∀ a b, 0 < b → 1 <= a / b ↔ b <= a.
    intros a b b_nz.
    rewrite le_mult_1_ab_db_a_pos by (apply div_pos; exact b_nz).
    rewrite div_div by apply b_nz.
    reflexivity.
Qed.

Theorem le_mult_llmove_neg : ∀ a b c, a < 0 → a * b <= c ↔ /a * c <= b.
    intros a b c a_neg.
    split; intros eq.
    -   apply le_lmult_neg with (/a) in eq.
        2: apply div_neg; apply a_neg.
        rewrite mult_llinv in eq by (rewrite neq_sym; apply a_neg).
        exact eq.
    -   apply le_lmult_neg with a in eq.
        2: apply a_neg.
        rewrite mult_lrinv in eq by (rewrite neq_sym; apply a_neg).
        exact eq.
Qed.
Theorem le_mult_lrmove_neg : ∀ a b c, b < 0 → a * b <= c ↔ c / b <= a.
    intros a b c b_neg.
    split; intros eq.
    -   apply le_rmult_neg with (/b) in eq.
        2: apply div_neg; apply b_neg.
        rewrite mult_rrinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
    -   apply le_rmult_neg with b in eq.
        2: apply b_neg.
        rewrite mult_rlinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
Qed.
Theorem le_mult_rlmove_neg : ∀ a b c, b < 0 → a <= b * c ↔ c <= /b * a.
    intros a b c b_neg.
    split; intros eq.
    -   apply le_lmult_neg with (/b) in eq.
        2: apply div_neg; apply b_neg.
        rewrite mult_llinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
    -   apply le_lmult_neg with b in eq.
        2: apply b_neg.
        rewrite mult_lrinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
Qed.
Theorem le_mult_rrmove_neg : ∀ a b c, c < 0 → a <= b * c ↔ b <= a / c.
    intros a b c c_neg.
    split; intros eq.
    -   apply le_rmult_neg with (/c) in eq.
        2: apply div_neg; apply c_neg.
        rewrite mult_rrinv in eq by (rewrite neq_sym; apply c_neg).
        exact eq.
    -   apply le_rmult_neg with c in eq.
        2: apply c_neg.
        rewrite mult_rlinv in eq by (rewrite neq_sym; apply c_neg).
        exact eq.
Qed.

Theorem le_mult_1_ab_b_da_neg : ∀ a b, a < 0 → 1 <= a * b ↔ b <= /a.
    intros a b a_nz.
    rewrite le_mult_rlmove_neg by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem le_mult_1_ab_a_db_neg : ∀ a b, b < 0 → 1 <= a * b ↔ a <= /b.
    intros a b b_nz.
    rewrite le_mult_rrmove_neg by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem le_mult_ab_1_db_a_neg : ∀ a b, b < 0 → a * b <= 1 ↔ /b <= a.
    intros a b b_nz.
    rewrite le_mult_lrmove_neg by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem le_mult_ab_1_da_b_neg : ∀ a b, a < 0 → a * b <= 1 ↔ /a <= b.
    intros a b a_nz.
    rewrite le_mult_llmove_neg by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem le_mult_a_1_b_ab_neg : ∀ a b, b < 0 → a <= 1 ↔ b <= a * b.
    intros a b b_nz.
    rewrite le_mult_rrmove_neg by exact b_nz.
    rewrite mult_rinv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem le_mult_a_1_b_ba_neg : ∀ a b, b < 0 → a <= 1 ↔ b <= b * a.
    intros a b b_nz.
    rewrite le_mult_rlmove_neg by exact b_nz.
    rewrite mult_linv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem le_mult_1_a_ab_b_neg : ∀ a b, b < 0 → 1 <= a ↔ a * b <= b.
    intros a b b_nz.
    rewrite le_mult_lrmove_neg by exact b_nz.
    rewrite mult_rinv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem le_mult_1_a_ba_b_neg : ∀ a b, b < 0 → 1 <= a ↔ b * a <= b.
    intros a b b_nz.
    rewrite le_mult_llmove_neg by exact b_nz.
    rewrite mult_linv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.

Theorem le_mult_1_dab_b_a_neg : ∀ a b, a < 0 → 1 <= /a * b ↔ b <= a.
    intros a b a_nz.
    rewrite le_mult_1_ab_b_da_neg by (apply div_neg; exact a_nz).
    rewrite div_div by (rewrite neq_sym; apply a_nz).
    reflexivity.
Qed.
Theorem le_mult_adb_1_b_a_neg : ∀ a b, b < 0 → a / b <= 1 ↔ b <= a.
    intros a b b_nz.
    rewrite le_mult_ab_1_db_a_neg by (apply div_neg; exact b_nz).
    rewrite div_div by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem le_mult_1_dab_a_b_neg : ∀ a b, a < 0 → /a * b <= 1 ↔ a <= b.
    intros a b a_nz.
    rewrite le_mult_ab_1_da_b_neg by (apply div_neg; exact a_nz).
    rewrite div_div by (rewrite neq_sym; apply a_nz).
    reflexivity.
Qed.
Theorem le_mult_1_adb_a_b_neg : ∀ a b, b < 0 → 1 <= a / b ↔ a <= b.
    intros a b b_nz.
    rewrite le_mult_1_ab_a_db_neg by (apply div_neg; exact b_nz).
    rewrite div_div by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.

Theorem lt_mult_llmove_pos : ∀ a b c, 0 < a → a * b < c ↔ b < /a * c.
    intros a b c a_pos.
    split; intros eq.
    -   apply lt_lmult_pos with (/a) in eq.
        2: apply div_pos; apply a_pos.
        rewrite mult_llinv in eq by apply a_pos.
        exact eq.
    -   apply lt_lmult_pos with a in eq.
        2: apply a_pos.
        rewrite mult_lrinv in eq by apply a_pos.
        exact eq.
Qed.
Theorem lt_mult_lrmove_pos : ∀ a b c, 0 < b → a * b < c ↔ a < c / b.
    intros a b c b_pos.
    split; intros eq.
    -   apply lt_rmult_pos with (/b) in eq.
        2: apply div_pos; apply b_pos.
        rewrite mult_rrinv in eq by apply b_pos.
        exact eq.
    -   apply lt_rmult_pos with b in eq.
        2: apply b_pos.
        rewrite mult_rlinv in eq by apply b_pos.
        exact eq.
Qed.
Theorem lt_mult_rlmove_pos : ∀ a b c, 0 < b → a < b * c ↔ /b * a < c.
    intros a b c b_pos.
    split; intros eq.
    -   apply lt_lmult_pos with (/b) in eq.
        2: apply div_pos; apply b_pos.
        rewrite mult_llinv in eq by apply b_pos.
        exact eq.
    -   apply lt_lmult_pos with b in eq.
        2: apply b_pos.
        rewrite mult_lrinv in eq by apply b_pos.
        exact eq.
Qed.
Theorem lt_mult_rrmove_pos : ∀ a b c, 0 < c → a < b * c ↔ a / c < b.
    intros a b c c_pos.
    split; intros eq.
    -   apply lt_rmult_pos with (/c) in eq.
        2: apply div_pos; apply c_pos.
        rewrite mult_rrinv in eq by apply c_pos.
        exact eq.
    -   apply lt_rmult_pos with c in eq.
        2: apply c_pos.
        rewrite mult_rlinv in eq by apply c_pos.
        exact eq.
Qed.

Theorem lt_mult_1_ab_da_b_pos : ∀ a b, 0 < a → 1 < a * b ↔ /a < b.
    intros a b a_nz.
    rewrite lt_mult_rlmove_pos by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem lt_mult_1_ab_db_a_pos : ∀ a b, 0 < b → 1 < a * b ↔ /b < a.
    intros a b b_nz.
    rewrite lt_mult_rrmove_pos by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem lt_mult_ab_1_a_db_pos : ∀ a b, 0 < b → a * b < 1 ↔ a < /b.
    intros a b b_nz.
    rewrite lt_mult_lrmove_pos by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem lt_mult_ab_1_b_da_pos : ∀ a b, 0 < a → a * b < 1 ↔ b < /a.
    intros a b a_nz.
    rewrite lt_mult_llmove_pos by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem lt_mult_a_1_ab_b_pos : ∀ a b, 0 < b → a < 1 ↔ a * b < b.
    intros a b b_nz.
    rewrite lt_mult_lrmove_pos by exact b_nz.
    rewrite mult_rinv by apply b_nz.
    reflexivity.
Qed.
Theorem lt_mult_a_1_ba_b_pos : ∀ a b, 0 < b → a < 1 ↔ b * a < b.
    intros a b b_nz.
    rewrite lt_mult_llmove_pos by exact b_nz.
    rewrite mult_linv by apply b_nz.
    reflexivity.
Qed.
Theorem lt_mult_1_a_b_ab_pos : ∀ a b, 0 < b → 1 < a ↔ b < a * b.
    intros a b b_nz.
    rewrite lt_mult_rrmove_pos by exact b_nz.
    rewrite mult_rinv by apply b_nz.
    reflexivity.
Qed.
Theorem lt_mult_1_a_b_ba_pos : ∀ a b, 0 < b → 1 < a ↔ b < b * a.
    intros a b b_nz.
    rewrite lt_mult_rlmove_pos by exact b_nz.
    rewrite mult_linv by apply b_nz.
    reflexivity.
Qed.

Theorem lt_mult_1_dab_a_b_pos : ∀ a b, 0 < a → 1 < /a * b ↔ a < b.
    intros a b a_nz.
    rewrite lt_mult_1_ab_da_b_pos by (apply div_pos; exact a_nz).
    rewrite div_div by apply a_nz.
    reflexivity.
Qed.
Theorem lt_mult_adb_1_a_b_pos : ∀ a b, 0 < b → a / b < 1 ↔ a < b.
    intros a b b_nz.
    rewrite lt_mult_ab_1_a_db_pos by (apply div_pos; exact b_nz).
    rewrite div_div by apply b_nz.
    reflexivity.
Qed.
Theorem lt_mult_1_dab_b_a_pos : ∀ a b, 0 < a → /a * b < 1 ↔ b < a.
    intros a b a_nz.
    rewrite lt_mult_ab_1_b_da_pos by (apply div_pos; exact a_nz).
    rewrite div_div by apply a_nz.
    reflexivity.
Qed.
Theorem lt_mult_1_adb_b_a_pos : ∀ a b, 0 < b → 1 < a / b ↔ b < a.
    intros a b b_nz.
    rewrite lt_mult_1_ab_db_a_pos by (apply div_pos; exact b_nz).
    rewrite div_div by apply b_nz.
    reflexivity.
Qed.

Theorem lt_mult_llmove_neg : ∀ a b c, a < 0 → a * b < c ↔ /a * c < b.
    intros a b c a_neg.
    split; intros eq.
    -   apply lt_lmult_neg with (/a) in eq.
        2: apply div_neg; apply a_neg.
        rewrite mult_llinv in eq by (rewrite neq_sym; apply a_neg).
        exact eq.
    -   apply lt_lmult_neg with a in eq.
        2: apply a_neg.
        rewrite mult_lrinv in eq by (rewrite neq_sym; apply a_neg).
        exact eq.
Qed.
Theorem lt_mult_lrmove_neg : ∀ a b c, b < 0 → a * b < c ↔ c / b < a.
    intros a b c b_neg.
    split; intros eq.
    -   apply lt_rmult_neg with (/b) in eq.
        2: apply div_neg; apply b_neg.
        rewrite mult_rrinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
    -   apply lt_rmult_neg with b in eq.
        2: apply b_neg.
        rewrite mult_rlinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
Qed.
Theorem lt_mult_rlmove_neg : ∀ a b c, b < 0 → a < b * c ↔ c < /b * a.
    intros a b c b_neg.
    split; intros eq.
    -   apply lt_lmult_neg with (/b) in eq.
        2: apply div_neg; apply b_neg.
        rewrite mult_llinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
    -   apply lt_lmult_neg with b in eq.
        2: apply b_neg.
        rewrite mult_lrinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
Qed.
Theorem lt_mult_rrmove_neg : ∀ a b c, c < 0 → a < b * c ↔ b < a / c.
    intros a b c c_neg.
    split; intros eq.
    -   apply lt_rmult_neg with (/c) in eq.
        2: apply div_neg; apply c_neg.
        rewrite mult_rrinv in eq by (rewrite neq_sym; apply c_neg).
        exact eq.
    -   apply lt_rmult_neg with c in eq.
        2: apply c_neg.
        rewrite mult_rlinv in eq by (rewrite neq_sym; apply c_neg).
        exact eq.
Qed.

Theorem lt_mult_1_ab_b_da_neg : ∀ a b, a < 0 → 1 < a * b ↔ b < /a.
    intros a b a_nz.
    rewrite lt_mult_rlmove_neg by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem lt_mult_1_ab_a_db_neg : ∀ a b, b < 0 → 1 < a * b ↔ a < /b.
    intros a b b_nz.
    rewrite lt_mult_rrmove_neg by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem lt_mult_ab_1_db_a_neg : ∀ a b, b < 0 → a * b < 1 ↔ /b < a.
    intros a b b_nz.
    rewrite lt_mult_lrmove_neg by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem lt_mult_ab_1_da_b_neg : ∀ a b, a < 0 → a * b < 1 ↔ /a < b.
    intros a b a_nz.
    rewrite lt_mult_llmove_neg by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem lt_mult_a_1_b_ab_neg : ∀ a b, b < 0 → a < 1 ↔ b < a * b.
    intros a b b_nz.
    rewrite lt_mult_rrmove_neg by exact b_nz.
    rewrite mult_rinv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem lt_mult_a_1_b_ba_neg : ∀ a b, b < 0 → a < 1 ↔ b < b * a.
    intros a b b_nz.
    rewrite lt_mult_rlmove_neg by exact b_nz.
    rewrite mult_linv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem lt_mult_1_a_ab_b_neg : ∀ a b, b < 0 → 1 < a ↔ a * b < b.
    intros a b b_nz.
    rewrite lt_mult_lrmove_neg by exact b_nz.
    rewrite mult_rinv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem lt_mult_1_a_ba_b_neg : ∀ a b, b < 0 → 1 < a ↔ b * a < b.
    intros a b b_nz.
    rewrite lt_mult_llmove_neg by exact b_nz.
    rewrite mult_linv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.

Theorem lt_mult_1_dab_b_a_neg : ∀ a b, a < 0 → 1 < /a * b ↔ b < a.
    intros a b a_nz.
    rewrite lt_mult_1_ab_b_da_neg by (apply div_neg; exact a_nz).
    rewrite div_div by (rewrite neq_sym; apply a_nz).
    reflexivity.
Qed.
Theorem lt_mult_adb_1_b_a_neg : ∀ a b, b < 0 → a / b < 1 ↔ b < a.
    intros a b b_nz.
    rewrite lt_mult_ab_1_db_a_neg by (apply div_neg; exact b_nz).
    rewrite div_div by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem lt_mult_1_dab_a_b_neg : ∀ a b, a < 0 → /a * b < 1 ↔ a < b.
    intros a b a_nz.
    rewrite lt_mult_ab_1_da_b_neg by (apply div_neg; exact a_nz).
    rewrite div_div by (rewrite neq_sym; apply a_nz).
    reflexivity.
Qed.
Theorem lt_mult_1_adb_a_b_neg : ∀ a b, b < 0 → 1 < a / b ↔ a < b.
    intros a b b_nz.
    rewrite lt_mult_1_ab_a_db_neg by (apply div_neg; exact b_nz).
    rewrite div_div by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.

Theorem square_pos : ∀ a, 0 <= a * a.
    intros a.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply le_mult; exact a_pos.
    -   apply neg_pos in a_neg.
        pose proof (le_mult _ _ a_neg a_neg) as a_pos.
        rewrite mult_lneg, mult_rneg in a_pos.
        rewrite neg_neg in a_pos.
        exact a_pos.
Qed.

Theorem le_square : ∀ a b, 0 <= a → 0 <= b → a <= b ↔ a*a <= b*b.
    intros a b a_pos b_pos.
    split.
    -   intros ab.
        pose proof (le_lmult_pos a a_pos ab) as eq1.
        pose proof (le_rmult_pos b b_pos ab) as eq2.
        exact (trans eq1 eq2).
    -   intros ab.
        classic_case (0 = a) as [a_z|a_nz].
        1: {
            subst a.
            exact b_pos.
        }
        rewrite <- le_plus_0_anb_b_a in ab.
        rewrite dif_squares in ab.
        assert (0 < a) as a_pos2 by (split; assumption).
        apply lt_lplus with b in a_pos2.
        rewrite plus_rid in a_pos2.
        pose proof (le_lt_trans b_pos a_pos2) as ba_pos.
        rewrite <- (mult_ranni (b + a)) in ab.
        apply le_mult_lcancel_pos in ab.
        2: exact ba_pos.
        rewrite le_plus_0_anb_b_a in ab.
        exact ab.
Qed.

Theorem lt_square : ∀ a b, 0 <= a → 0 <= b → a < b ↔ a*a < b*b.
    intros a b a_pos b_pos.
    split.
    -   intros ab.
        split.
        +   rewrite <- le_square by assumption.
            apply ab.
        +   intros contr.
            rewrite <- (plus_0_anb_b_a) in contr.
            rewrite dif_squares in contr.
            apply mult_0 in contr.
            destruct contr as [eq|eq].
            *   apply plus_0_ab_a_nb in eq.
                subst b.
                apply pos_neg in b_pos.
                rewrite neg_neg in b_pos.
                pose proof (antisym a_pos b_pos); subst a.
                rewrite neg_zero in ab.
                destruct ab; contradiction.
            *   rewrite plus_0_anb_b_a in eq.
                subst.
                destruct ab; contradiction.
    -   intros ab.
        split.
        +   rewrite le_square by assumption.
            apply ab.
        +   intros contr.
            subst.
            destruct ab; contradiction.
Qed.
(* begin hide *)
End OrderMult.
(* end hide *)
