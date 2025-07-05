Require Import init.

Require Export order_mult_base.

Section OrderMult.

Context {U} `{OrderedFieldClass U}.

Theorem le_lmult_neg : ∀ {a b} c, c ≤ 0 → a ≤ b → c * b ≤ c * a.
Proof.
    intros a b c c_neg eq.
    apply neg_pos in c_neg.
    apply (le_lmult_pos _ c_neg) in eq.
    do 2 rewrite mult_lneg in eq.
    rewrite <- le_neg in eq.
    exact eq.
Qed.

Theorem le_rmult_neg : ∀ {a b} c, c ≤ 0 → a ≤ b → b * c ≤ a * c.
Proof.
    intros a b c c_neg eq.
    apply neg_pos in c_neg.
    apply (le_rmult_pos _ c_neg) in eq.
    do 2 rewrite mult_rneg in eq.
    rewrite <- le_neg in eq.
    exact eq.
Qed.

Theorem lt_lmult_neg : ∀ {a b} c, c < 0 → a < b → c * b < c * a.
Proof.
    intros a b c c_neg eq.
    apply neg_pos2 in c_neg.
    apply (lt_lmult_pos _ c_neg) in eq.
    do 2 rewrite mult_lneg in eq.
    rewrite <- lt_neg in eq.
    exact eq.
Qed.

Theorem lt_rmult_neg : ∀ {a b} c, c < 0 → a < b → b * c < a * c.
Proof.
    intros a b c c_neg eq.
    apply neg_pos2 in c_neg.
    apply (lt_rmult_pos _ c_neg) in eq.
    do 2 rewrite mult_rneg in eq.
    rewrite <- lt_neg in eq.
    exact eq.
Qed.

Theorem div_neg : ∀ {a}, a < 0 → /a < 0.
Proof.
    intros a a_neg.
    pose proof (land (neg_pos2 _) a_neg) as a_pos.
    apply div_pos in a_pos.
    rewrite neg_div in a_pos by (rewrite neq_sym; apply a_neg).
    rewrite <- neg_pos2 in a_pos.
    exact a_pos.
Qed.

Theorem le_mult_lcancel_neg : ∀ {a b} c, c < 0 → c * a ≤ c * b → b ≤ a.
Proof.
    intros a b c c_neg eq.
    apply le_lmult_neg with (/c) in eq; [>|apply div_neg; exact c_neg].
    do 2 rewrite mult_llinv in eq by (rewrite neq_sym; apply c_neg).
    exact eq.
Qed.
Theorem le_mult_rcancel_neg : ∀ {a b} c, c < 0 → a * c ≤ b * c → b ≤ a.
Proof.
    intros a b c c_neg eq.
    apply le_rmult_neg with (/c) in eq; [>|apply div_neg; exact c_neg].
    do 2 rewrite mult_rrinv in eq by (rewrite neq_sym; apply c_neg).
    exact eq.
Qed.
Theorem lt_mult_lcancel_neg : ∀ {a b} c, c < 0 → c * a < c * b → b < a.
Proof.
    intros a b c c_neg eq.
    apply lt_lmult_neg with (/c) in eq; [>|apply div_neg; exact c_neg].
    do 2 rewrite mult_llinv in eq by (rewrite neq_sym; apply c_neg).
    exact eq.
Qed.
Theorem lt_mult_rcancel_neg : ∀ {a b} c, c < 0 → a * c < b * c → b < a.
Proof.
    intros a b c c_neg eq.
    apply lt_rmult_neg with (/c) in eq; [>|apply div_neg; exact c_neg].
    do 2 rewrite mult_rrinv in eq by (rewrite neq_sym; apply c_neg).
    exact eq.
Qed.

Theorem le_mult_llmove_pos : ∀ a b c, 0 < a → a * b ≤ c ↔ b ≤ /a * c.
Proof.
    intros a b c a_pos.
    split; intros eq.
    -   apply le_lmult_pos with (/a) in eq; [>|apply div_pos; apply a_pos].
        rewrite mult_llinv in eq by apply a_pos.
        exact eq.
    -   apply le_lmult_pos with a in eq; [>|apply a_pos].
        rewrite mult_lrinv in eq by apply a_pos.
        exact eq.
Qed.
Theorem le_mult_lrmove_pos : ∀ a b c, 0 < b → a * b ≤ c ↔ a ≤ c / b.
Proof.
    intros a b c b_pos.
    split; intros eq.
    -   apply le_rmult_pos with (/b) in eq; [>|apply div_pos; apply b_pos].
        rewrite mult_rrinv in eq by apply b_pos.
        exact eq.
    -   apply le_rmult_pos with b in eq; [>|apply b_pos].
        rewrite mult_rlinv in eq by apply b_pos.
        exact eq.
Qed.
Theorem le_mult_rlmove_pos : ∀ a b c, 0 < b → a ≤ b * c ↔ /b * a ≤ c.
Proof.
    intros a b c b_pos.
    split; intros eq.
    -   apply le_lmult_pos with (/b) in eq; [>|apply div_pos; apply b_pos].
        rewrite mult_llinv in eq by apply b_pos.
        exact eq.
    -   apply le_lmult_pos with b in eq; [>|apply b_pos].
        rewrite mult_lrinv in eq by apply b_pos.
        exact eq.
Qed.
Theorem le_mult_rrmove_pos : ∀ a b c, 0 < c → a ≤ b * c ↔ a / c ≤ b.
Proof.
    intros a b c c_pos.
    split; intros eq.
    -   apply le_rmult_pos with (/c) in eq; [>|apply div_pos; apply c_pos].
        rewrite mult_rrinv in eq by apply c_pos.
        exact eq.
    -   apply le_rmult_pos with c in eq; [>|apply c_pos].
        rewrite mult_rlinv in eq by apply c_pos.
        exact eq.
Qed.

Theorem le_mult_1_ab_da_b_pos : ∀ a b, 0 < a → 1 ≤ a * b ↔ /a ≤ b.
Proof.
    intros a b a_nz.
    rewrite le_mult_rlmove_pos by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem le_mult_1_ab_db_a_pos : ∀ a b, 0 < b → 1 ≤ a * b ↔ /b ≤ a.
Proof.
    intros a b b_nz.
    rewrite le_mult_rrmove_pos by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem le_mult_ab_1_a_db_pos : ∀ a b, 0 < b → a * b ≤ 1 ↔ a ≤ /b.
Proof.
    intros a b b_nz.
    rewrite le_mult_lrmove_pos by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem le_mult_ab_1_b_da_pos : ∀ a b, 0 < a → a * b ≤ 1 ↔ b ≤ /a.
Proof.
    intros a b a_nz.
    rewrite le_mult_llmove_pos by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem le_mult_a_1_ab_b_pos : ∀ a b, 0 < b → a ≤ 1 ↔ a * b ≤ b.
Proof.
    intros a b b_nz.
    rewrite le_mult_lrmove_pos by exact b_nz.
    rewrite mult_rinv by apply b_nz.
    reflexivity.
Qed.
Theorem le_mult_a_1_ba_b_pos : ∀ a b, 0 < b → a ≤ 1 ↔ b * a ≤ b.
Proof.
    intros a b b_nz.
    rewrite le_mult_llmove_pos by exact b_nz.
    rewrite mult_linv by apply b_nz.
    reflexivity.
Qed.
Theorem le_mult_1_a_b_ab_pos : ∀ a b, 0 < b → 1 ≤ a ↔ b ≤ a * b.
Proof.
    intros a b b_nz.
    rewrite le_mult_rrmove_pos by exact b_nz.
    rewrite mult_rinv by apply b_nz.
    reflexivity.
Qed.
Theorem le_mult_1_a_b_ba_pos : ∀ a b, 0 < b → 1 ≤ a ↔ b ≤ b * a.
Proof.
    intros a b b_nz.
    rewrite le_mult_rlmove_pos by exact b_nz.
    rewrite mult_linv by apply b_nz.
    reflexivity.
Qed.

Theorem le_mult_1_dab_a_b_pos : ∀ a b, 0 < a → 1 ≤ /a * b ↔ a ≤ b.
Proof.
    intros a b a_nz.
    rewrite le_mult_1_ab_da_b_pos by (apply div_pos; exact a_nz).
    rewrite div_div by apply a_nz.
    reflexivity.
Qed.
Theorem le_mult_adb_1_a_b_pos : ∀ a b, 0 < b → a / b ≤ 1 ↔ a ≤ b.
Proof.
    intros a b b_nz.
    rewrite le_mult_ab_1_a_db_pos by (apply div_pos; exact b_nz).
    rewrite div_div by apply b_nz.
    reflexivity.
Qed.
Theorem le_mult_1_dab_b_a_pos : ∀ a b, 0 < a → /a * b ≤ 1 ↔ b ≤ a.
Proof.
    intros a b a_nz.
    rewrite le_mult_ab_1_b_da_pos by (apply div_pos; exact a_nz).
    rewrite div_div by apply a_nz.
    reflexivity.
Qed.
Theorem le_mult_1_adb_b_a_pos : ∀ a b, 0 < b → 1 ≤ a / b ↔ b ≤ a.
Proof.
    intros a b b_nz.
    rewrite le_mult_1_ab_db_a_pos by (apply div_pos; exact b_nz).
    rewrite div_div by apply b_nz.
    reflexivity.
Qed.

Theorem le_mult_llmove_neg : ∀ a b c, a < 0 → a * b ≤ c ↔ /a * c ≤ b.
Proof.
    intros a b c a_neg.
    split; intros eq.
    -   apply le_lmult_neg with (/a) in eq; [>|apply div_neg; apply a_neg].
        rewrite mult_llinv in eq by (rewrite neq_sym; apply a_neg).
        exact eq.
    -   apply le_lmult_neg with a in eq; [>|apply a_neg].
        rewrite mult_lrinv in eq by (rewrite neq_sym; apply a_neg).
        exact eq.
Qed.
Theorem le_mult_lrmove_neg : ∀ a b c, b < 0 → a * b ≤ c ↔ c / b ≤ a.
Proof.
    intros a b c b_neg.
    split; intros eq.
    -   apply le_rmult_neg with (/b) in eq; [>|apply div_neg; apply b_neg].
        rewrite mult_rrinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
    -   apply le_rmult_neg with b in eq; [>|apply b_neg].
        rewrite mult_rlinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
Qed.
Theorem le_mult_rlmove_neg : ∀ a b c, b < 0 → a ≤ b * c ↔ c ≤ /b * a.
Proof.
    intros a b c b_neg.
    split; intros eq.
    -   apply le_lmult_neg with (/b) in eq; [>|apply div_neg; apply b_neg].
        rewrite mult_llinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
    -   apply le_lmult_neg with b in eq; [>|apply b_neg].
        rewrite mult_lrinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
Qed.
Theorem le_mult_rrmove_neg : ∀ a b c, c < 0 → a ≤ b * c ↔ b ≤ a / c.
Proof.
    intros a b c c_neg.
    split; intros eq.
    -   apply le_rmult_neg with (/c) in eq; [>|apply div_neg; apply c_neg].
        rewrite mult_rrinv in eq by (rewrite neq_sym; apply c_neg).
        exact eq.
    -   apply le_rmult_neg with c in eq; [>|apply c_neg].
        rewrite mult_rlinv in eq by (rewrite neq_sym; apply c_neg).
        exact eq.
Qed.

Theorem le_mult_1_ab_b_da_neg : ∀ a b, a < 0 → 1 ≤ a * b ↔ b ≤ /a.
Proof.
    intros a b a_nz.
    rewrite le_mult_rlmove_neg by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem le_mult_1_ab_a_db_neg : ∀ a b, b < 0 → 1 ≤ a * b ↔ a ≤ /b.
Proof.
    intros a b b_nz.
    rewrite le_mult_rrmove_neg by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem le_mult_ab_1_db_a_neg : ∀ a b, b < 0 → a * b ≤ 1 ↔ /b ≤ a.
Proof.
    intros a b b_nz.
    rewrite le_mult_lrmove_neg by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem le_mult_ab_1_da_b_neg : ∀ a b, a < 0 → a * b ≤ 1 ↔ /a ≤ b.
Proof.
    intros a b a_nz.
    rewrite le_mult_llmove_neg by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem le_mult_a_1_b_ab_neg : ∀ a b, b < 0 → a ≤ 1 ↔ b ≤ a * b.
Proof.
    intros a b b_nz.
    rewrite le_mult_rrmove_neg by exact b_nz.
    rewrite mult_rinv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem le_mult_a_1_b_ba_neg : ∀ a b, b < 0 → a ≤ 1 ↔ b ≤ b * a.
Proof.
    intros a b b_nz.
    rewrite le_mult_rlmove_neg by exact b_nz.
    rewrite mult_linv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem le_mult_1_a_ab_b_neg : ∀ a b, b < 0 → 1 ≤ a ↔ a * b ≤ b.
Proof.
    intros a b b_nz.
    rewrite le_mult_lrmove_neg by exact b_nz.
    rewrite mult_rinv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem le_mult_1_a_ba_b_neg : ∀ a b, b < 0 → 1 ≤ a ↔ b * a ≤ b.
Proof.
    intros a b b_nz.
    rewrite le_mult_llmove_neg by exact b_nz.
    rewrite mult_linv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.

Theorem le_mult_1_dab_b_a_neg : ∀ a b, a < 0 → 1 ≤ /a * b ↔ b ≤ a.
Proof.
    intros a b a_nz.
    rewrite le_mult_1_ab_b_da_neg by (apply div_neg; exact a_nz).
    rewrite div_div by (rewrite neq_sym; apply a_nz).
    reflexivity.
Qed.
Theorem le_mult_adb_1_b_a_neg : ∀ a b, b < 0 → a / b ≤ 1 ↔ b ≤ a.
Proof.
    intros a b b_nz.
    rewrite le_mult_ab_1_db_a_neg by (apply div_neg; exact b_nz).
    rewrite div_div by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem le_mult_1_dab_a_b_neg : ∀ a b, a < 0 → /a * b ≤ 1 ↔ a ≤ b.
Proof.
    intros a b a_nz.
    rewrite le_mult_ab_1_da_b_neg by (apply div_neg; exact a_nz).
    rewrite div_div by (rewrite neq_sym; apply a_nz).
    reflexivity.
Qed.
Theorem le_mult_1_adb_a_b_neg : ∀ a b, b < 0 → 1 ≤ a / b ↔ a ≤ b.
Proof.
    intros a b b_nz.
    rewrite le_mult_1_ab_a_db_neg by (apply div_neg; exact b_nz).
    rewrite div_div by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.

Theorem lt_mult_llmove_pos : ∀ a b c, 0 < a → a * b < c ↔ b < /a * c.
Proof.
    intros a b c a_pos.
    split; intros eq.
    -   apply lt_lmult_pos with (/a) in eq; [>|apply div_pos; apply a_pos].
        rewrite mult_llinv in eq by apply a_pos.
        exact eq.
    -   apply lt_lmult_pos with a in eq; [>|apply a_pos].
        rewrite mult_lrinv in eq by apply a_pos.
        exact eq.
Qed.
Theorem lt_mult_lrmove_pos : ∀ a b c, 0 < b → a * b < c ↔ a < c / b.
Proof.
    intros a b c b_pos.
    split; intros eq.
    -   apply lt_rmult_pos with (/b) in eq; [>|apply div_pos; apply b_pos].
        rewrite mult_rrinv in eq by apply b_pos.
        exact eq.
    -   apply lt_rmult_pos with b in eq; [>|apply b_pos].
        rewrite mult_rlinv in eq by apply b_pos.
        exact eq.
Qed.
Theorem lt_mult_rlmove_pos : ∀ a b c, 0 < b → a < b * c ↔ /b * a < c.
Proof.
    intros a b c b_pos.
    split; intros eq.
    -   apply lt_lmult_pos with (/b) in eq; [>|apply div_pos; apply b_pos].
        rewrite mult_llinv in eq by apply b_pos.
        exact eq.
    -   apply lt_lmult_pos with b in eq; [>|apply b_pos].
        rewrite mult_lrinv in eq by apply b_pos.
        exact eq.
Qed.
Theorem lt_mult_rrmove_pos : ∀ a b c, 0 < c → a < b * c ↔ a / c < b.
Proof.
    intros a b c c_pos.
    split; intros eq.
    -   apply lt_rmult_pos with (/c) in eq; [>|apply div_pos; apply c_pos].
        rewrite mult_rrinv in eq by apply c_pos.
        exact eq.
    -   apply lt_rmult_pos with c in eq; [>|apply c_pos].
        rewrite mult_rlinv in eq by apply c_pos.
        exact eq.
Qed.

Theorem lt_mult_1_ab_da_b_pos : ∀ a b, 0 < a → 1 < a * b ↔ /a < b.
Proof.
    intros a b a_nz.
    rewrite lt_mult_rlmove_pos by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem lt_mult_1_ab_db_a_pos : ∀ a b, 0 < b → 1 < a * b ↔ /b < a.
Proof.
    intros a b b_nz.
    rewrite lt_mult_rrmove_pos by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem lt_mult_ab_1_a_db_pos : ∀ a b, 0 < b → a * b < 1 ↔ a < /b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_lrmove_pos by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem lt_mult_ab_1_b_da_pos : ∀ a b, 0 < a → a * b < 1 ↔ b < /a.
Proof.
    intros a b a_nz.
    rewrite lt_mult_llmove_pos by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem lt_mult_a_1_ab_b_pos : ∀ a b, 0 < b → a < 1 ↔ a * b < b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_lrmove_pos by exact b_nz.
    rewrite mult_rinv by apply b_nz.
    reflexivity.
Qed.
Theorem lt_mult_a_1_ba_b_pos : ∀ a b, 0 < b → a < 1 ↔ b * a < b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_llmove_pos by exact b_nz.
    rewrite mult_linv by apply b_nz.
    reflexivity.
Qed.
Theorem lt_mult_1_a_b_ab_pos : ∀ a b, 0 < b → 1 < a ↔ b < a * b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_rrmove_pos by exact b_nz.
    rewrite mult_rinv by apply b_nz.
    reflexivity.
Qed.
Theorem lt_mult_1_a_b_ba_pos : ∀ a b, 0 < b → 1 < a ↔ b < b * a.
Proof.
    intros a b b_nz.
    rewrite lt_mult_rlmove_pos by exact b_nz.
    rewrite mult_linv by apply b_nz.
    reflexivity.
Qed.

Theorem lt_mult_1_dab_a_b_pos : ∀ a b, 0 < a → 1 < /a * b ↔ a < b.
Proof.
    intros a b a_nz.
    rewrite lt_mult_1_ab_da_b_pos by (apply div_pos; exact a_nz).
    rewrite div_div by apply a_nz.
    reflexivity.
Qed.
Theorem lt_mult_adb_1_a_b_pos : ∀ a b, 0 < b → a / b < 1 ↔ a < b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_ab_1_a_db_pos by (apply div_pos; exact b_nz).
    rewrite div_div by apply b_nz.
    reflexivity.
Qed.
Theorem lt_mult_1_dab_b_a_pos : ∀ a b, 0 < a → /a * b < 1 ↔ b < a.
Proof.
    intros a b a_nz.
    rewrite lt_mult_ab_1_b_da_pos by (apply div_pos; exact a_nz).
    rewrite div_div by apply a_nz.
    reflexivity.
Qed.
Theorem lt_mult_1_adb_b_a_pos : ∀ a b, 0 < b → 1 < a / b ↔ b < a.
Proof.
    intros a b b_nz.
    rewrite lt_mult_1_ab_db_a_pos by (apply div_pos; exact b_nz).
    rewrite div_div by apply b_nz.
    reflexivity.
Qed.

Theorem lt_mult_llmove_neg : ∀ a b c, a < 0 → a * b < c ↔ /a * c < b.
Proof.
    intros a b c a_neg.
    split; intros eq.
    -   apply lt_lmult_neg with (/a) in eq; [>|apply div_neg; apply a_neg].
        rewrite mult_llinv in eq by (rewrite neq_sym; apply a_neg).
        exact eq.
    -   apply lt_lmult_neg with a in eq; [>|apply a_neg].
        rewrite mult_lrinv in eq by (rewrite neq_sym; apply a_neg).
        exact eq.
Qed.
Theorem lt_mult_lrmove_neg : ∀ a b c, b < 0 → a * b < c ↔ c / b < a.
Proof.
    intros a b c b_neg.
    split; intros eq.
    -   apply lt_rmult_neg with (/b) in eq; [>|apply div_neg; apply b_neg].
        rewrite mult_rrinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
    -   apply lt_rmult_neg with b in eq; [>|apply b_neg].
        rewrite mult_rlinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
Qed.
Theorem lt_mult_rlmove_neg : ∀ a b c, b < 0 → a < b * c ↔ c < /b * a.
Proof.
    intros a b c b_neg.
    split; intros eq.
    -   apply lt_lmult_neg with (/b) in eq; [>|apply div_neg; apply b_neg].
        rewrite mult_llinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
    -   apply lt_lmult_neg with b in eq; [>|apply b_neg].
        rewrite mult_lrinv in eq by (rewrite neq_sym; apply b_neg).
        exact eq.
Qed.
Theorem lt_mult_rrmove_neg : ∀ a b c, c < 0 → a < b * c ↔ b < a / c.
Proof.
    intros a b c c_neg.
    split; intros eq.
    -   apply lt_rmult_neg with (/c) in eq; [>|apply div_neg; apply c_neg].
        rewrite mult_rrinv in eq by (rewrite neq_sym; apply c_neg).
        exact eq.
    -   apply lt_rmult_neg with c in eq; [>|apply c_neg].
        rewrite mult_rlinv in eq by (rewrite neq_sym; apply c_neg).
        exact eq.
Qed.

Theorem lt_mult_1_ab_b_da_neg : ∀ a b, a < 0 → 1 < a * b ↔ b < /a.
Proof.
    intros a b a_nz.
    rewrite lt_mult_rlmove_neg by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.
Theorem lt_mult_1_ab_a_db_neg : ∀ a b, b < 0 → 1 < a * b ↔ a < /b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_rrmove_neg by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem lt_mult_ab_1_db_a_neg : ∀ a b, b < 0 → a * b < 1 ↔ /b < a.
Proof.
    intros a b b_nz.
    rewrite lt_mult_lrmove_neg by exact b_nz.
    rewrite mult_lid.
    reflexivity.
Qed.
Theorem lt_mult_ab_1_da_b_neg : ∀ a b, a < 0 → a * b < 1 ↔ /a < b.
Proof.
    intros a b a_nz.
    rewrite lt_mult_llmove_neg by exact a_nz.
    rewrite mult_rid.
    reflexivity.
Qed.

Theorem lt_mult_a_1_b_ab_neg : ∀ a b, b < 0 → a < 1 ↔ b < a * b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_rrmove_neg by exact b_nz.
    rewrite mult_rinv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem lt_mult_a_1_b_ba_neg : ∀ a b, b < 0 → a < 1 ↔ b < b * a.
Proof.
    intros a b b_nz.
    rewrite lt_mult_rlmove_neg by exact b_nz.
    rewrite mult_linv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem lt_mult_1_a_ab_b_neg : ∀ a b, b < 0 → 1 < a ↔ a * b < b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_lrmove_neg by exact b_nz.
    rewrite mult_rinv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem lt_mult_1_a_ba_b_neg : ∀ a b, b < 0 → 1 < a ↔ b * a < b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_llmove_neg by exact b_nz.
    rewrite mult_linv by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.

Theorem lt_mult_1_dab_b_a_neg : ∀ a b, a < 0 → 1 < /a * b ↔ b < a.
Proof.
    intros a b a_nz.
    rewrite lt_mult_1_ab_b_da_neg by (apply div_neg; exact a_nz).
    rewrite div_div by (rewrite neq_sym; apply a_nz).
    reflexivity.
Qed.
Theorem lt_mult_adb_1_b_a_neg : ∀ a b, b < 0 → a / b < 1 ↔ b < a.
Proof.
    intros a b b_nz.
    rewrite lt_mult_ab_1_db_a_neg by (apply div_neg; exact b_nz).
    rewrite div_div by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.
Theorem lt_mult_1_dab_a_b_neg : ∀ a b, a < 0 → /a * b < 1 ↔ a < b.
Proof.
    intros a b a_nz.
    rewrite lt_mult_ab_1_da_b_neg by (apply div_neg; exact a_nz).
    rewrite div_div by (rewrite neq_sym; apply a_nz).
    reflexivity.
Qed.
Theorem lt_mult_1_adb_a_b_neg : ∀ a b, b < 0 → 1 < a / b ↔ a < b.
Proof.
    intros a b b_nz.
    rewrite lt_mult_1_ab_a_db_neg by (apply div_neg; exact b_nz).
    rewrite div_div by (rewrite neq_sym; apply b_nz).
    reflexivity.
Qed.

Theorem le_lrmult_pos : ∀ a b c d, 0 ≤ a → 0 ≤ c → a ≤ b → c ≤ d →
    a * c ≤ b * d.
Proof.
    intros a b c d a_pos c_pos ab cd.
    pose proof (trans a_pos ab) as b_pos.
    apply le_rmult_pos with c in ab; [>|exact c_pos].
    apply le_lmult_pos with b in cd; [>|exact b_pos].
    exact (trans ab cd).
Qed.

Theorem lt_lrmult_pos : ∀ a b c d, 0 ≤ a → 0 ≤ c → a < b → c < d →
    a * c < b * d.
Proof.
    intros a b c d a_pos c_pos ab cd.
    pose proof (le_lt_trans a_pos ab) as b_pos.
    classic_case (0 = c) as [c_z|c_nz].
    {
        subst c.
        rewrite mult_ranni.
        apply lt_mult.
        -   exact b_pos.
        -   exact cd.
    }
    apply lt_rmult_pos with c in ab; [>|split; assumption].
    apply lt_lmult_pos with b in cd; [>|exact b_pos].
    exact (trans ab cd).
Qed.

Theorem square_pos : ∀ a, 0 ≤ a * a.
Proof.
    intros a.
    destruct (connex 0 a) as [a_pos|a_neg].
    -   apply le_mult; exact a_pos.
    -   apply neg_pos in a_neg.
        pose proof (le_mult a_neg a_neg) as a_pos.
        rewrite mult_lneg, mult_rneg in a_pos.
        rewrite neg_neg in a_pos.
        exact a_pos.
Qed.

Theorem le_square : ∀ a b, 0 ≤ a → 0 ≤ b → a ≤ b ↔ a*a ≤ b*b.
Proof.
    intros a b a_pos b_pos.
    split.
    -   intros ab.
        apply le_lrmult_pos; assumption.
    -   intros ab.
        classic_case (0 = a) as [a_z|a_nz].
        {
            subst a.
            exact b_pos.
        }
        rewrite <- le_plus_0_anb_b_a in ab.
        rewrite dif_squares in ab.
        assert (0 < a) as a_pos2 by (split; assumption).
        pose proof (le_lt_pos_plus b_pos a_pos2) as ba_pos.
        rewrite <- (mult_ranni (b + a)) in ab.
        apply le_mult_lcancel_pos in ab; [>|exact ba_pos].
        rewrite le_plus_0_anb_b_a in ab.
        exact ab.
Qed.

Theorem lt_square : ∀ a b, 0 ≤ a → 0 ≤ b → a < b ↔ a*a < b*b.
Proof.
    intros a b a_pos b_pos.
    split.
    -   intros ab.
        apply lt_lrmult_pos; assumption.
    -   intros ab.
        split.
        +   rewrite le_square by assumption.
            apply ab.
        +   intros contr.
            subst.
            destruct ab; contradiction.
Qed.

Theorem one_pos : 0 < 1.
Proof.
    split; [>|exact not_trivial_one].
    classic_contradiction contr.
    rewrite nle_lt in contr.
    pose proof (land (neg_pos2 _) contr) as eq.
    pose proof (lt_mult eq eq) as eq2.
    rewrite mult_rneg, mult_lneg in eq2.
    rewrite neg_neg in eq2.
    rewrite mult_lid in eq2.
    destruct (trans contr eq2); contradiction.
Qed.

Theorem two_pos : 0 < 2.
Proof.
    exact (lt_pos_plus one_pos one_pos).
Qed.

Theorem lt_1_2 : 1 < 2.
Proof.
    rewrite <- lt_plus_0_a_b_ba.
    exact one_pos.
Qed.

Theorem three_pos : 0 < 3.
Proof.
    exact (lt_pos_plus one_pos two_pos).
Qed.

Theorem four_pos : 0 < 4.
Proof.
    exact (lt_pos_plus one_pos three_pos).
Qed.

Theorem inv_ge_one : ∀ a, 1 ≤ a → /a ≤ 1.
Proof.
    intros a a_ge.
    pose proof (lt_le_trans one_pos a_ge) as a_pos.
    apply le_mult_rcancel_pos with a; [>exact a_pos|].
    rewrite mult_linv by apply a_pos.
    rewrite mult_lid.
    exact a_ge.
Qed.

Theorem inv_le_one : ∀ a, 0 < a → a ≤ 1 → 1 ≤ /a.
Proof.
    intros a a_pos a_leq.
    apply le_mult_rcancel_pos with a; [>exact a_pos|].
    rewrite mult_linv by apply a_pos.
    rewrite mult_lid.
    exact a_leq.
Qed.

Theorem inv_gt_one : ∀ a, 1 < a → /a < 1.
Proof.
    intros a a_gt.
    pose proof (trans one_pos a_gt) as a_pos.
    apply lt_mult_rcancel_pos with a; [>exact a_pos|].
    rewrite mult_linv by apply a_pos.
    rewrite mult_lid.
    exact a_gt.
Qed.

Theorem inv_lt_one : ∀ a, 0 < a → a < 1 → 1 < /a.
Proof.
    intros a a_pos a_ltq.
    apply lt_mult_rcancel_pos with a; [>exact a_pos|].
    rewrite mult_linv by apply a_pos.
    rewrite mult_lid.
    exact a_ltq.
Qed.

Theorem square_one_one_pos : ∀ a, 0 < a → a * a = 1 → a = 1.
Proof.
    intros a a_pos eq.
    rewrite <- (mult_lid 1) in eq.
    rewrite <- plus_0_anb_a_b in eq.
    rewrite dif_squares in eq.
    rewrite <- plus_0_anb_a_b.
    classic_contradiction contr.
    apply mult_zero in eq as [eq|eq]; [>|contradiction].
    rewrite plus_0_ab_a_nb in eq.
    rewrite eq in a_pos.
    apply neg_pos2 in a_pos.
    destruct (trans a_pos one_pos); contradiction.
Qed.
Theorem square_one_one : ∀ a, a * a = 1 → a = 1 ∨ a = -(1).
Proof.
    intros a eq.
    destruct (trichotomy 0 a) as [[a_pos|a_z]|a_neg].
    -   left.
        apply square_one_one_pos; assumption.
    -   subst.
        rewrite mult_ranni in eq.
        contradiction (not_trivial_one eq).
    -   right.
        rewrite <- (neg_neg a).
        rewrite <- neg_eq.
        apply square_one_one_pos.
        +   apply neg_pos2 in a_neg.
            exact a_neg.
        +   rewrite mult_lneg, mult_rneg, neg_neg.
            exact eq.
Qed.

Theorem plus_half : ∀ a, a / 2 + a / 2 = a.
Proof.
    intros a.
    rewrite <- ldist.
    rewrite <- (mult_lid (/2)).
    rewrite <- rdist.
    rewrite mult_rinv by apply two_pos.
    apply mult_rid.
Qed.

Theorem minus_half : ∀ a, a - (a/2) = a/2.
Proof.
    intros a.
    rewrite <- (plus_half a) at 1.
    apply plus_rrinv.
Qed.

Theorem half_minus : ∀ a, a/2 - a = -(a/2).
Proof.
    intros a.
    rewrite <- (plus_half a) at 2.
    rewrite neg_plus.
    apply plus_lrinv.
Qed.

Theorem le_div_pos : ∀ a b, 0 < a → a ≤ b → /b ≤ /a.
Proof.
    intros a b a_pos ab.
    pose proof (lt_le_trans a_pos ab) as b_pos.
    rewrite <- le_mult_1_adb_b_a_pos in ab by exact a_pos.
    rewrite le_mult_1_ab_da_b_pos in ab by exact b_pos.
    exact ab.
Qed.

Theorem le_div_neg : ∀ a b, b < 0 → a ≤ b → /b ≤ /a.
Proof.
    intros a b b_neg ab.
    pose proof (le_lt_trans ab b_neg) as a_neg.
    rewrite <- le_mult_1_adb_a_b_neg in ab by exact b_neg.
    rewrite le_mult_1_ab_b_da_neg in ab by exact a_neg.
    exact ab.
Qed.

Theorem lt_div_pos : ∀ a b, 0 < a → a < b → /b < /a.
Proof.
    intros a b a_pos ab.
    pose proof (trans a_pos ab) as b_pos.
    rewrite <- lt_mult_1_adb_b_a_pos in ab by exact a_pos.
    rewrite lt_mult_1_ab_da_b_pos in ab by exact b_pos.
    exact ab.
Qed.

Theorem lt_div_neg : ∀ a b, b < 0 → a < b → div b < div a.
Proof.
    intros a b b_neg ab.
    pose proof (trans ab b_neg) as a_neg.
    rewrite <- lt_mult_1_adb_a_b_neg in ab by exact b_neg.
    rewrite lt_mult_1_ab_b_da_neg in ab by exact a_neg.
    exact ab.
Qed.

Theorem half_pos : ∀ {a}, 0 < a → 0 < a / 2.
Proof.
    intros a a_pos.
    apply lt_mult_rcancel_pos with 2; [>exact two_pos|].
    rewrite mult_lanni.
    rewrite mult_rlinv by apply two_pos.
    exact a_pos.
Qed.
Theorem half_neg : ∀ {a}, a < 0 → a / 2 < 0.
Proof.
    intros a a_neg.
    apply lt_mult_rcancel_pos with 2; [>exact two_pos|].
    rewrite mult_lanni.
    rewrite mult_rlinv by apply two_pos.
    exact a_neg.
Qed.

Theorem double_pos : ∀ a, 0 < a → 0 < 2 * a.
Proof.
    intros a a_pos.
    rewrite rdist, mult_lid.
    apply lt_pos_plus; exact a_pos.
Qed.
Theorem double_neg : ∀ a, a < 0 → 2 * a < 0.
Proof.
    intros a a_neg.
    rewrite rdist, mult_lid.
    apply lt_neg_plus; exact a_neg.
Qed.

Theorem average_leq1 : ∀ a b, a < b → a < (a + b) / 2.
Proof.
    intros a b ltq.
    rewrite rdist.
    rewrite <- (plus_half a) at 1.
    apply lt_lplus.
    apply lt_rmult_pos; [>apply div_pos; exact two_pos|].
    exact ltq.
Qed.

Theorem average_leq2 : ∀ a b, a < b → (a + b) / 2 < b.
Proof.
    intros a b ltq.
    rewrite rdist.
    rewrite <- (plus_half b) at 2.
    apply lt_rplus.
    apply lt_rmult_pos; [>apply div_pos; exact two_pos|].
    exact ltq.
Qed.

Theorem lt_plus_one : ∀ a, a < a + 1.
Proof.
    intros a.
    rewrite <- lt_plus_0_a_b_ba.
    exact one_pos.
Qed.

Theorem lt_minus_one : ∀ a, a - 1 < a.
Proof.
    intros a.
    rewrite <- lt_plus_rrmove.
    apply lt_plus_one.
Qed.

Global Instance ordered_field_dense_class : Dense (strict le).
Proof.
    split.
    intros a b ab.
    exists ((a + b) / 2).
    split.
    -   apply lt_mult_rcancel_pos with 2; [>exact two_pos|].
        rewrite mult_rlinv by apply two_pos.
        rewrite <- mult_comm, <- plus_two.
        apply lt_lplus.
        exact ab.
    -   apply lt_mult_rcancel_pos with 2; [>exact two_pos|].
        rewrite mult_rlinv by apply two_pos.
        rewrite <- mult_comm, <- plus_two.
        apply lt_rplus.
        exact ab.
Qed.

End OrderMult.
