Require Import init.

Require Export order_plus_base.

Section OrderPlus.

Context {U} `{OrderPlusClass U}.

Theorem le_lrplus : ∀ {a b c d}, a ≤ b → c ≤ d → a + c ≤ b + d.
Proof.
    intros a b c d ab cd.
    apply le_rplus with c in ab.
    apply le_lplus with b in cd.
    exact (trans ab cd).
Qed.

Theorem lt_lrplus : ∀ {a b c d}, a < b → c < d → a + c < b + d.
Proof.
    intros a b c d ab cd.
    apply lt_rplus with c in ab.
    apply lt_lplus with b in cd.
    exact (trans ab cd).
Qed.

Theorem le_lt_lrplus : ∀ {a b c d}, a ≤ b → c < d → a + c < b + d.
Proof.
    intros a b c d ab cd.
    apply le_rplus with c in ab.
    apply lt_lplus with b in cd.
    exact (le_lt_trans ab cd).
Qed.

Theorem lt_le_lrplus : ∀ {a b c d}, a < b → c ≤ d → a + c < b + d.
Proof.
    intros a b c d ab cd.
    apply lt_rplus with c in ab.
    apply le_lplus with b in cd.
    exact (lt_le_trans ab cd).
Qed.

Theorem le_plus_llmove : ∀ a b c, a + b ≤ c ↔ b ≤ -a + c.
Proof.
    intros a b c.
    split; intros eq.
    -   apply le_lplus with (-a) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply le_lplus with a in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem le_plus_lrmove : ∀ a b c, a + b ≤ c ↔ a ≤ c - b.
Proof.
    intros a b c.
    split; intros eq.
    -   apply le_rplus with (-b) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply le_rplus with b in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.
Theorem le_plus_rlmove : ∀ a b c, a ≤ b + c ↔ -b + a ≤ c.
Proof.
    intros a b c.
    split; intros eq.
    -   apply le_lplus with (-b) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply le_lplus with b in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem le_plus_rrmove : ∀ a b c, a ≤ b + c ↔ a - c ≤ b.
Proof.
    intros a b c.
    split; intros eq.
    -   apply le_rplus with (-c) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply le_rplus with c in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.

Theorem le_plus_0_ab_na_b : ∀ a b, 0 ≤ a + b ↔ -a ≤ b.
Proof.
    intros a b.
    rewrite le_plus_rlmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem le_plus_0_ab_nb_a : ∀ a b, 0 ≤ a + b ↔ -b ≤ a.
Proof.
    intros a b.
    rewrite le_plus_rrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem le_plus_ab_0_a_nb : ∀ a b, a + b ≤ 0 ↔ a ≤ -b.
Proof.
    intros a b.
    rewrite le_plus_lrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem le_plus_ab_0_b_na : ∀ a b, a + b ≤ 0 ↔ b ≤ -a.
Proof.
    intros a b.
    rewrite le_plus_llmove.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem le_plus_a_0_ab_b : ∀ a b, a ≤ 0 ↔ a + b ≤ b.
Proof.
    intros a b.
    split; intros leq.
    -   apply le_rplus with b in leq.
        rewrite plus_lid in leq.
        exact leq.
    -   apply le_plus_rcancel with b.
        rewrite plus_lid.
        exact leq.
Qed.
Theorem le_plus_a_0_ba_b : ∀ a b, a ≤ 0 ↔ b + a ≤ b.
Proof.
    intros a b.
    split; intros leq.
    -   apply le_lplus with b in leq.
        rewrite plus_rid in leq.
        exact leq.
    -   apply le_plus_lcancel with b.
        rewrite plus_rid.
        exact leq.
Qed.
Theorem le_plus_0_a_b_ab : ∀ a b, 0 ≤ a ↔ b ≤ a + b.
Proof.
    intros a b.
    split; intros leq.
    -   apply le_rplus with b in leq.
        rewrite plus_lid in leq.
        exact leq.
    -   apply le_plus_rcancel with b.
        rewrite plus_lid.
        exact leq.
Qed.
Theorem le_plus_0_a_b_ba : ∀ a b, 0 ≤ a ↔ b ≤ b + a.
Proof.
    intros a b.
    split; intros leq.
    -   apply le_lplus with b in leq.
        rewrite plus_rid in leq.
        exact leq.
    -   apply le_plus_lcancel with b.
        rewrite plus_rid.
        exact leq.
Qed.

Theorem le_plus_0_nab_a_b : ∀ a b, 0 ≤ -a + b ↔ a ≤ b.
Proof.
    intros a b.
    rewrite <- le_plus_llmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem le_plus_anb_0_a_b : ∀ a b, a - b ≤ 0 ↔ a ≤ b.
Proof.
    intros a b.
    rewrite <- le_plus_rrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem le_plus_nab_0_b_a : ∀ a b, -a + b ≤ 0 ↔ b ≤ a.
Proof.
    intros a b.
    rewrite <- le_plus_rlmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem le_plus_0_anb_b_a : ∀ a b, 0 ≤ a - b ↔ b ≤ a.
Proof.
    intros a b.
    rewrite <- le_plus_lrmove.
    rewrite plus_lid.
    reflexivity.
Qed.

Theorem lt_plus_llmove : ∀ a b c, a + b < c ↔ b < -a + c.
Proof.
    intros a b c.
    split; intros eq.
    -   apply lt_lplus with (-a) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply lt_lplus with a in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem lt_plus_lrmove : ∀ a b c, a + b < c ↔ a < c - b.
Proof.
    intros a b c.
    split; intros eq.
    -   apply lt_rplus with (-b) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply lt_rplus with b in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.
Theorem lt_plus_rlmove : ∀ a b c, a < b + c ↔ -b + a < c.
Proof.
    intros a b c.
    split; intros eq.
    -   apply lt_lplus with (-b) in eq.
        rewrite plus_llinv in eq.
        exact eq.
    -   apply lt_lplus with b in eq.
        rewrite plus_lrinv in eq.
        exact eq.
Qed.
Theorem lt_plus_rrmove : ∀ a b c, a < b + c ↔ a - c < b.
Proof.
    intros a b c.
    split; intros eq.
    -   apply lt_rplus with (-c) in eq.
        rewrite plus_rrinv in eq.
        exact eq.
    -   apply lt_rplus with c in eq.
        rewrite plus_rlinv in eq.
        exact eq.
Qed.

Theorem lt_plus_0_ab_na_b : ∀ a b, 0 < a + b ↔ -a < b.
Proof.
    intros a b.
    rewrite lt_plus_rlmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem lt_plus_0_ab_nb_a : ∀ a b, 0 < a + b ↔ -b < a.
Proof.
    intros a b.
    rewrite lt_plus_rrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem lt_plus_ab_0_a_nb : ∀ a b, a + b < 0 ↔ a < -b.
Proof.
    intros a b.
    rewrite lt_plus_lrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem lt_plus_ab_0_b_na : ∀ a b, a + b < 0 ↔ b < -a.
Proof.
    intros a b.
    rewrite lt_plus_llmove.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem lt_plus_a_0_ab_b : ∀ a b, a < 0 ↔ a + b < b.
Proof.
    intros a b.
    split; intros ltq.
    -   apply lt_rplus with b in ltq.
        rewrite plus_lid in ltq.
        exact ltq.
    -   apply lt_plus_rcancel with b.
        rewrite plus_lid.
        exact ltq.
Qed.
Theorem lt_plus_a_0_ba_b : ∀ a b, a < 0 ↔ b + a < b.
Proof.
    intros a b.
    split; intros ltq.
    -   apply lt_lplus with b in ltq.
        rewrite plus_rid in ltq.
        exact ltq.
    -   apply lt_plus_lcancel with b.
        rewrite plus_rid.
        exact ltq.
Qed.
Theorem lt_plus_0_a_b_ab : ∀ a b, 0 < a ↔ b < a + b.
Proof.
    intros a b.
    split; intros ltq.
    -   apply lt_rplus with b in ltq.
        rewrite plus_lid in ltq.
        exact ltq.
    -   apply lt_plus_rcancel with b.
        rewrite plus_lid.
        exact ltq.
Qed.
Theorem lt_plus_0_a_b_ba : ∀ a b, 0 < a ↔ b < b + a.
Proof.
    intros a b.
    split; intros ltq.
    -   apply lt_lplus with b in ltq.
        rewrite plus_rid in ltq.
        exact ltq.
    -   apply lt_plus_lcancel with b.
        rewrite plus_rid.
        exact ltq.
Qed.

Theorem lt_plus_0_nab_a_b : ∀ a b, 0 < -a + b ↔ a < b.
Proof.
    intros a b.
    rewrite <- lt_plus_llmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem lt_plus_anb_0_a_b : ∀ a b, a - b < 0 ↔ a < b.
Proof.
    intros a b.
    rewrite <- lt_plus_rrmove.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem lt_plus_nab_0_b_a : ∀ a b, -a + b < 0 ↔ b < a.
Proof.
    intros a b.
    rewrite <- lt_plus_rlmove.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem lt_plus_0_anb_b_a : ∀ a b, 0 < a - b ↔ b < a.
Proof.
    intros a b.
    rewrite <- lt_plus_lrmove.
    rewrite plus_lid.
    reflexivity.
Qed.

Theorem neg_pos : ∀ a, a ≤ 0 ↔ 0 ≤ -a.
Proof.
    intros a.
    rewrite <- le_plus_ab_0_a_nb.
    rewrite plus_lid.
    reflexivity.
Qed.
Theorem neg_pos2 : ∀ a, a < 0 ↔ 0 < -a.
Proof.
    intros a.
    rewrite <- lt_plus_ab_0_a_nb.
    rewrite plus_lid.
    reflexivity.
Qed.

Theorem pos_neg : ∀ a, 0 ≤ a ↔ -a ≤ 0.
Proof.
    intros a.
    rewrite <- le_plus_0_ab_na_b.
    rewrite plus_rid.
    reflexivity.
Qed.
Theorem pos_neg2 : ∀ a, 0 < a ↔ -a < 0.
Proof.
    intros a.
    rewrite <- lt_plus_0_ab_na_b.
    rewrite plus_rid.
    reflexivity.
Qed.

Theorem le_neg : ∀ a b, a ≤ b ↔ -b ≤ -a.
Proof.
    intros a b.
    rewrite <- le_plus_0_anb_b_a.
    rewrite le_plus_0_ab_na_b.
    reflexivity.
Qed.
Theorem lt_neg : ∀ a b, a < b ↔ -b < -a.
Proof.
    intros a b.
    rewrite <- lt_plus_0_anb_b_a.
    rewrite lt_plus_0_ab_na_b.
    reflexivity.
Qed.

Theorem le_half_rneg : ∀ a b, a ≤ -b ↔ b ≤ -a.
Proof.
    intros a b.
    rewrite le_neg.
    rewrite neg_neg.
    reflexivity.
Qed.
Theorem lt_half_rneg : ∀ a b, a < -b ↔ b < -a.
Proof.
    intros a b.
    rewrite lt_neg.
    rewrite neg_neg.
    reflexivity.
Qed.
Theorem le_half_lneg : ∀ a b, -a ≤ b ↔ -b ≤ a.
Proof.
    intros a b.
    rewrite le_neg.
    rewrite neg_neg.
    reflexivity.
Qed.
Theorem lt_half_lneg : ∀ a b, -a < b ↔ -b < a.
Proof.
    intros a b.
    rewrite lt_neg.
    rewrite neg_neg.
    reflexivity.
Qed.

Theorem le_pos_plus : ∀ {a b}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b.
Proof.
    intros a b a_pos b_pos.
    rewrite <- (plus_rid 0).
    apply le_lrplus; assumption.
Qed.
Theorem lt_pos_plus : ∀ {a b}, 0 < a → 0 < b → 0 < a + b.
Proof.
    intros a b a_pos b_pos.
    rewrite <- (plus_rid 0).
    apply lt_lrplus; assumption.
Qed.
Theorem le_lt_pos_plus : ∀ {a b}, 0 ≤ a → 0 < b → 0 < a + b.
Proof.
    intros a b a_pos b_pos.
    rewrite <- (plus_rid 0).
    apply le_lt_lrplus; assumption.
Qed.
Theorem lt_le_pos_plus : ∀ {a b}, 0 < a → 0 ≤ b → 0 < a + b.
Proof.
    intros a b a_pos b_pos.
    rewrite <- (plus_rid 0).
    apply lt_le_lrplus; assumption.
Qed.

Theorem le_neg_plus : ∀ {a b}, a ≤ 0 → b ≤ 0 → a + b ≤ 0.
Proof.
    intros a b a_neg b_neg.
    rewrite <- (plus_rid 0).
    apply le_lrplus; assumption.
Qed.
Theorem lt_neg_plus : ∀ {a b}, a < 0 → b < 0 → a + b < 0.
Proof.
    intros a b a_neg b_neg.
    rewrite <- (plus_rid 0).
    apply lt_lrplus; assumption.
Qed.
Theorem le_lt_neg_plus : ∀ {a b}, a ≤ 0 → b < 0 → a + b < 0.
Proof.
    intros a b a_neg b_neg.
    rewrite <- (plus_rid 0).
    apply le_lt_lrplus; assumption.
Qed.
Theorem lt_le_neg_plus : ∀ {a b}, a < 0 → b ≤ 0 → a + b < 0.
Proof.
    intros a b a_neg b_neg.
    rewrite <- (plus_rid 0).
    apply lt_le_lrplus; assumption.
Qed.
(* begin hide *)
End OrderPlus.
(* end hide *)
